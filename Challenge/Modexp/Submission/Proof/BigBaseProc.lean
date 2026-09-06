import Challenge.Modexp.Submission.Proof.BigLoadProc
import Challenge.Modexp.Submission.Proof.AddModProcProof
import Mathlib.Tactic

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# The MODEXP big path: base reduction and accumulator init (procedure basis)

`secBigPath`'s base-reduction section, on the procedure-based `programAsm`:
from the nonzero-modulus dispatch (`BigLoad.big_scan_nonzero` hands a `BMScan`
state at `bigMid ++ …`) through

* `store ONE 1` — the ONE region becomes the `n`-limb encoding of `1`;
* the `lbBase` byte loop (one round per base byte `i < BS`): `Wcell := byte i`
  of the base at `BO = 96`, `Jcell := 8`, then the `lbBaseBits` bit loop —
  `Jcell--`, `callAddMod BASE BASE lamCallBase1` (double), and, when bit
  `Jcell` of `Wcell` is set, `callAddMod BASE ONE lamCallBase2` (conditional
  add of one);
* the `lbBaseDone` `callAddMod ACC ONE lamCallAccInit` — the accumulator init
  `ACC := 1 % m`.

The arithmetic is done by the `addMod` *procedure* (`lamEntry`…`lamDone`,
ending `.dynJump`), entered through the call sites; this file applies
`AddModProcProof.addModCall_correct` at each of the three sites (the seven
internal label resolutions are shared, discharged once by `decide`; the two
call-site-dependent facts are `lret ∈ labelDefs` and the return-label
resolution).  The value-level Horner invariants are exactly those of the
inline-fragment basis: per bit `j` of byte `w` (prefix `P`), BASE holds
`(P · 2 ^ (8 - j) + w / 2 ^ j) % m`; one double-plus-conditional-add round
moves it to `j - 1`; eight rounds move it to `(P · 256 + w) % m`.

Entry contract (from `BMScan yst cd (nlimbs cd)` plus `modVal cd ≠ 0`): the
MOD region represents the modulus `m`, every byte from the end of the MOD
region up to `BS` is zero (so BASE/ACC/ONE/SUBC/… all start zero), the scalar
cells `MS/BS/ES/BO/EO/Ncell` hold the parsed sizes, `activeWords = 250`.

Exit contract (`BBExit`): `BASE` represents `b % m` with
`b = bytesToNatPadded cd 96 (baseSize cd)`, `ACC` represents `1 % m` (the
`m = 1` case gives `0`), the ONE region still represents `1`, MOD still
represents `m`, the exponent phase's cells (`ES`, `EO`) are untouched, and
`activeWords` is still `250`.  The machine lands at `bbExpRest` — the
exponent-scan continuation — so the big-path composer can chain
header → load → base (this file) → exponent → serialize.
-/

namespace Challenge.Modexp.Submission.Proof.BigBaseProc

open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState wordFrom byteFrom byteAt loadWord storeWord
  readBytes activeWordsAfter touchMemory b2w)
open Challenge.Modexp.Submission (Expr store storeAt jumpIfNz jumpIfZ
  jumpUnlessLt cdbCell bitTest compileExpr loadAt evalExpr exprOK callAddMod
  callMulMod
  BS ES MS BO EO MO Ncell Icell I2 Jcell Wcell T0 T1 T2 RET TOP ONE ACC BASE MOD OUT
  SUBC C1 C2 AOFF AX AY AS AZ ADST ASRC
  programAsm localModel)
open Challenge.Modexp.Submission.Proof.Header
open Challenge.Modexp.Submission.Proof.YulMem
open Challenge.Modexp.Submission.Proof.YulLimbs
open Challenge.Modexp.Submission.Proofs.Limbs (radix limbCount limbDigits
  length_limbDigits limbDigits_lt value_limbDigits radix_gt_one radix_pos
  pow_radix limbCount_le_32 limbCount_pos)
open Challenge.Modexp.Submission.Proof.BigLoad
open Challenge.Modexp.Submission.Proof.AddModProcProof
open Challenge.Modexp (baseSize exponentSize modulusSize spec ValidInput)
open EvmSemantics.EVM.Precompile (bytesToNatPadded)
open Challenge.EvmProof.Bytes (bytesToNatPadded_succ bytesToNatPadded_lt_pow)

/-- Shorthand for the 256-bit word carrying the natural `n`. -/
local notation:max "W " n:max => BitVec.ofNat 256 n

/-! ## Values and modular arithmetic -/

/-- The modulus value held by the MOD region (BigLoad's `partVal` at full
width). -/
def modVal (cd : ByteArray) : Nat := partVal cd (modulusSize cd)

/-- … which is the padded big-endian read at the modulus offset. -/
theorem modVal_eq (cd : ByteArray) :
    modVal cd = bytesToNatPadded cd (modOff cd) (modulusSize cd) := by
  simp only [modVal, partVal, Nat.sub_self, pow_zero, Nat.mul_one]
  exact (bytesToNatPadded_wordVal cd (modOff cd) (modulusSize cd)).symm

/-- Base byte `i` (0-indexed from the base operand's calldata offset 96). -/
def bByte (cd : ByteArray) (i : Nat) : Nat := (byteFrom cd.toList (96 + i)).toNat
theorem bByte_lt (cd : ByteArray) (i : Nat) : bByte cd i < 256 :=
  (byteFrom cd.toList (96 + i)).toNat_lt

/-- The big-endian prefix value of the first `i` base bytes. -/
def bPre (cd : ByteArray) (i : Nat) : Nat := bytesToNatPadded cd 96 i

theorem bPre_succ (cd : ByteArray) (i : Nat) :
    bPre cd (i + 1) = bPre cd i * 256 + bByte cd i :=
  bytesToNatPadded_succ cd 96 i

/-- The bit-level Horner step inside one byte: doubling plus the conditional
add moves the `2 ^ j`-scaled window down one bit. -/
theorem bb_bit_step (P w n : Nat) (hn : 0 < n) (hn8 : n ≤ 8) :
    2 * (P * 2 ^ (8 - n) + w / 2 ^ n) + w / 2 ^ (n - 1) % 2 =
      P * 2 ^ (8 - (n - 1)) + w / 2 ^ (n - 1) := by
  have hpow : 2 ^ (8 - (n - 1)) = 2 ^ (8 - n) * 2 := by
    rw [show 8 - (n - 1) = 8 - n + 1 from by omega, Nat.pow_succ]
  have hd : w / 2 ^ (n - 1) = 2 * (w / 2 ^ n) + w / 2 ^ (n - 1) % 2 := by
    have h2 : (2 : Nat) ^ n = 2 ^ (n - 1) * 2 := by
      conv_lhs => rw [show n = n - 1 + 1 from by omega]
      exact Nat.pow_succ 2 (n - 1)
    have hdiv : w / 2 ^ (n - 1) / 2 = w / 2 ^ n := by
      rw [Nat.div_div_eq_div_mul, h2]
    omega
  rw [hpow, show P * (2 ^ (8 - n) * 2) = 2 * (P * 2 ^ (8 - n)) from by ring]
  omega

/-- Doubling at the mod level. -/
theorem dbl_mod (m V r : Nat) (hr : r = V % m) : (r + r) % m = (2 * V) % m := by
  rw [hr, ← Nat.add_mod, show 2 * V = V + V from by omega]

/-- Adding one at the mod level. -/
theorem add1_mod (m V r : Nat) (hr : r = (2 * V) % m) :
    (r + 1) % m = (2 * V + 1) % m := by
  rw [hr, Nat.mod_add_mod]

/-- The word-level bitwise-and with one. -/
theorem W_and_one {v : Nat} (hv : v < 2 ^ 256) : (W v) &&& W 1 = W (v % 2) := by
  have h2 : v % 2 < 2 ^ 256 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt (by norm_num : (1 : Nat) < 2 ^ 256), toNat_W hv]
  simp

/-! ## The addMod procedure's label bundle -/

/-- The procedure's eight labels as `programAsm` allocates them (the fields
of `ProgLabels`; `AddModProcProof`'s fragments are spelled over this
bundle). -/
def amLabels : AddModProcLabels :=
  ⟨programLabels.lamEntry, programLabels.lamAdd, programLabels.lamSubStart,
    programLabels.amSub, programLabels.lamSel, programLabels.lamDoCopy,
    programLabels.lamCopy, programLabels.lamDone⟩

/-! ## The base section as nested fragments -/

/-- The fixed continuation after `bigMid`: serializer, halt stubs, and the two
procedure bodies. -/
def bbK : List Asm := secTailSer programLabels ++ progTail

/-- `bigMid` from the ACC-init call on: the exponent scan and loops (opaque
here — the exponent phase's proof owns it). -/
def bbExpRest (l : ProgLabels) : List Asm :=
  store Icell (.imm 0) ++
  [.label l.lbEScan] ++
  jumpUnlessLt (.load Icell) (.load ES) l.lbSer ++
  store Wcell (cdbCell EO) ++
  jumpIfNz (.load Wcell) l.lbInit ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lbEScan] ++
  [.label l.lbInit] ++
  store Jcell (.imm 7) ++
  [.label l.lbTop] ++
  jumpIfNz bitTest l.lbInitAcc ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  [.jump l.lbTop] ++
  [.label l.lbInitAcc] ++
  store I2 (.imm 0) ++
  [.label l.lbAccInit] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lbAccInitDone ++
  storeAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm BASE) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lbAccInit] ++
  [.label l.lbAccInitDone] ++
  [.label l.lbTopBits] ++
  jumpIfZ (.load Jcell) l.lbRest ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  callMulMod ACC l.lsqRet1 l.lmmEntry ++
  jumpIfZ bitTest l.lbTopBitsSkip ++
  callMulMod BASE l.lmulRet1 l.lmmEntry ++
  [.label l.lbTopBitsSkip] ++
  [.jump l.lbTopBits] ++
  [.label l.lbRest] ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.label l.lbBytes] ++
  jumpUnlessLt (.load Icell) (.load ES) l.lbSer ++
  store Wcell (cdbCell EO) ++
  store Jcell (.imm 8) ++
  [.label l.lbByteBits] ++
  jumpIfZ (.load Jcell) l.lbNextByte ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  callMulMod ACC l.lsqRet2 l.lmmEntry ++
  jumpIfZ bitTest l.lbByteBitsSkip ++
  callMulMod BASE l.lmulRet2 l.lmmEntry ++
  [.label l.lbByteBitsSkip] ++
  [.jump l.lbByteBits] ++
  [.label l.lbNextByte] ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lbBytes]

/-- From just after `.label lbBaseDone`: the ACC-init call, then the
exponent rest. -/
def bbDoneK (l : ProgLabels) : List Asm :=
  callAddMod ACC ONE l.lamCallAccInit l.lamEntry ++ bbExpRest l

/-- From just after `.label lbBaseNext`: the byte counter bump and back-jump,
then the exit. -/
def bbNextK (l : ProgLabels) : List Asm :=
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lbBase] ++ ([.label l.lbBaseDone] ++ bbDoneK l))

/-- From just after `.label lbBaseBitsSkip`: the back-jump, the byte exit,
and on. -/
def bbSkipK (l : ProgLabels) : List Asm :=
  [.jump l.lbBaseBits] ++ ([.label l.lbBaseNext] ++ bbNextK l)

/-- The conditional-add call and onward (continuation of the doubled
call). -/
def bbOneK (l : ProgLabels) : List Asm :=
  callAddMod BASE ONE l.lamCallBase2 l.lamEntry ++
  ([.label l.lbBaseBitsSkip] ++ bbSkipK l)

/-- The bit test and onward. -/
def bbCondK (l : ProgLabels) : List Asm :=
  jumpIfZ bitTest l.lbBaseBitsSkip ++ bbOneK l

/-- The doubling call and onward. -/
def bbDblK (l : ProgLabels) : List Asm :=
  callAddMod BASE BASE l.lamCallBase1 l.lamEntry ++ bbCondK l

/-- From just after `.label lbBaseBits`: one bit round. -/
def bbBitsK (l : ProgLabels) : List Asm :=
  jumpIfZ (.load Jcell) l.lbBaseNext ++
  (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ bbDblK l)

/-- From just after `.label lbBase`: the byte-round guard. -/
def bbOuterK (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load BS) l.lbBaseDone ++
  (store Wcell (cdbCell BO) ++ (store Jcell (.imm 8) ++
    ([.label l.lbBaseBits] ++ bbBitsK l)))

/-- `bigMid` entire: the ONE store, the byte counter reset, and the loops. -/
def bbEntryK (l : ProgLabels) : List Asm :=
  store ONE (.imm 1) ++
  (store Icell (.imm 0) ++ ([.label l.lbBase] ++ bbOuterK l))

/-- The fragments reassemble `bigMid`. -/
theorem bigMid_eq : bigMid programLabels = bbEntryK programLabels := by rfl

/-! ## Label resolutions -/

/-! ### The addMod procedure's internal labels (shared by every call site) -/

/-- The procedure entry: the body, the return jump, and the mulMod procedure
trailing it in `programAsm`. -/
theorem findAmEntry : findLabel amLabels.lEntry programAsm =
    some (amProcFrag amLabels ++ [.dynJump] ++ secMulModProc programLabels) := by
  decide

/-- The procedure's addition loop. -/
theorem findAmAdd : findLabel amLabels.lAdd programAsm =
    some (amAddBody amLabels ++ amFromSubStart amLabels ++ [.dynJump] ++
      secMulModProc programLabels) := by
  decide

/-- The procedure's subtraction-pass entry. -/
theorem findAmSubStart : findLabel amLabels.lSubStart programAsm =
    some (store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub amLabels ++
      [.dynJump] ++ secMulModProc programLabels) := by
  decide

/-- The procedure's subtraction loop. -/
theorem findAmSub : findLabel amLabels.lSub programAsm =
    some (amSubBody amLabels ++ amFromSel amLabels ++ [.dynJump] ++
      secMulModProc programLabels) := by
  decide

/-- The procedure's selection. -/
theorem findAmSel : findLabel amLabels.lSel programAsm =
    some (amSelBody amLabels ++ amFromDoCopy amLabels ++ [.dynJump] ++
      secMulModProc programLabels) := by
  decide

/-- The procedure's copy-loop entry. -/
theorem findAmDoCopy : findLabel amLabels.lDoCopy programAsm =
    some (store I2 (.imm 0) ++ amFromCopy amLabels ++ [.dynJump] ++
      secMulModProc programLabels) := by
  decide

/-- The procedure's copy loop. -/
theorem findAmCopy : findLabel amLabels.lCopy programAsm =
    some (amCopyBody amLabels ++ amFromDone amLabels ++ [.dynJump] ++
      secMulModProc programLabels) := by
  decide

/-- The procedure's exit: the return jump into the mulMod procedure. -/
theorem findAmDone : findLabel amLabels.lDone programAsm =
    some ([.dynJump] ++ secMulModProc programLabels) := by
  decide

/-! ### The three call sites' return labels -/

/-- The doubling call's return label is defined (its `pushLabel` needs it). -/
theorem memLamCallBase1 : programLabels.lamCallBase1 ∈ labelDefs programAsm := by
  decide

/-- The doubling call returns to the bit test. -/
theorem findLamCallBase1 : findLabel programLabels.lamCallBase1 programAsm =
    some (bbCondK programLabels ++ bbK) := by
  decide

/-- The conditional-add call's return label is defined. -/
theorem memLamCallBase2 : programLabels.lamCallBase2 ∈ labelDefs programAsm := by
  decide

/-- The conditional-add call returns to the skip label. -/
theorem findLamCallBase2 : findLabel programLabels.lamCallBase2 programAsm =
    some (([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++
      bbK) := by
  decide

/-- The ACC-init call's return label is defined. -/
theorem memLamCallAccInit : programLabels.lamCallAccInit ∈ labelDefs programAsm := by
  decide

/-- The ACC-init call returns to the exponent scan. -/
theorem findLamCallAccInit : findLabel programLabels.lamCallAccInit programAsm =
    some (bbExpRest programLabels ++ bbK) := by
  decide

/-! ### The base section's loop labels -/

/-- The outer byte loop top. -/
theorem findLbBase :
    findLabel programLabels.lbBase programAsm =
      some (bbOuterK programLabels ++ bbK) := by
  decide

/-- The inner bit loop top. -/
theorem findLbBaseBits :
    findLabel programLabels.lbBaseBits programAsm =
      some (bbBitsK programLabels ++ bbK) := by
  decide

/-- The byte-round exit. -/
theorem findLbBaseNext :
    findLabel programLabels.lbBaseNext programAsm =
      some (bbNextK programLabels ++ bbK) := by
  decide

/-- The bit-skip landing. -/
theorem findLbBaseBitsSkip :
    findLabel programLabels.lbBaseBitsSkip programAsm =
      some (bbSkipK programLabels ++ bbK) := by
  decide

/-- The base loop exit: the ACC-init call and onward. -/
theorem findLbBaseDone :
    findLabel programLabels.lbBaseDone programAsm =
      some (bbDoneK programLabels ++ bbK) := by
  decide

/-! ## The frame, invariants, and memory transfers -/

/-- `ofDigits` of an all-zero replicate is zero. -/
theorem ofDigits_replicate_zero : ∀ (k : Nat),
    Nat.ofDigits radix (List.replicate k 0) = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, ih]
      simp

/-- A zero limb region represents zero. -/
theorem rep_zero_of_zero {M : Nat → UInt8} {R n : Nat} (hn0 : 0 < n)
    (hzero : ∀ a, R ≤ a → a < R + 32 * n → M a = 0) :
    RepresentsY M R n 0 := by
  have hval : (0 : Nat) < radix ^ n :=
    Nat.pow_pos (by have := radix_gt_one; omega)
  refine (RepresentsY_iff_value hval).mpr ?_
  rw [yLimbs_congr (mem := M) (mem' := fun _ => 0)
    (fun a ha1 ha2 => hzero a ha1 ha2), yLimbs_zero_value]

/-- The `n`-limb one over an otherwise-zero region. -/
theorem rep_one_of_zero {M : Nat → UInt8} {R n : Nat} (hn0 : 0 < n)
    (hzero : ∀ a, R ≤ a → a < R + 32 * n → M a = 0) :
    RepresentsY (storeWord M R (W 1)) R n 1 := by
  have hval : (1 : Nat) < radix ^ n := by
    calc (1 : Nat) < radix := radix_gt_one
      _ = radix ^ 1 := (Nat.pow_one radix).symm
      _ ≤ radix ^ n := Nat.pow_le_pow_right (by have := radix_gt_one; omega)
        (by omega)
  refine (RepresentsY_iff_value hval).mpr ?_
  have hy : yLimbs M R n = List.replicate n 0 := by
    rw [yLimbs_congr (mem := M) (mem' := fun _ => 0)
      (fun a ha1 ha2 => hzero a ha1 ha2), yLimbs_zero]
  have hw : yLimbs (storeWord M R (W 1)) R n = (yLimbs M R n).set 0 1 := by
    have h := yLimbs_storeWord M R n 0 hn0 (W 1)
    rw [show R + 32 * 0 = R from by omega,
      toNat_W (by norm_num : (1 : Nat) < 2 ^ 256)] at h
    exact h
  rw [hw, hy]
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨k, rfl⟩
  rw [List.replicate_succ]
  show Nat.ofDigits radix (1 :: List.replicate k 0) = 1
  rw [Nat.ofDigits_cons, ofDigits_replicate_zero]
  simp

/-- The cells and regions preserved through the base section (the frame the
call applications keep): the size/offset cells, the ONE region, the MOD
region, and the still-zero ACC region. -/
structure BBFrame (yst : EvmState) (cd : ByteArray) : Prop where
  aw : yst.activeWords.toNat = 250
  env : yst.env.calldata = cd.toList
  hn0 : 0 < nlimbs cd
  hn32 : nlimbs cd ≤ 32
  ncell : loadWord yst.memory Ncell = W (nlimbs cd)
  mscell : loadWord yst.memory MS = W (modulusSize cd)
  bscell : loadWord yst.memory BS = W (baseSize cd)
  escell : loadWord yst.memory ES = W (exponentSize cd)
  bocell : loadWord yst.memory BO = W 96
  eocell : loadWord yst.memory EO = W (96 + baseSize cd)
  modrep : RepresentsY yst.memory MOD (nlimbs cd) (modVal cd)
  onerep : RepresentsY yst.memory ONE (nlimbs cd) 1
  accrep : RepresentsY yst.memory ACC (nlimbs cd) 0

/-- Outer-loop invariant: at `.label lbBase` after consuming `i` base bytes —
BASE holds the reduced prefix value. -/
structure BBase (yst : EvmState) (cd : ByteArray) (i : Nat) : Prop where
  fr : BBFrame yst cd
  icell : loadWord yst.memory Icell = W i
  baserep : RepresentsY yst.memory BASE (nlimbs cd) (bPre cd i % modVal cd)

/-- Inner-loop invariant: at `.label lbBaseBits` with `j` bits left of byte
`w` — BASE holds the doubled prefix plus the processed top bits of `w`. -/
structure BBits (yst : EvmState) (cd : ByteArray) (i w j : Nat) : Prop where
  fr : BBFrame yst cd
  icell : loadWord yst.memory Icell = W i
  wcell : loadWord yst.memory Wcell = W w
  jcell : loadWord yst.memory Jcell = W j
  baserep : RepresentsY yst.memory BASE (nlimbs cd)
    ((bPre cd i * 2 ^ (8 - j) + w / 2 ^ j) % modVal cd)

/-- The exit contract: BASE holds `b % m`, ACC holds `1 % m`. -/
structure BBExit (yst : EvmState) (cd : ByteArray) : Prop where
  aw : yst.activeWords.toNat = 250
  env : yst.env.calldata = cd.toList
  hn0 : 0 < nlimbs cd
  hn32 : nlimbs cd ≤ 32
  icell : loadWord yst.memory Icell = W (baseSize cd)
  ncell : loadWord yst.memory Ncell = W (nlimbs cd)
  mscell : loadWord yst.memory MS = W (modulusSize cd)
  bscell : loadWord yst.memory BS = W (baseSize cd)
  escell : loadWord yst.memory ES = W (exponentSize cd)
  bocell : loadWord yst.memory BO = W 96
  eocell : loadWord yst.memory EO = W (96 + baseSize cd)
  modrep : RepresentsY yst.memory MOD (nlimbs cd) (modVal cd)
  onerep : RepresentsY yst.memory ONE (nlimbs cd) 1
  baserep : RepresentsY yst.memory BASE (nlimbs cd)
    (bPre cd (baseSize cd) % modVal cd)
  accrep : RepresentsY yst.memory ACC (nlimbs cd) (1 % modVal cd)

/-- A scalar cell load survives an `addMod` call application (the keeps side
condition, lifted to words; the scratch set is the call-scratch list — the
address registers included). -/
theorem keeps_loadCell {M M' : Nat → UInt8} {c dst n : Nat}
    (hk : ∀ a, (a < dst ∨ dst + 32 * n ≤ a) → (a < SUBC ∨ SUBC + 32 * n ≤ a) →
      (∀ cc ∈ addModCallScratch, a < cc ∨ cc + 32 ≤ a) → M' a = M a)
    (h1 : c + 32 ≤ dst ∨ dst + 32 * n ≤ c)
    (h2 : c + 32 ≤ SUBC ∨ SUBC + 32 * n ≤ c)
    (h3 : ∀ cc ∈ addModCallScratch, c + 32 ≤ cc ∨ cc + 32 ≤ c) :
    loadWord M' c = loadWord M c := by
  apply loadWord_congr
  intro a ha1 ha2
  rw [hk a ?_ ?_ ?_]
  · rcases h1 with h | h <;> omega
  · rcases h2 with h | h <;> omega
  · intro cc hcc
    rcases h3 cc hcc with h | h <;> omega

/-- A limb region survives an `addMod` call application (when disjoint from
`dst`, `SUBC`, and the call-scratch cells). -/
theorem keeps_rep {M M' : Nat → UInt8} {R dst n v : Nat}
    (hk : ∀ a, (a < dst ∨ dst + 32 * n ≤ a) → (a < SUBC ∨ SUBC + 32 * n ≤ a) →
      (∀ cc ∈ addModCallScratch, a < cc ∨ cc + 32 ≤ a) → M' a = M a)
    (hR : RepresentsY M R n v)
    (h1 : R + 32 * n ≤ dst ∨ dst + 32 * n ≤ R)
    (h2 : R + 32 * n ≤ SUBC)
    (h3 : ∀ cc ∈ addModCallScratch, R + 32 * n ≤ cc) :
    RepresentsY M' R n v := by
  refine ⟨hR.1, ?_⟩
  rw [yLimbs_congr (mem := M') (mem' := M) (base := R) (n := n) ?_, hR.2]
  intro a ha1 ha2
  exact hk a (by rcases h1 with h | h <;> omega) (by omega)
    (by intro cc hcc; have hcc' := h3 cc hcc; omega)

/-- The frame survives an `addMod` call application at `dst = BASE`: every
framed cell and region is disjoint from the write set. -/
theorem keeps_frame {yst yst' : EvmState} {cd : ByteArray}
    (hk : ∀ a, (a < BASE ∨ BASE + 32 * nlimbs cd ≤ a) →
      (a < SUBC ∨ SUBC + 32 * nlimbs cd ≤ a) →
      (∀ cc ∈ addModCallScratch, a < cc ∨ cc + 32 ≤ a) → yst'.memory a = yst.memory a)
    (hawEq : yst'.activeWords = yst.activeWords)
    (henv : yst'.env = yst.env)
    (hf : BBFrame yst cd) :
    BBFrame yst' cd := by
  have hMODv : MOD = (0 : Nat) := rfl
  have hBASEv : BASE = 1024 := by decide
  have hACCv : ACC = 2048 := by decide
  have hONEv : ONE = 4096 := by decide
  have hSUBCv : SUBC = 5120 := by decide
  have hNcv : Ncell = 7360 := by decide
  have hBSv : BS = 7168 := by decide
  have hESv : ES = 7200 := by decide
  have hMSv : MS = 7232 := by decide
  have hBOv : BO = 7264 := by decide
  have hEOv : EO = 7296 := by decide
  have hC1v : C1 = 7488 := by decide
  have hC2v : C2 = 7520 := by decide
  have hI2v : I2 = 7776 := by decide
  have hAOFFv : AOFF = 7808 := by decide
  have hAXv : AX = 7840 := by decide
  have hAYv : AY = 7872 := by decide
  have hASv : AS = 7904 := by decide
  have hAZv : AZ = 7936 := by decide
  have hn32f := hf.hn32
  refine ⟨by rw [hawEq]; exact hf.aw, by rw [henv]; exact hf.env, hf.hn0, hf.hn32,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact keeps_loadCell (c := Ncell) hk (by omega) (by omega) (by decide) |>.trans hf.ncell
  · exact keeps_loadCell (c := MS) hk (by omega) (by omega) (by decide) |>.trans hf.mscell
  · exact keeps_loadCell (c := BS) hk (by omega) (by omega) (by decide) |>.trans hf.bscell
  · exact keeps_loadCell (c := ES) hk (by omega) (by omega) (by decide) |>.trans hf.escell
  · exact keeps_loadCell (c := BO) hk (by omega) (by omega) (by decide) |>.trans hf.bocell
  · exact keeps_loadCell (c := EO) hk (by omega) (by omega) (by decide) |>.trans hf.eocell
  · exact keeps_rep (R := MOD) (dst := BASE) (n := nlimbs cd) hk hf.modrep (by omega) (by omega)
      (by intro cc hcc
          have hmem : ∀ cc ∈ addModCallScratch, C1 ≤ cc := by decide
          have hcc' := hmem cc hcc
          omega)
  · exact keeps_rep (R := ONE) (dst := BASE) (n := nlimbs cd) hk hf.onerep (by omega) (by omega)
      (by intro cc hcc
          have hmem : ∀ cc ∈ addModCallScratch, C1 ≤ cc := by decide
          have hcc' := hmem cc hcc
          omega)
  · exact keeps_rep (R := ACC) (dst := BASE) (n := nlimbs cd) hk hf.accrep (by omega) (by omega)
      (by intro cc hcc
          have hmem : ∀ cc ∈ addModCallScratch, C1 ≤ cc := by decide
          have hcc' := hmem cc hcc
          omega)

/-- The frame survives a store to one of the counter/scratch scalar cells
(`Icell..Wcell`). -/
theorem frame_store {yst : EvmState} {cd : ByteArray} {c : Nat} {v : U256}
    (hc : Icell ≤ c ∧ c ≤ Wcell) (hf : BBFrame yst cd) :
    BBFrame { yst with memory := storeWord yst.memory c v } cd := by
  obtain ⟨hc1, hc2⟩ := hc
  have hMODv : MOD = (0 : Nat) := rfl
  have hONEv : ONE = 4096 := by decide
  have hBASEv : BASE = 1024 := by decide
  have hACCv : ACC = 2048 := by decide
  have hNcv : Ncell = 7360 := by decide
  have hBSv : BS = 7168 := by decide
  have hESv : ES = 7200 := by decide
  have hMSv : MS = 7232 := by decide
  have hBOv : BO = 7264 := by decide
  have hEOv : EO = 7296 := by decide
  have hIcv : Icell = 7392 := by decide
  have hWcv : Wcell = 7456 := by decide
  have hn32f := hf.hn32
  refine ⟨by exact hf.aw, by exact hf.env, hf.hn0, hf.hn32, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · show loadWord (storeWord yst.memory c v) Ncell = _
    rw [load_disj' _ _ _ _ (by omega)]; exact hf.ncell
  · show loadWord (storeWord yst.memory c v) MS = _
    rw [load_disj' _ _ _ _ (by omega)]; exact hf.mscell
  · show loadWord (storeWord yst.memory c v) BS = _
    rw [load_disj' _ _ _ _ (by omega)]; exact hf.bscell
  · show loadWord (storeWord yst.memory c v) ES = _
    rw [load_disj' _ _ _ _ (by omega)]; exact hf.escell
  · show loadWord (storeWord yst.memory c v) BO = _
    rw [load_disj' _ _ _ _ (by omega)]; exact hf.bocell
  · show loadWord (storeWord yst.memory c v) EO = _
    rw [load_disj' _ _ _ _ (by omega)]; exact hf.eocell
  · exact RepresentsY_storeWord_disjoint hf.modrep (by omega)
  · exact RepresentsY_storeWord_disjoint hf.onerep (by omega)
  · exact RepresentsY_storeWord_disjoint hf.accrep (by omega)

/-- The `store ONE 1`, `store Icell 0` preamble: from the scan-exit state to
the outer loop top with the invariant at `i = 0`. -/
theorem bb_entry {cd : ByteArray} (hv : ValidInput cd) {yst : EvmState}
    (hgt : 32 < modulusSize cd) (hinv : BMScan yst cd (nlimbs cd)) :
    ∃ yst', BBase yst' cd 0 ∧
      ASteps programAsm ⟨bbEntryK programLabels ++ bbK, [], yst⟩
        ⟨bbOuterK programLabels ++ bbK, [], yst'⟩ := by
  have haw : yst.activeWords.toNat = 250 := hinv.aw
  have hn0 : 0 < nlimbs cd := limbCount_pos (by omega)
  have hn32 : nlimbs cd ≤ 32 :=
    limbCount_le_32 _ (by obtain ⟨-, -, hm⟩ := hv; omega)
  have hs1 := store_pin (c := ONE) (e := .imm 1) (v := W 1)
    (k := store Icell (.imm 0) ++ ([.label programLabels.lbBase] ++
      (bbOuterK programLabels ++ bbK)))
    (yst := yst) (by trivial) (by decide)
    (by rw [haw]; show ONE + 32 ≤ 8000; decide) rfl
  have hs2 := store_pin (c := Icell) (e := .imm 0) (v := W 0)
    (k := [.label programLabels.lbBase] ++ (bbOuterK programLabels ++ bbK))
    (yst := { yst with memory := storeWord yst.memory ONE (W 1) })
    (by trivial) (by decide) (by rw [haw]; show Icell + 32 ≤ 8000; decide) rfl
  set yst2 : EvmState :=
    { yst with memory := storeWord (storeWord yst.memory ONE (W 1)) Icell (W 0) }
    with hyst2
  have hlabel := label_steps (model := localModel) (prog := programAsm) (l := programLabels.lbBase)
    (k := bbOuterK programLabels ++ bbK) (σ := ([] : List AVal)) (yst := yst2)
  refine ⟨yst2, ?_, ?_⟩
  swap
  · rw [show bbEntryK programLabels ++ bbK =
        store ONE (.imm 1) ++ (store Icell (.imm 0) ++
          ([.label programLabels.lbBase] ++ (bbOuterK programLabels ++ bbK)))
      from by simp only [bbEntryK, List.append_assoc]]
    exact (hs1.trans hs2).trans hlabel
  · -- the invariant
    have hyst2mem : yst2.memory =
        storeWord (storeWord yst.memory ONE (W 1)) Icell (W 0) := rfl
    have hMODv : MOD = (0 : Nat) := rfl
    have hONEv : ONE = 4096 := by decide
    have hBASEv : BASE = 1024 := by decide
    have hACCv : ACC = 2048 := by decide
    have hBSeq : BS = 7168 := by decide
    have hIcv : Icell = 7392 := by decide
    have hzBASE : ∀ a, BASE ≤ a → a < BASE + 32 * nlimbs cd →
        yst.memory a = 0 := by
      intro a ha1 ha2
      exact hinv.midzero a (by omega) (by omega)
    have hzACC : ∀ a, ACC ≤ a → a < ACC + 32 * nlimbs cd →
        yst.memory a = 0 := by
      intro a ha1 ha2
      exact hinv.midzero a (by omega) (by omega)
    have hzONE : ∀ a, ONE ≤ a → a < ONE + 32 * nlimbs cd →
        yst.memory a = 0 := by
      intro a ha1 ha2
      exact hinv.midzero a (by omega) (by omega)
    have hmodrep : RepresentsY yst2.memory MOD (nlimbs cd) (modVal cd) := by
      rw [hyst2mem]
      exact RepresentsY_storeWord_disjoint
        (RepresentsY_storeWord_disjoint hinv.rep (by omega)) (by omega)
    have honerep : RepresentsY yst2.memory ONE (nlimbs cd) 1 := by
      rw [hyst2mem]
      exact RepresentsY_storeWord_disjoint (rep_one_of_zero hn0 hzONE)
        (by omega)
    have haccrep : RepresentsY yst2.memory ACC (nlimbs cd) 0 := by
      rw [hyst2mem]
      exact RepresentsY_storeWord_disjoint
        (RepresentsY_storeWord_disjoint (rep_zero_of_zero hn0 hzACC)
          (by omega)) (by omega)
    have hbaserep : RepresentsY yst2.memory BASE (nlimbs cd)
        (bPre cd 0 % modVal cd) := by
      have h0 : bPre cd 0 % modVal cd = 0 := by simp [bPre]
      rw [h0, hyst2mem]
      exact RepresentsY_storeWord_disjoint
        (RepresentsY_storeWord_disjoint (rep_zero_of_zero hn0 hzBASE)
          (by omega)) (by omega)
    have hcell {c : Nat} (h1 : c + 32 ≤ Icell) (h2 : ONE + 32 ≤ c) {v : U256}
        (hc : loadWord yst.memory c = v) :
        loadWord yst2.memory c = v := by
      rw [hyst2mem, load_disj' _ _ _ _ (Or.inr h1),
        load_disj' _ _ _ _ (Or.inl h2)]
      exact hc
    refine ⟨⟨by rw [hyst2]; exact haw, by rw [hyst2]; exact hinv.env, hn0, hn32,
      hcell (by decide) (by decide) hinv.ncell,
      hcell (by decide) (by decide) hinv.mscell,
      hcell (by decide) (by decide) hinv.bscell,
      hcell (by decide) (by decide) hinv.ecell,
      hcell (by decide) (by decide) hinv.bocell,
      hcell (by decide) (by decide) hinv.eocell,
      hmodrep, honerep, haccrep⟩, ?_, hbaserep⟩
    show loadWord yst2.memory Icell = W 0
    rw [hyst2mem]
    exact loadWord_storeWord_self _ _ _

/-! ## The inner bit loop -/

/-- The bit-test expression's value: bit `j` of `Wcell`. -/
theorem evalExpr_bitTest {yst : EvmState} {w j : Nat}
    (hW : loadWord yst.memory Wcell = W w) (hJ : loadWord yst.memory Jcell = W j)
    (hw : w < 2 ^ 256) (hj : j < 2 ^ 256) :
    evalExpr bitTest yst = W ((w / 2 ^ j) % 2) := by
  show evalBin .and (evalBin .shr (loadWord yst.memory Jcell)
      (loadWord yst.memory Wcell)) (W 1) = _
  show (loadWord yst.memory Wcell >>> (loadWord yst.memory Jcell).toNat) &&& W 1 = _
  rw [hW, hJ, toNat_W hj, W_shr hw j,
    W_and_one (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw)]

/-- One bit round of `lbBaseBits`: fall through the counter test, decrement,
double BASE by the first call, and conditionally add ONE by the second. -/
theorem bb_bit_round {cd : ByteArray} {yst : EvmState} (hm0 : modVal cd ≠ 0)
    {i w j : Nat} (hj : 0 < j) (hj8 : j ≤ 8) (hw : w < 2 ^ 256)
    (hinv : BBits yst cd i w j) :
    ∃ yst', BBits yst' cd i w (j - 1) ∧
      ASteps programAsm ⟨bbBitsK programLabels ++ bbK, [], yst⟩
        ⟨bbBitsK programLabels ++ bbK, [], yst'⟩ := by
  have hn0 := hinv.fr.hn0
  have hn32 := hinv.fr.hn32
  have haw := hinv.fr.aw
  have hm0pos : 0 < modVal cd := Nat.pos_of_ne_zero hm0
  have hnl : nlimbs cd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt hn32 (by norm_num : (32 : Nat) < 2 ^ 256)
  set P := bPre cd i with hPdef
  set V := (P * 2 ^ (8 - j) + w / 2 ^ j) % modVal cd with hVdef
  have hVlt : V < modVal cd := Nat.mod_lt _ hm0pos
  have hlt1 : (V + V) % modVal cd < modVal cd := Nat.mod_lt _ hm0pos
  have hMODv : MOD = (0 : Nat) := rfl
  have hBASEv : BASE = 1024 := by decide
  have hONEv : ONE = 4096 := by decide
  have hSUBCv : SUBC = 5120 := by decide
  have hNcv : Ncell = 7360 := by decide
  have hIcv : Icell = 7392 := by decide
  have hJcv : Jcell = 7424 := by decide
  have hWcv : Wcell = 7456 := by decide
  have hj256 : j < 2 ^ 256 := by omega
  -- step 1: fall through the counter test
  have hfall : ASteps programAsm ⟨bbBitsK programLabels ++ bbK, [], yst⟩
      ⟨store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
          (bbCondK programLabels ++ bbK)), [], yst⟩ := by
    rw [show bbBitsK programLabels ++ bbK =
        jumpIfZ (.load Jcell) programLabels.lbBaseNext ++
          (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
            (callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
              (bbCondK programLabels ++ bbK)))
      from by simp only [bbBitsK, bbDblK, List.append_assoc]]
    exact jumpIfZ_fall (model := localModel) (prog := programAsm)
      (e := .load Jcell) (l := programLabels.lbBaseNext)
      (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
          (bbCondK programLabels ++ bbK)))
      (σ := ([] : List AVal)) (pin250 haw (by decide))
      (by
        show loadWord yst.memory Jcell ≠ 0
        rw [hinv.jcell]
        exact W_ne_zero (by omega) (by omega))
  -- step 2: decrement the bit counter
  have hsJ : ASteps programAsm
      ⟨store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
          (bbCondK programLabels ++ bbK)), [], yst⟩
      ⟨callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
        (bbCondK programLabels ++ bbK), [],
        { yst with memory := storeWord yst.memory Jcell (W (j - 1)) }⟩ :=
    store_pin (c := Jcell) (e := .bin .sub (.load Jcell) (.imm 1))
      (v := W (j - 1))
      (k := callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
        (bbCondK programLabels ++ bbK))
      (by
        show binOK .sub = true ∧ exprOK (Expr.load Jcell) yst ∧
          exprOK (Expr.imm 1) yst
        exact ⟨rfl, pin250 haw (by decide), trivial⟩)
      (by decide) (by rw [haw]; show Jcell + 32 ≤ 8000; decide)
      (by
        show loadWord yst.memory Jcell - W 1 = _
        rw [hinv.jcell]
        exact W_sub (by omega) (by omega))
  set ystJ : EvmState :=
    { yst with memory := storeWord yst.memory Jcell (W (j - 1)) } with hystJ
  have hystJmem : ystJ.memory = storeWord yst.memory Jcell (W (j - 1)) := rfl
  have hawJ : 0x1f40 ≤ 32 * ystJ.activeWords.toNat := by
    rw [hystJ, haw]
  have hframeJ : BBFrame ystJ cd :=
    frame_store (c := Jcell) (hc := ⟨by rw [hIcv, hJcv]; omega,
      by rw [hJcv, hWcv]; omega⟩) hinv.fr
  have hicellJ : loadWord ystJ.memory Icell = W i := by
    rw [hystJmem, load_disj' _ _ _ _ (Or.inr (by omega))]
    exact hinv.icell
  have hwcellJ : loadWord ystJ.memory Wcell = W w := by
    rw [hystJmem, load_disj' _ _ _ _ (Or.inl (by omega))]
    exact hinv.wcell
  have hjcellJ : loadWord ystJ.memory Jcell = W (j - 1) :=
    loadWord_storeWord_self _ _ _
  have hNJ : (loadWord ystJ.memory Ncell).toNat = nlimbs cd := by
    rw [hystJmem, load_disj' _ _ _ _ (Or.inr (by rw [hNcv, hJcv]; omega)),
      hinv.fr.ncell, toNat_W hnl]
  have hxJ : RepresentsY ystJ.memory BASE (nlimbs cd) V := by
    rw [hystJmem]
    exact RepresentsY_storeWord_disjoint hinv.baserep
      (by rw [hBASEv, hJcv]; omega)
  have hmodJ : RepresentsY ystJ.memory MOD (nlimbs cd) (modVal cd) := by
    rw [hystJmem]
    exact RepresentsY_storeWord_disjoint hinv.fr.modrep
      (by rw [hMODv, hJcv]; omega)
  -- step 3: the doubling call
  obtain ⟨S1, hdbl, hrep1, hN1, hkeeps1, haw1, henv1⟩ :=
    addModCall_correct (model := localModel) (prog := programAsm)
      (dst := BASE) (src := BASE) (lret := programLabels.lamCallBase1)
      (l := amLabels) (n := nlimbs cd) (m := modVal cd) (x := V) (y := V)
      (tail := secMulModProc programLabels)
      (cont := bbCondK programLabels ++ bbK) (σ := ([] : List AVal))
      (yst := ystJ)
      memLamCallBase1 findAmEntry findAmAdd findAmSubStart findAmSub findAmSel
      findAmDoCopy findAmCopy findAmDone findLamCallBase1
      hn0 hn32 hNJ hawJ
      (by omega) (by omega) (by omega) (by omega)
      (Or.inr (Or.inr rfl)) (by omega) (by omega)
      hmodJ hm0pos hxJ hVlt hxJ (Nat.le_of_lt hVlt)
  have haw1' : 0x1f40 ≤ 32 * S1.activeWords.toNat := by
    rw [haw1]; exact hawJ
  have haw250 : S1.activeWords.toNat = 250 := by
    rw [haw1]; exact hframeJ.aw
  have hframe1 : BBFrame S1 cd := keeps_frame hkeeps1 haw1 henv1 hframeJ
  have hcell1 {c : Nat}
      (h1 : c + 32 ≤ BASE ∨ BASE + 32 * nlimbs cd ≤ c)
      (h2 : c + 32 ≤ SUBC ∨ SUBC + 32 * nlimbs cd ≤ c) {v : U256}
      (h3 : ∀ cc ∈ addModCallScratch, c + 32 ≤ cc ∨ cc + 32 ≤ c)
      (hc : loadWord ystJ.memory c = v) :
      loadWord S1.memory c = v :=
    (keeps_loadCell (c := c) (dst := BASE) (n := nlimbs cd) hkeeps1 h1 h2 h3).trans hc
  have hicell1 : loadWord S1.memory Icell = W i :=
    hcell1 (by omega) (by omega) (by decide) hicellJ
  have hwcell1 : loadWord S1.memory Wcell = W w :=
    hcell1 (by omega) (by omega) (by decide) hwcellJ
  have hjcell1 : loadWord S1.memory Jcell = W (j - 1) :=
    hcell1 (by omega) (by omega) (by decide) hjcellJ
  have hbit1 : evalExpr bitTest S1 = W ((w / 2 ^ (j - 1)) % 2) :=
    evalExpr_bitTest hwcell1 hjcell1 (by omega) (by omega)
  have hok1 : exprOK bitTest S1 := by
    show binOK .and = true ∧
      (binOK .shr = true ∧ exprOK (Expr.load Jcell) S1 ∧
        exprOK (Expr.load Wcell) S1) ∧ exprOK (Expr.imm 1) S1
    exact ⟨rfl, ⟨rfl, pin250 haw250 (by decide), pin250 haw250 (by decide)⟩,
      trivial⟩
  have hdval : (V + V) % modVal cd =
      (2 * (P * 2 ^ (8 - j) + w / 2 ^ j)) % modVal cd :=
    dbl_mod _ _ _ hVdef
  -- the two bit branches
  by_cases hbit : (w / 2 ^ (j - 1)) % 2 = 1
  · -- bit set: add ONE
    have hfall2 : ASteps programAsm ⟨bbCondK programLabels ++ bbK, [], S1⟩
        ⟨callAddMod BASE ONE programLabels.lamCallBase2 programLabels.lamEntry ++
          (([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++ bbK),
          [], S1⟩ := by
      rw [show bbCondK programLabels ++ bbK =
          jumpIfZ bitTest programLabels.lbBaseBitsSkip ++
            (callAddMod BASE ONE programLabels.lamCallBase2 programLabels.lamEntry ++
              (([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++
                bbK))
        from by simp only [bbCondK, bbOneK, List.append_assoc]]
      exact jumpIfZ_fall (model := localModel) (prog := programAsm)
        (e := bitTest) (l := programLabels.lbBaseBitsSkip)
        (k := callAddMod BASE ONE programLabels.lamCallBase2 programLabels.lamEntry ++
          (([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++
            bbK))
        (σ := ([] : List AVal)) hok1
        (by rw [hbit1, hbit]; exact W_ne_zero one_ne_zero (by norm_num))
    obtain ⟨S2, hone, hrep2, hN2, hkeeps2, haw2, henv2⟩ :=
      addModCall_correct (model := localModel) (prog := programAsm)
        (dst := BASE) (src := ONE) (lret := programLabels.lamCallBase2)
        (l := amLabels) (n := nlimbs cd) (m := modVal cd)
        (x := (V + V) % modVal cd) (y := 1)
        (tail := secMulModProc programLabels)
        (cont := ([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++
          bbK)
        (σ := ([] : List AVal)) (yst := S1)
        memLamCallBase2 findAmEntry findAmAdd findAmSubStart findAmSub findAmSel
        findAmDoCopy findAmCopy findAmDone findLamCallBase2
        hn0 hn32 hN1 haw1'
        (by omega) (by rw [hONEv, hNcv]; omega) (by omega)
        (by rw [hMODv, hONEv]; omega)
        (Or.inr (Or.inl (by rw [hBASEv, hONEv]; omega)))
        (by omega) (by rw [hONEv, hSUBCv]; omega)
        hframe1.modrep hm0pos hrep1 hlt1 hframe1.onerep (by omega)
    have haw250b : S2.activeWords.toNat = 250 := by
      rw [haw2]; exact haw250
    have hframe2 : BBFrame S2 cd := keeps_frame hkeeps2 haw2 henv2 hframe1
    have hcell2 {c : Nat}
        (h1 : c + 32 ≤ BASE ∨ BASE + 32 * nlimbs cd ≤ c)
        (h2 : c + 32 ≤ SUBC ∨ SUBC + 32 * nlimbs cd ≤ c) {v : U256}
        (h3 : ∀ cc ∈ addModCallScratch, c + 32 ≤ cc ∨ cc + 32 ≤ c)
        (hc : loadWord S1.memory c = v) :
        loadWord S2.memory c = v :=
      (keeps_loadCell (c := c) (dst := BASE) (n := nlimbs cd) hkeeps2 h1 h2 h3).trans hc
    have hicell2 : loadWord S2.memory Icell = W i :=
      hcell2 (by omega) (by omega) (by decide) hicell1
    have hwcell2 : loadWord S2.memory Wcell = W w :=
      hcell2 (by omega) (by omega) (by decide) hwcell1
    have hjcell2 : loadWord S2.memory Jcell = W (j - 1) :=
      hcell2 (by omega) (by omega) (by decide) hjcell1
    -- the value composition
    have hstep := bb_bit_step P w j hj hj8
    rw [hbit] at hstep
    have hval2 : ((V + V) % modVal cd + 1) % modVal cd =
        (P * 2 ^ (8 - (j - 1)) + w / 2 ^ (j - 1)) % modVal cd := by
      rw [add1_mod _ _ _ hdval, hstep]
    rw [hval2] at hrep2
    -- the trailing label and back-jump
    have hlabel2 : ASteps programAsm
        ⟨([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++ bbK,
          [], S2⟩
        ⟨bbSkipK programLabels ++ bbK, [], S2⟩ := by
      rw [show ([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++
            bbK =
          [.label programLabels.lbBaseBitsSkip] ++
            (bbSkipK programLabels ++ bbK)
        from by simp only [List.append_assoc]]
      exact label_steps (model := localModel) (σ := ([] : List AVal))
        (yst := S2)
    have hjmp2 : ASteps programAsm ⟨bbSkipK programLabels ++ bbK, [], S2⟩
        ⟨bbBitsK programLabels ++ bbK, [], S2⟩ := by
      rw [show bbSkipK programLabels ++ bbK =
          [.jump programLabels.lbBaseBits] ++
            (([.label programLabels.lbBaseNext] ++ bbNextK programLabels) ++ bbK)
        from by simp only [bbSkipK, List.append_assoc]]
      exact jump_steps (model := localModel) (σ := ([] : List AVal))
        findLbBaseBits
    refine ⟨S2, ⟨hframe2, hicell2, hwcell2, hjcell2, hrep2⟩, ?_⟩
    exact ((((hfall.trans hsJ).trans hdbl).trans hfall2).trans hone).trans
      (hlabel2.trans hjmp2)
  · -- bit clear: skip the add
    have hzero : (w / 2 ^ (j - 1)) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ (j - 1)) with h | h
      · exact h
      · exact absurd h hbit
    have hjmp3 : ASteps programAsm ⟨bbCondK programLabels ++ bbK, [], S1⟩
        ⟨bbSkipK programLabels ++ bbK, [], S1⟩ := by
      rw [show bbCondK programLabels ++ bbK =
          jumpIfZ bitTest programLabels.lbBaseBitsSkip ++
            (callAddMod BASE ONE programLabels.lamCallBase2 programLabels.lamEntry ++
              (([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++
                bbK))
        from by simp only [bbCondK, bbOneK, List.append_assoc]]
      exact jumpIfZ_taken (model := localModel) (prog := programAsm)
        (e := bitTest) (l := programLabels.lbBaseBitsSkip)
        (c' := bbSkipK programLabels ++ bbK)
        (k := callAddMod BASE ONE programLabels.lamCallBase2 programLabels.lamEntry ++
          (([.label programLabels.lbBaseBitsSkip] ++ bbSkipK programLabels) ++
            bbK))
        (σ := ([] : List AVal)) hok1
        (by rw [hbit1, hzero]; rfl) findLbBaseBitsSkip
    have hjmp4 : ASteps programAsm ⟨bbSkipK programLabels ++ bbK, [], S1⟩
        ⟨bbBitsK programLabels ++ bbK, [], S1⟩ := by
      rw [show bbSkipK programLabels ++ bbK =
          [.jump programLabels.lbBaseBits] ++
            (([.label programLabels.lbBaseNext] ++ bbNextK programLabels) ++ bbK)
        from by simp only [bbSkipK, List.append_assoc]]
      exact jump_steps (model := localModel) (σ := ([] : List AVal))
        findLbBaseBits
    have hstep0 := bb_bit_step P w j hj hj8
    rw [hzero] at hstep0
    have hval1 : (V + V) % modVal cd =
        (P * 2 ^ (8 - (j - 1)) + w / 2 ^ (j - 1)) % modVal cd := by
      rw [hdval, ← hstep0, Nat.add_zero]
    rw [hval1] at hrep1
    refine ⟨S1, ⟨hframe1, hicell1, hwcell1, hjcell1, hrep1⟩, ?_⟩
    exact (((hfall.trans hsJ).trans hdbl).trans hjmp3).trans hjmp4


/-- The inner bit loop: from `.label lbBaseBits` at `j = 8` down to `j = 0`,
where BASE holds the whole doubled byte. -/
theorem bb_bits_loop {cd : ByteArray} {yst : EvmState} (hm0 : modVal cd ≠ 0)
    {i w : Nat} (hw : w < 2 ^ 256) (hinv : BBits yst cd i w 8) :
    ∃ yst', BBits yst' cd i w 0 ∧
      ASteps programAsm ⟨bbBitsK programLabels ++ bbK, [], yst⟩
        ⟨bbNextK programLabels ++ bbK, [], yst'⟩ := by
  refine loop_counted (model := localModel) (prog := programAsm)
    (top := bbBitsK programLabels ++ bbK) (σ := ([] : List AVal))
    (c' := bbNextK programLabels ++ bbK)
    (Inv := fun yst3 r => r ≤ 8 ∧ BBits yst3 cd i w r)
    (P := fun yst3 => BBits yst3 cd i w 0) ?_ ?_ (n := 8) ⟨by omega, hinv⟩
  · intro r yst3 hr ⟨hrle, hinv3⟩
    obtain ⟨yst4, hinv4, hst⟩ :=
      bb_bit_round hm0 (hj := hr) (hj8 := hrle) (hw := hw) hinv3
    exact Or.inl ⟨yst4, ⟨by omega, hinv4⟩, hst⟩
  · intro yst3 ⟨_, hinv3⟩
    have hjz : evalExpr (.load Jcell) yst3 = 0 := by
      show loadWord yst3.memory Jcell = 0
      rw [hinv3.jcell]
      rfl
    refine ⟨hinv3, ?_⟩
    rw [show bbBitsK programLabels ++ bbK =
        jumpIfZ (.load Jcell) programLabels.lbBaseNext ++
          (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
            (callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
              (bbCondK programLabels ++ bbK)))
      from by simp only [bbBitsK, bbDblK, List.append_assoc]]
    exact jumpIfZ_taken (model := localModel) (prog := programAsm)
      (e := .load Jcell) (l := programLabels.lbBaseNext)
      (c' := bbNextK programLabels ++ bbK)
      (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callAddMod BASE BASE programLabels.lamCallBase1 programLabels.lamEntry ++
          (bbCondK programLabels ++ bbK)))
      (σ := ([] : List AVal)) (pin250 hinv3.fr.aw (by decide)) hjz
      findLbBaseNext

/-- One byte round of `lbBase`: fetch byte `i`, run the bit loop, bump the
counter. -/
theorem bb_byte_round {cd : ByteArray} (hv : ValidInput cd)
    (hm0 : modVal cd ≠ 0) {i : Nat} {yst : EvmState}
    (hi : i < baseSize cd) (hinv : BBase yst cd i) :
    ∃ yst', BBase yst' cd (i + 1) ∧
      ASteps programAsm ⟨bbOuterK programLabels ++ bbK, [], yst⟩
        ⟨bbOuterK programLabels ++ bbK, [], yst'⟩ := by
  have haw := hinv.fr.aw
  have hn32 := hinv.fr.hn32
  have hbs256 : baseSize cd < 2 ^ 256 :=
    size_lt _ (by obtain ⟨-, hb, -⟩ := hv; omega)
  have hbs1024 : baseSize cd ≤ 1024 := by obtain ⟨-, hb, -⟩ := hv; omega
  have hi256 : i < 2 ^ 256 := by omega
  have hi1024 : i ≤ 1024 := by omega
  have hbw : bByte cd i < 2 ^ 256 := by
    have := bByte_lt cd i
    omega
  have hBASEv : BASE = 1024 := by decide
  have hIcv : Icell = 7392 := by decide
  have hJcv : Jcell = 7424 := by decide
  have hWcv : Wcell = 7456 := by decide
  -- guard falls through
  have hfall : ASteps programAsm ⟨bbOuterK programLabels ++ bbK, [], yst⟩
      ⟨store Wcell (cdbCell BO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK))),
        [], yst⟩ := by
    rw [show bbOuterK programLabels ++ bbK =
        jumpUnlessLt (.load Icell) (.load BS) programLabels.lbBaseDone ++
          (store Wcell (cdbCell BO) ++ (store Jcell (.imm 8) ++
            ([.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK))))
      from by simp only [bbOuterK, List.append_assoc]]
    exact jumpUnlessLt_fall (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load BS)
      (l := programLabels.lbBaseDone)
      (k := store Wcell (cdbCell BO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK))))
      (σ := ([] : List AVal)) (pin250 haw (by decide)) (pin250 haw (by decide))
      (by
        show (loadWord yst.memory Icell).ult (loadWord yst.memory BS) = true
        rw [hinv.icell, hinv.fr.bscell]
        exact W_ult hi256 hbs256 hi)
  -- Wcell := byte i
  have haddr : evalExpr (.bin .add (.load BO) (.load Icell)) yst
      = W (96 + i) :=
    eval_add_loads yst BO Icell 96 i hinv.fr.bocell hinv.icell
  have hvalW : evalExpr (cdbCell BO) yst = W (bByte cd i) := by
    have h := evalExpr_cdb (e := .bin .add (.load BO) (.load Icell))
      (yst := yst) (p := 96 + i)
      (by rw [haddr, toNat_W (by omega)])
    rw [hinv.fr.env] at h
    exact h
  have hsW : ASteps programAsm
      ⟨store Wcell (cdbCell BO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK))),
        [], yst⟩
      ⟨store Jcell (.imm 8) ++ ([.label programLabels.lbBaseBits] ++
        (bbBitsK programLabels ++ bbK)), [],
        { yst with memory := storeWord yst.memory Wcell (W (bByte cd i)) }⟩ :=
    store_pin (c := Wcell) (e := cdbCell BO) (v := W (bByte cd i))
      (k := store Jcell (.imm 8) ++ ([.label programLabels.lbBaseBits] ++
        (bbBitsK programLabels ++ bbK)))
      (by
        show exprOK (Expr.bin .add (Expr.load BO) (Expr.load Icell)) yst
        exact ⟨rfl, pin250 haw (by decide), pin250 haw (by decide)⟩)
      (by decide) (by rw [haw]; show Wcell + 32 ≤ 8000; decide) hvalW
  set ystW : EvmState :=
    { yst with memory := storeWord yst.memory Wcell (W (bByte cd i)) } with hystW
  have hystWmem : ystW.memory =
      storeWord yst.memory Wcell (W (bByte cd i)) := rfl
  have hawW : ystW.activeWords.toNat = 250 := by rw [hystW]; exact haw
  -- Jcell := 8
  have hsJ : ASteps programAsm
      ⟨store Jcell (.imm 8) ++ ([.label programLabels.lbBaseBits] ++
        (bbBitsK programLabels ++ bbK)), [], ystW⟩
      ⟨[.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK), [],
        { ystW with memory := storeWord ystW.memory Jcell (W 8) }⟩ :=
    store_pin (c := Jcell) (e := .imm 8) (v := W 8)
      (k := [.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK))
      (by trivial) (by decide) (by rw [hawW]; show Jcell + 32 ≤ 8000; decide) rfl
  set ystWJ : EvmState :=
    { ystW with memory := storeWord ystW.memory Jcell (W 8) } with hystWJ
  have hystWJmem : ystWJ.memory =
      storeWord (storeWord yst.memory Wcell (W (bByte cd i))) Jcell (W 8) := rfl
  have hlabel : ASteps programAsm
      ⟨[.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK), [],
        ystWJ⟩
      ⟨bbBitsK programLabels ++ bbK, [], ystWJ⟩ :=
    label_steps (model := localModel) (σ := ([] : List AVal)) (yst := ystWJ)
  -- the inner-loop entry invariant
  have hd8 : 2 ^ (8 - 8) = 1 := by norm_num
  have hbdiv : bByte cd i / 2 ^ 8 = 0 := by
    rw [show (2 : Nat) ^ 8 = 256 from by norm_num]
    exact Nat.div_eq_of_lt (bByte_lt cd i)
  have hentry8 : (bPre cd i * 2 ^ (8 - 8) + bByte cd i / 2 ^ 8) % modVal cd
      = bPre cd i % modVal cd := by
    rw [hd8, hbdiv]; simp
  have hframeW : BBFrame ystW cd := frame_store (c := Wcell)
    (hc := ⟨by rw [hIcv, hWcv]; omega, le_refl _⟩) hinv.fr
  have hframeWJ : BBFrame ystWJ cd := frame_store (c := Jcell)
    (hc := ⟨by rw [hIcv, hJcv]; omega, by rw [hJcv, hWcv]; omega⟩) hframeW
  have hicellWJ : loadWord ystWJ.memory Icell = W i := by
    rw [hystWJmem, load_disj' _ _ _ _ (Or.inr (by omega)),
      load_disj' _ _ _ _ (Or.inr (by omega))]
    exact hinv.icell
  have hwcellWJ : loadWord ystWJ.memory Wcell = W (bByte cd i) := by
    rw [hystWJmem, load_disj' _ _ _ _ (Or.inl (by omega))]
    exact loadWord_storeWord_self _ _ _
  have hjcellWJ : loadWord ystWJ.memory Jcell = W 8 :=
    loadWord_storeWord_self _ _ _
  have hbase8 : RepresentsY ystWJ.memory BASE (nlimbs cd)
      ((bPre cd i * 2 ^ (8 - 8) + bByte cd i / 2 ^ 8) % modVal cd) := by
    have h0 : RepresentsY ystWJ.memory BASE (nlimbs cd)
        (bPre cd i % modVal cd) := by
      rw [hystWJmem]
      exact RepresentsY_storeWord_disjoint
        (RepresentsY_storeWord_disjoint hinv.baserep
          (by rw [hBASEv, hWcv]; omega))
        (by rw [hBASEv, hJcv]; omega)
    rw [← hentry8] at h0
    exact h0
  -- run the inner loop
  obtain ⟨ystB, hinvB, hstepsB⟩ :=
    bb_bits_loop (hm0 := hm0) (hw := hbw)
      (hinv := ⟨hframeWJ, hicellWJ, hwcellWJ, hjcellWJ, hbase8⟩)
  -- Icell := i + 1 and jump back
  have hvalI : evalExpr (.bin .add (.load Icell) (.imm 1)) ystB = W (i + 1) := by
    show loadWord ystB.memory Icell + W 1 = _
    rw [hinvB.icell]
    exact W_add (by omega)
  have hsI : ASteps programAsm
      ⟨bbNextK programLabels ++ bbK, [], ystB⟩
      ⟨[.jump programLabels.lbBase] ++ ([.label programLabels.lbBaseDone] ++
        (bbDoneK programLabels ++ bbK)), [],
        { ystB with memory := storeWord ystB.memory Icell (W (i + 1)) }⟩ := by
    rw [show bbNextK programLabels ++ bbK =
        store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbBase] ++ ([.label programLabels.lbBaseDone] ++
            (bbDoneK programLabels ++ bbK)))
      from by simp only [bbNextK, List.append_assoc]]
    exact store_pin (c := Icell) (e := .bin .add (.load Icell) (.imm 1))
      (v := W (i + 1))
      (k := [.jump programLabels.lbBase] ++ ([.label programLabels.lbBaseDone] ++
        (bbDoneK programLabels ++ bbK)))
      (by
        show binOK .add = true ∧ exprOK (Expr.load Icell) ystB ∧
          exprOK (Expr.imm 1) ystB
        exact ⟨rfl, pin250 hinvB.fr.aw (by decide), trivial⟩)
      (by decide) (by rw [hinvB.fr.aw]; show Icell + 32 ≤ 8000; decide) hvalI
  set ystI : EvmState :=
    { ystB with memory := storeWord ystB.memory Icell (W (i + 1)) } with hystI
  have hystImem : ystI.memory =
      storeWord ystB.memory Icell (W (i + 1)) := rfl
  have hjmp : ASteps programAsm
      ⟨[.jump programLabels.lbBase] ++ ([.label programLabels.lbBaseDone] ++
        (bbDoneK programLabels ++ bbK)), [], ystI⟩
      ⟨bbOuterK programLabels ++ bbK, [], ystI⟩ :=
    jump_steps (model := localModel) (σ := ([] : List AVal)) findLbBase
  -- the output invariant
  have hb0 : (bPre cd i * 2 ^ (8 - 0) + bByte cd i / 2 ^ 0) % modVal cd
      = bPre cd (i + 1) % modVal cd := by
    have h2 : 2 ^ (8 - 0) = 256 := by norm_num
    have h3 : bByte cd i / 2 ^ 0 = bByte cd i := by simp
    rw [h2, h3, bPre_succ]
  have hframeI : BBFrame ystI cd := frame_store (c := Icell)
    (hc := ⟨le_refl _, by rw [hIcv, hWcv]; omega⟩) hinvB.fr
  have hbaseI : RepresentsY ystI.memory BASE (nlimbs cd)
      (bPre cd (i + 1) % modVal cd) := by
    have h0 : RepresentsY ystI.memory BASE (nlimbs cd)
        ((bPre cd i * 2 ^ (8 - 0) + bByte cd i / 2 ^ 0) % modVal cd) := by
      rw [hystImem]
      exact RepresentsY_storeWord_disjoint hinvB.baserep
        (by rw [hBASEv, hIcv]; omega)
    rw [hb0] at h0
    exact h0
  refine ⟨ystI, ⟨hframeI, loadWord_storeWord_self _ _ _, hbaseI⟩, ?_⟩
  exact ((((hfall.trans hsW).trans hsJ).trans hlabel).trans hstepsB).trans
    (hsI.trans hjmp)

/-- The outer byte loop: `baseSize cd` rounds, from the invariant at `i = 0`
to `i = baseSize cd`, landing at the ACC-init call. -/
theorem bb_base_loop {cd : ByteArray} (hv : ValidInput cd) (hm0 : modVal cd ≠ 0)
    {yst : EvmState} (hinv : BBase yst cd 0) :
    ∃ yst', BBase yst' cd (baseSize cd) ∧
      ASteps programAsm ⟨bbOuterK programLabels ++ bbK, [], yst⟩
        ⟨bbDoneK programLabels ++ bbK, [], yst'⟩ := by
  have hbs256 : baseSize cd < 2 ^ 256 :=
    size_lt _ (by obtain ⟨-, hb, -⟩ := hv; omega)
  refine loop_counted (model := localModel) (prog := programAsm)
    (top := bbOuterK programLabels ++ bbK) (σ := ([] : List AVal))
    (c' := bbDoneK programLabels ++ bbK)
    (Inv := fun yst3 r => r ≤ baseSize cd ∧ BBase yst3 cd (baseSize cd - r))
    (P := fun yst3 => BBase yst3 cd (baseSize cd)) ?_ ?_
    (n := baseSize cd) (yst := yst) ⟨le_refl _, by rw [Nat.sub_self]; exact hinv⟩
  · intro r yst3 hr ⟨hrle, hinv3⟩
    obtain ⟨yst4, hinv4, hst⟩ :=
      bb_byte_round hv hm0 (hi := by omega) hinv3
    refine Or.inl ⟨yst4, ⟨by omega, ?_⟩, hst⟩
    rw [show baseSize cd - (r - 1) = baseSize cd - r + 1 from by omega]
    exact hinv4
  · intro yst3 ⟨_, hinv3⟩
    refine ⟨hinv3, ?_⟩
    rw [show bbOuterK programLabels ++ bbK =
        jumpUnlessLt (.load Icell) (.load BS) programLabels.lbBaseDone ++
          (store Wcell (cdbCell BO) ++ (store Jcell (.imm 8) ++
            ([.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK))))
      from by simp only [bbOuterK, List.append_assoc]]
    exact jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load BS) (l := programLabels.lbBaseDone)
      (c' := bbDoneK programLabels ++ bbK)
      (k := store Wcell (cdbCell BO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbBaseBits] ++ (bbBitsK programLabels ++ bbK))))
      (σ := ([] : List AVal)) (pin250 hinv3.fr.aw (by decide))
      (pin250 hinv3.fr.aw (by decide))
      (by
        show ¬(loadWord yst3.memory Icell).ult (loadWord yst3.memory BS)
        rw [hinv3.icell, hinv3.fr.bscell]
        exact W_nult hbs256 hbs256 (le_refl _))
      findLbBaseDone

/-! ## The main theorem -/

/-- The base reduction and accumulator init composed: from the big-path
post-scan state (MOD represents the nonzero modulus `m`, everything above the
MOD region still zero) to the exponent-scan continuation, with BASE holding
`b % m` (the reduced base) and ACC holding `1 % m`.  This is the
header → load → base link the big-path composer chains. -/
theorem big_base {cd : ByteArray} (hv : ValidInput cd) {yst : EvmState}
    (hgt : 32 < modulusSize cd)
    (hinv : BMScan yst cd (nlimbs cd)) (hm0 : modVal cd ≠ 0) :
    ∃ yst', BBExit yst' cd ∧
      ASteps programAsm ⟨bigMid programLabels ++ bbK, [], yst⟩
        ⟨bbExpRest programLabels ++ bbK, [], yst'⟩ := by
  obtain ⟨yst1, hinv1, hsteps1⟩ := bb_entry hv hgt hinv
  obtain ⟨yst2, hinv2, hsteps2⟩ := bb_base_loop hv hm0 hinv1
  -- the ACC-init call
  have hn0 := hinv2.fr.hn0
  have hn32 := hinv2.fr.hn32
  have haw2 : 0x1f40 ≤ 32 * yst2.activeWords.toNat := by
    rw [hinv2.fr.aw]
  have hN2 : (loadWord yst2.memory Ncell).toNat = nlimbs cd := by
    rw [hinv2.fr.ncell, toNat_W
      (Nat.lt_of_le_of_lt hn32 (by norm_num : (32 : Nat) < 2 ^ 256))]
  have hm0pos : 0 < modVal cd := Nat.pos_of_ne_zero hm0
  have hMODv : MOD = (0 : Nat) := rfl
  have hBASEv : BASE = 1024 := by decide
  have hACCv : ACC = 2048 := by decide
  have hONEv : ONE = 4096 := by decide
  have hSUBCv : SUBC = 5120 := by decide
  have hNcv : Ncell = 7360 := by decide
  have hIcv : Icell = 7392 := by decide
  have hESv : ES = 7200 := by decide
  have hBSv : BS = 7168 := by decide
  have hMSv : MS = 7232 := by decide
  have hBOv : BO = 7264 := by decide
  have hEOv : EO = 7296 := by decide
  have hC1v : C1 = 7488 := by decide
  obtain ⟨yst3, hacc, hrep3, hN3, hkeeps3, haw3, henv3⟩ :=
    addModCall_correct (model := localModel) (prog := programAsm)
      (dst := ACC) (src := ONE) (lret := programLabels.lamCallAccInit)
      (l := amLabels) (n := nlimbs cd) (m := modVal cd) (x := 0) (y := 1)
      (tail := secMulModProc programLabels)
      (cont := bbExpRest programLabels ++ bbK) (σ := ([] : List AVal))
      (yst := yst2)
      memLamCallAccInit findAmEntry findAmAdd findAmSubStart findAmSub findAmSel
      findAmDoCopy findAmCopy findAmDone findLamCallAccInit
      hn0 hn32 hN2 haw2
      (by rw [hACCv, hNcv]; omega) (by rw [hONEv, hNcv]; omega)
      (by rw [hMODv, hACCv]; omega) (by rw [hMODv, hONEv]; omega)
      (Or.inr (Or.inl (by rw [hACCv, hONEv]; omega)))
      (by rw [hACCv, hSUBCv]; omega) (by rw [hONEv, hSUBCv]; omega)
      hinv2.fr.modrep hm0pos hinv2.fr.accrep (by omega) hinv2.fr.onerep
      (by omega)
  -- the exit predicate
  have haw3' : yst3.activeWords.toNat = 250 := by
    rw [haw3]; exact hinv2.fr.aw
  have hcell3 {c : Nat}
      (h1 : c + 32 ≤ ACC ∨ ACC + 32 * nlimbs cd ≤ c)
      (h2 : c + 32 ≤ SUBC ∨ SUBC + 32 * nlimbs cd ≤ c)
      (h3 : ∀ cc ∈ addModCallScratch, c + 32 ≤ cc ∨ cc + 32 ≤ c) {v : U256}
      (hc : loadWord yst2.memory c = v) :
      loadWord yst3.memory c = v :=
    (keeps_loadCell (c := c) (dst := ACC) (n := nlimbs cd) hkeeps3 h1 h2 h3).trans hc
  have hrep3' : RepresentsY yst3.memory ACC (nlimbs cd) (1 % modVal cd) := by
    rw [Nat.zero_add] at hrep3
    exact hrep3
  have hmod3 : RepresentsY yst3.memory MOD (nlimbs cd) (modVal cd) :=
    keeps_rep (R := MOD) (dst := ACC) (n := nlimbs cd) hkeeps3 hinv2.fr.modrep
      (by rw [hMODv, hACCv]; omega) (by rw [hMODv, hSUBCv]; omega)
      (by intro cc hcc
          have hmem : ∀ cc ∈ addModCallScratch, C1 ≤ cc := by decide
          have hcc' := hmem cc hcc
          omega)
  have hone3 : RepresentsY yst3.memory ONE (nlimbs cd) 1 :=
    keeps_rep (R := ONE) (dst := ACC) (n := nlimbs cd) hkeeps3 hinv2.fr.onerep
      (by rw [hONEv, hACCv]; omega) (by rw [hONEv, hSUBCv]; omega)
      (by intro cc hcc
          have hmem : ∀ cc ∈ addModCallScratch, C1 ≤ cc := by decide
          have hcc' := hmem cc hcc
          omega)
  have hbase3 : RepresentsY yst3.memory BASE (nlimbs cd)
      (bPre cd (baseSize cd) % modVal cd) :=
    keeps_rep (R := BASE) (dst := ACC) (n := nlimbs cd) hkeeps3 hinv2.baserep
      (by rw [hBASEv, hACCv]; omega) (by rw [hBASEv, hSUBCv]; omega)
      (by intro cc hcc
          have hmem : ∀ cc ∈ addModCallScratch, C1 ≤ cc := by decide
          have hcc' := hmem cc hcc
          omega)
  refine ⟨yst3, ⟨haw3', by rw [henv3]; exact hinv2.fr.env, hn0, hn32,
    hcell3 (by omega) (by omega) (by decide) hinv2.icell,
    hcell3 (by omega) (by omega) (by decide) hinv2.fr.ncell,
    hcell3 (by omega) (by omega) (by decide) hinv2.fr.mscell,
    hcell3 (by omega) (by omega) (by decide) hinv2.fr.bscell,
    hcell3 (by omega) (by omega) (by decide) hinv2.fr.escell,
    hcell3 (by omega) (by omega) (by decide) hinv2.fr.bocell,
    hcell3 (by omega) (by omega) (by decide) hinv2.fr.eocell,
    hmod3, hone3, hbase3, hrep3'⟩, ?_⟩
  rw [show bigMid programLabels ++ bbK = bbEntryK programLabels ++ bbK from by
    rw [bigMid_eq]]
  exact (hsteps1.trans hsteps2).trans hacc

/-- The composer-facing form of `big_base` (identical contract, the
deliverable's name): from the `big_scan_nonzero` landing state at
`bigMid ++ (secTailSer ++ progTail)` to the exponent-scan continuation. -/
theorem bigBase_correct {cd : ByteArray} (hv : ValidInput cd) {yst : EvmState}
    (hgt : 32 < modulusSize cd)
    (hinv : BMScan yst cd (nlimbs cd)) (hm0 : modVal cd ≠ 0) :
    ∃ yst', BBExit yst' cd ∧
      ASteps programAsm ⟨bigMid programLabels ++ bbK, [], yst⟩
        ⟨bbExpRest programLabels ++ bbK, [], yst'⟩ :=
  big_base hv hgt hinv hm0

end Challenge.Modexp.Submission.Proof.BigBaseProc

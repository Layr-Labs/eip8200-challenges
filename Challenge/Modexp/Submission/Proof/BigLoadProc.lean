import Challenge.Modexp.Submission.Proof.HeaderProc
import Challenge.Modexp.Submission.Proof.YulLimbs
import Challenge.Modexp.Submission.Proofs.Limbs
import Mathlib.Tactic

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-!
# The MODEXP big path: modulus load and zero-scan

`secBigPath`'s head, from `.label lbig` through the end of the modulus
zero-scan: the `TOP`/`Ncell`/`Icell` preamble, the `lbLoad` loop that splices
the `msize` modulus bytes (read big-endian out of the calldata) into
little-endian 256-bit limbs over the `MOD` region, and the `lbMScan` OR-scan
over those limbs.

Entry contract (produced by `Proof.Header.header_big`): control at the code
after `.label lbig` (=`bigEntryCode programLabels ++ progTail`) with
the header exit state `hst6 cd` (six scalar cells, `activeWords = 230`,
everything below `BS` zero) and `32 < msize ≤ 1024`.

Exit contract (`big_scan_zero` / `big_scan_nonzero`), with
`n = limbCount msize`, `modOff = 96 + bsize + esize`,
`m = bytesToNatPadded cd modOff msize`:

* the `MOD` region `RepresentsY`-holds `m` with `n` limbs;
* `Ncell = W n`, `Icell = W n`, `MS = W msize`, `MO = W modOff`, the other
  header cells unchanged; `activeWords = 250` exactly (the `TOP` store raises
  it from 230; every later touch is pinned); calldata unchanged;
* every region between the limbs and the scalar block
  (`32*n ≤ a < BS`: `BASE/ACC/OUT/ONE/SUBC/RET` and the limb-tail padding)
  is still zero;
* `T0` holds the OR of all `n` limbs: zero exactly when `m = 0`, selecting
  the `lbSer` serialize jump (`m = 0`: `ACC` is still zero there) versus the
  `store ONE 1` base-reduction continuation (`m ≠ 0`).

The generic helpers (`nat_lor_le`, `W_or_add`, the `wordVal` split,
`ofDigits_set`) live here and are reused by `Proof/BigSer.lean`.
-/

namespace Challenge.Modexp.Submission.Proof.BigLoad

open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState wordFrom byteFrom byteAt loadWord storeWord
  storeByte readBytes touchMemory activeWordsAfter b2w)
open Challenge.Modexp.Submission (Expr store storeAt storeAt8 jumpIfNz jumpIfZ
  jumpUnlessLt cdbCell bitTest compileExpr loadAt evalExpr exprOK
  BS ES MS BO EO MO Ncell Icell I2 Jcell Wcell T0 T1 T2 RET TOP ONE ACC BASE MOD OUT
  SUBC HIcell C1 C2 AOFF AX AY AS AZ BPTR
  programAsm localModel callAddMod callMulMod)
open Challenge.Modexp.Submission.Proof.Header
open Challenge.Modexp.Submission.Proof.YulMem
open Challenge.Modexp.Submission.Proof.YulLimbs
open Challenge.Modexp.Submission.Proofs.Limbs (radix limbCount limbDigits
  length_limbDigits limbDigits_lt value_limbDigits radix_gt_one radix_pos
  pow_radix limbCount_le_32 width_le_limbs limbCount_pos)
open Challenge.Modexp (baseSize exponentSize modulusSize spec ValidInput)
open EvmSemantics.EVM.Precompile (bytesToNatPadded)

/-- Shorthand for the 256-bit word carrying the natural `n`. -/
local notation:max "W " n:max => BitVec.ofNat 256 n

/-! ## Nat and word helpers -/

/-- Or-ing a number below `2 ^ k` onto a multiple of `2 ^ k` is addition. -/
private theorem nat_lor_le : ∀ (k q b : Nat), b < 2 ^ k →
    2 ^ k * q ||| b = 2 ^ k * q + b := by
  intro k
  induction k with
  | zero =>
      intro q b hb
      have hb0 : b = 0 := by simpa using hb
      subst hb0
      simp
  | succ k ih =>
      intro q b hb
      have hbit : 2 ^ (k + 1) * q = Nat.bit false (2 ^ k * q) := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.bit_val, Bool.toNat_false]
        ring
      rw [hbit]
      induction b using Nat.binaryRec with
      | zero => simp
      | bit bl b' _ =>
          have hbt : bl.toNat ≤ 1 := by cases bl <;> decide
          have hb' : b' < 2 ^ k := by
            simp only [Nat.bit_val, Nat.pow_succ] at hb
            omega
          rw [Nat.lor_bit, ih q b' hb']
          simp only [Nat.bit_val, Bool.false_or, Bool.toNat_false]
          omega

/-- Word-level OR-splice: OR-ing a word whose low `2 ^ j` bits are zero with
one below `2 ^ j` (the sum small enough not to wrap). -/
private theorem W_or_add {x y j : Nat} (hx : x < 2 ^ 256) (hy : y < 2 ^ 256)
    (hsum : x + y < 2 ^ 256) (hyj : y < 2 ^ j) (hxj : x % 2 ^ j = 0) :
    (W x) ||| (W y) = W (x + y) := by
  apply BitVec.eq_of_toNat_eq
  have hxq : x = 2 ^ j * (x / 2 ^ j) := by
    have hmd := Nat.mod_add_div x (2 ^ j)
    rw [hxj] at hmd
    omega
  rw [BitVec.toNat_or, toNat_W hx, toNat_W hy, toNat_W hsum, hxq,
    nat_lor_le j (x / 2 ^ j) y hyj]

/-- A full shift of a small word. -/
private theorem W_shl_full {b s : Nat} (h : b * 2 ^ s < 2 ^ 256) :
    (W b) <<< s = W (b * 2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  have hb : b < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right b (Nat.two_pow_pos s)) h
  rw [BitVec.toNat_shiftLeft, toNat_W hb, toNat_W h]
  simp
  omega

/-- A byte range that is entirely zero has value zero. -/
private theorem wordVal_zero_range : ∀ (m : Nat → UInt8) (p k : Nat),
    (∀ a, p ≤ a → a < p + k → m a = 0) → wordVal m p k = 0 := by
  intro m p k
  induction k generalizing p with
  | zero => intro _; rfl
  | succ k ih =>
      intro hz
      rw [wordVal_succ, ih p (fun a ha hb => hz a (by omega) (by omega)),
        hz (p + k) (by omega) (by omega)]
      simp

/-- Splitting a big-endian byte value at an inner boundary: the last `j`
bytes of the window at `p` are the window at `p + (k - j)`. -/
private theorem wordVal_split : ∀ (m : Nat → UInt8) (j p k : Nat), j ≤ k →
    wordVal m p k = wordVal m p (k - j) * 256 ^ j + wordVal m (p + (k - j)) j := by
  intro m j
  induction j with
  | zero =>
      intro p k _
      simp [wordVal]
  | succ j ih =>
      intro p k hj
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hjk' : j ≤ k' := by omega
      rw [wordVal_succ m p k', ih p k' hjk',
        show k' - j = k' + 1 - (j + 1) from by omega,
        wordVal_succ m (p + (k' + 1 - (j + 1))) j,
        show p + (k' + 1 - (j + 1)) + j = p + k' from by omega,
        Nat.pow_succ]
      ring

/-- A word whose last `j` bytes are all zero is `0` modulo `256 ^ j`. -/
private theorem wordVal_mod_zero (m : Nat → UInt8) (p j : Nat) (hj : j ≤ 32)
    (hzero : ∀ a, p + (32 - j) ≤ a → a < p + 32 → m a = 0) :
    wordVal m p 32 % 256 ^ j = 0 := by
  have hsplit := wordVal_split m j p 32 (by omega)
  have hlast : wordVal m (p + (32 - j)) j = 0 :=
    wordVal_zero_range m (p + (32 - j)) j (fun a ha hb => hzero a ha (by omega))
  rw [hsplit, hlast, Nat.add_zero, Nat.mul_mod_left]

/-- Byte `j` (little-endian) of a multiple of `256 ^ (j + 1)` is zero. -/
private theorem byteAt_of_mod {x j : Nat} (hx256 : x < 2 ^ 256)
    (hx : x % 256 ^ (j + 1) = 0) :
    (byteAt (W x) j).toNat = 0 := by
  rw [byteAt_toNat_div, toNat_W hx256]
  have hxq : x = 256 ^ (j + 1) * (x / 256 ^ (j + 1)) := by
    have hmd := Nat.mod_add_div x (256 ^ (j + 1))
    rw [hx] at hmd
    omega
  rw [hxq, Nat.pow_succ, Nat.mul_assoc,
    Nat.mul_div_cancel_left _ (by norm_num : (0 : Nat) < 256 ^ j),
    Nat.mul_mod_right]

/-- Updating one digit of an `ofDigits` sum. -/
private theorem ofDigits_set : ∀ {l : List Nat} {i x : Nat}, i < l.length →
    l[i]! ≤ x → ∀ b : Nat,
    Nat.ofDigits b (l.set i x) = Nat.ofDigits b l + b ^ i * (x - l[i]!) := by
  intro l
  induction l with
  | nil => intro _ _ hi _; exact absurd hi (Nat.not_lt_zero _)
  | cons h t ih =>
      intro i x hi hle b
      cases i with
      | zero =>
          show Nat.ofDigits b (x :: t) = Nat.ofDigits b (h :: t) + b ^ 0 * (x - h)
          rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.pow_zero, Nat.one_mul]
          have hle0 : h ≤ x := by simpa using hle
          omega
      | succ i' =>
          have hi' : i' < t.length := by simpa using hi
          have hle' : t[i']! ≤ x := by simpa using hle
          show Nat.ofDigits b (h :: t.set i' x)
            = Nat.ofDigits b (h :: t) + b ^ (i' + 1) * (x - (h :: t)[i' + 1]!)
          rw [Nat.ofDigits_cons, Nat.ofDigits_cons, List.getElem!_cons_succ,
            ih hi' hle' b, Nat.pow_succ]
          ring


/-! ## The big-path head fragments -/

/-- The computation between the zero-scan and serialize (not this module's
scope): base reduction, accumulator init, exponent loops, from
`store ONE 1` to just before `.label lbSer`. Flat `++` chain, used only as
an opaque continuation. -/
def bigMid (l : ProgLabels) : List Asm :=
  store ONE (.imm 1) ++
  store Icell (.imm 0) ++
  [.label l.lbBase] ++
  jumpUnlessLt (.load Icell) (.load BS) l.lbBaseDone ++
  store Wcell (cdbCell BO) ++
  store Jcell (.imm 8) ++
  [.label l.lbBaseBits] ++
  jumpIfZ (.load Jcell) l.lbBaseNext ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  callAddMod BASE BASE l.lamCallBase1 l.lamEntry ++
  jumpIfZ bitTest l.lbBaseBitsSkip ++
  callAddMod BASE ONE l.lamCallBase2 l.lamEntry ++
  [.label l.lbBaseBitsSkip] ++
  [.jump l.lbBaseBits] ++
  [.label l.lbBaseNext] ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lbBase] ++
  [.label l.lbBaseDone] ++
  callAddMod ACC ONE l.lamCallAccInit l.lamEntry ++
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

/-- The serialize-and-return section from `.label lbSer` (`BigSer.lean`). -/
def bpSer (l : ProgLabels) : List Asm :=
  store Icell (.imm 0) ++
  [.label l.lbSerLoop] ++
  (jumpUnlessLt (.load Icell) (.load MS) l.lbReturn ++
  (store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
  (storeAt8 (.bin .add (.imm RET) (.load Icell))
    (.bin .shr (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
      (loadAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))))) ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lbSerLoop] ++
  [.label l.lbReturn] ++
  (compileExpr (.load MS) ++ (compileExpr (.imm RET) ++ [.op .ret])))))))

/-- From `.label lbMScanDone` on: the zero/nonzero dispatch, then `bigMid`. -/
def bpMScanDone (l : ProgLabels) : List Asm :=
  [.label l.lbMScanDone] ++
  (jumpIfZ (.load T0) l.lbSer ++ bigMid l)

/-- The `lbMScan` loop body: closed chunk, ends with the back-jump. -/
def bpMScan (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load Ncell) l.lbMScanDone ++
  (store T0 (.bin .or (.load T0) (loadAt (.bin .mul (.imm 32) (.load Icell)))) ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump l.lbMScan]))

/-- The scan preamble between the two loop labels. -/
def bpScanInit (_l : ProgLabels) : List Asm :=
  store T0 (.imm 0) ++ store Icell (.imm 0)

/-- The `lbLoad` loop body: closed chunk, ends with the back-jump. -/
def bpLoad (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load MS) l.lbLoadDone ++
  (store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
  (store T1 (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))) ++
  (storeAt (.load T1) (.bin .or (loadAt (.load T1))
    (.bin .shl (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32))) (cdbCell MO))) ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump l.lbLoad]))))

/-- The big path's preamble stores (no labels). -/
def bpEntry (_l : ProgLabels) : List Asm :=
  store TOP (.imm 0) ++
  (store Ncell (.bin .div (.bin .add (.load MS) (.imm 31)) (.imm 32)) ++
  store Icell (.imm 0))

/-- From `.label lbSer` on. -/
def secTailSer (l : ProgLabels) : List Asm := [.label l.lbSer] ++ bpSer l

/-- The code from `.label lbMScan` on (the zero-scan loop top). -/
def bigMScanTop (l : ProgLabels) : List Asm :=
  bpMScan l ++ (bpMScanDone l ++ secTailSer l)

/-- The code from `.label lbLoadDone` on. -/
def bigScanInit (l : ProgLabels) : List Asm :=
  bpScanInit l ++ ([.label l.lbMScan] ++ bigMScanTop l)

/-- The code from `.label lbLoad` on (the load loop top). -/
def bigLoadTop (l : ProgLabels) : List Asm :=
  bpLoad l ++ ([.label l.lbLoadDone] ++ bigScanInit l)

/-- The code from `.label lbig` on (the big-path entry). -/
def bigEntryCode (l : ProgLabels) : List Asm :=
  bpEntry l ++ ([.label l.lbLoad] ++ bigLoadTop l)

/-- The section as a flat chain over the label-free chunks. -/
theorem secBigPath_splitSer : secBigPath programLabels =
    [.label programLabels.lbig] ++ bpEntry programLabels ++
    [.label programLabels.lbLoad] ++ bpLoad programLabels ++
    [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
    [.label programLabels.lbMScan] ++ bpMScan programLabels ++
    bpMScanDone programLabels ++ secTailSer programLabels := by rfl

/-! ## Label resolutions against the concrete program -/

/-- Resolve a label defined inside `secBigPath`: `pre` is its prefix inside
the section (label-free below the label), `tail` the section's remainder from
just after the label. -/
theorem resolve_big {lbl : Label} {pre tail : List Asm}
    (h1 : lbl ∉ labelDefs (secHeader programLabels))
    (h2 : lbl ∉ labelDefs (secWordPath programLabels))
    (h3 : lbl ∉ labelDefs pre)
    (hsplit : secBigPath programLabels = pre ++ [Asm.label lbl] ++ tail) :
    findLabel lbl programAsm = some (tail ++ progTail) := by
  rw [programAsm_eq, hsplit]
  simp only [List.append_assoc]
  rw [findLabel_pre h1, findLabel_pre h2, findLabel_pre h3]
  exact findLabel_here (pre := []) (by simp [labelDefs])

theorem findLbig : findLabel programLabels.lbig programAsm =
    some (bigEntryCode programLabels ++ progTail) :=
  resolve_big (pre := []) (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [Asm.label programLabels.lbig] ++ bigEntryCode programLabels from by
      rw [secBigPath_splitSer]
      simp only [bigEntryCode, bigLoadTop, bigScanInit, bigMScanTop, List.append_assoc])

theorem findLbLoad : findLabel programLabels.lbLoad programAsm =
    some (bigLoadTop programLabels ++ progTail) :=
  resolve_big
    (pre := [.label programLabels.lbig] ++ bpEntry programLabels)
    (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [.label programLabels.lbig] ++ bpEntry programLabels ++
          [Asm.label programLabels.lbLoad] ++ bigLoadTop programLabels from by
      rw [secBigPath_splitSer]
      simp only [bigLoadTop, bigScanInit, bigMScanTop, List.append_assoc])

theorem findLbLoadDone : findLabel programLabels.lbLoadDone programAsm =
    some (bigScanInit programLabels ++ progTail) :=
  resolve_big
    (pre := [.label programLabels.lbig] ++ bpEntry programLabels ++
      [.label programLabels.lbLoad] ++ bpLoad programLabels)
    (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [.label programLabels.lbig] ++ bpEntry programLabels ++
          [.label programLabels.lbLoad] ++ bpLoad programLabels ++
          [Asm.label programLabels.lbLoadDone] ++ bigScanInit programLabels from by
      rw [secBigPath_splitSer]
      simp only [bigScanInit, bigMScanTop, List.append_assoc])

theorem findLbMScan : findLabel programLabels.lbMScan programAsm =
    some (bigMScanTop programLabels ++ progTail) :=
  resolve_big
    (pre := [.label programLabels.lbig] ++ bpEntry programLabels ++
      [.label programLabels.lbLoad] ++ bpLoad programLabels ++
      [.label programLabels.lbLoadDone] ++ bpScanInit programLabels)
    (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [.label programLabels.lbig] ++ bpEntry programLabels ++
          [.label programLabels.lbLoad] ++ bpLoad programLabels ++
          [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
          [Asm.label programLabels.lbMScan] ++ bigMScanTop programLabels from by
      rw [secBigPath_splitSer]
      simp only [bigMScanTop, List.append_assoc])

theorem findLbMScanDone : findLabel programLabels.lbMScanDone programAsm =
    some (jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
      secTailSer programLabels ++ progTail) :=
  resolve_big
    (pre := [.label programLabels.lbig] ++ bpEntry programLabels ++
      [.label programLabels.lbLoad] ++ bpLoad programLabels ++
      [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
      [.label programLabels.lbMScan] ++ bpMScan programLabels)
    (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [.label programLabels.lbig] ++ bpEntry programLabels ++
          [.label programLabels.lbLoad] ++ bpLoad programLabels ++
          [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
          [.label programLabels.lbMScan] ++ bpMScan programLabels ++
          [Asm.label programLabels.lbMScanDone] ++
          (jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
            secTailSer programLabels) from by
      rw [secBigPath_splitSer]
      simp only [bpMScanDone, List.append_assoc])

/-- The serialize label: the heavy resolution — its prefix contains the whole
`bigMid` computation. -/
theorem findLbSer : findLabel programLabels.lbSer programAsm =
    some (bpSer programLabels ++ progTail) :=
  resolve_big
    (pre := [.label programLabels.lbig] ++ bpEntry programLabels ++
      [.label programLabels.lbLoad] ++ bpLoad programLabels ++
      [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
      [.label programLabels.lbMScan] ++ bpMScan programLabels ++
      bpMScanDone programLabels)
    (by decide) (by decide) (by decide)
    (show secBigPath programLabels =
        [.label programLabels.lbig] ++ bpEntry programLabels ++
          [.label programLabels.lbLoad] ++ bpLoad programLabels ++
          [.label programLabels.lbLoadDone] ++ bpScanInit programLabels ++
          [.label programLabels.lbMScan] ++ bpMScan programLabels ++
          bpMScanDone programLabels ++ [Asm.label programLabels.lbSer] ++
          bpSer programLabels from by
      rw [secBigPath_splitSer]
      simp only [secTailSer, List.append_assoc])


/-! ## Entry state and stores -/

/-- The modulus operand's calldata offset. -/
def modOff (cd : ByteArray) : Nat := 96 + baseSize cd + exponentSize cd

/-- The limb count for the modulus. -/
def nlimbs (cd : ByteArray) : Nat := limbCount (modulusSize cd)

/-- Memory after the big-path preamble stores (`TOP := 0`, `Ncell := n`,
`Icell := 0`) over the header exit memory. -/
def blmTOP (cd : ByteArray) : Nat → UInt8 := storeWord (hdrMem cd) TOP (W 0)

def blmNc (cd : ByteArray) : Nat → UInt8 := storeWord (blmTOP cd) Ncell (W (nlimbs cd))

def blMem0 (cd : ByteArray) : Nat → UInt8 := storeWord (blmNc cd) Icell (W 0)

/-- The state entering the `lbLoad` loop. -/
def bl0 (cd : ByteArray) : EvmState :=
  { hst6 cd with memory := blMem0 cd, activeWords := W 250 }

theorem bl0_activeWords (cd : ByteArray) : (bl0 cd).activeWords.toNat = 250 := rfl

theorem bl0_env (cd : ByteArray) : (bl0 cd).env.calldata = cd.toList := rfl

theorem bl0_mem (cd : ByteArray) : blMem0 cd =
    storeWord (storeWord (storeWord (hdrMem cd) TOP (W 0))
      Ncell (W (nlimbs cd))) Icell (W 0) := rfl

/-- Disjoint-load helper on plain memory functions. -/
theorem load_disj' (m : Nat → UInt8) (p q : Nat) (v : U256)
    (h : p + 32 ≤ q ∨ q + 32 ≤ p) :
    loadWord (storeWord m p v) q = loadWord m q :=
  loadWord_storeWord_disjoint h

/-- A store strictly outside the address's window leaves it untouched. -/
theorem storeWord_out (m : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : ¬(p ≤ a ∧ a < p + 32)) : storeWord m p v a = m a := by
  show (if p ≤ a ∧ a < p + 32 then byteAt v (31 - (a - p)) else m a) = m a
  rw [if_neg h]

/-- A store strictly above the address leaves it untouched. -/
private theorem store_out' (m : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : a < p) : storeWord m p v a = m a := by
  show (if p ≤ a ∧ a < p + 32 then byteAt v (31 - (a - p)) else m a) = m a
  rw [if_neg (by omega : ¬ (p ≤ a ∧ a < p + 32))]

/-- Every byte below the scalar block is still zero in the entry state
(the preamble stores are all at or above `BS`). -/
theorem bl0_zero (cd : ByteArray) : ∀ a, a < BS → blMem0 cd a = 0 := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0c, hT1c, hWc, hI2c, -⟩ :=
    cells_num
  intro a ha
  show blMem0 cd a = 0
  rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
    store_out' (blmNc cd) Icell (W 0) a (by omega),
    show blmNc cd = storeWord (blmTOP cd) Ncell (W (nlimbs cd)) from rfl,
    store_out' (blmTOP cd) Ncell (W (nlimbs cd)) a (by omega),
    show blmTOP cd = storeWord (hdrMem cd) TOP (W 0) from rfl,
    store_out' (hdrMem cd) TOP (W 0) a (by omega)]
  exact hst6_zero cd a ha

/-- A load anywhere in the limb region of the entry state is zero. -/
private theorem bl0_load_zero (cd : ByteArray) (hv : ValidInput cd) (p : Nat)
    (hp : p + 32 ≤ 32 * nlimbs cd) : loadWord (blMem0 cd) p = 0 := by
  have hn : nlimbs cd ≤ 32 := limbCount_le_32 (modulusSize cd) hv.2.2.2
  have hz : ∀ a, p ≤ a → a < p + 32 → blMem0 cd a = 0 := by
    intro a ha hb
    exact bl0_zero cd a (by
      obtain ⟨hBS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := cells_num
      omega)
  rw [loadWord_eq, wordVal_zero_range (blMem0 cd) p 32 hz]
  rfl

/-- The MOD region of the entry state is all zero, hence represents `0`. -/
theorem bl0_mod_zero (cd : ByteArray) (hv : ValidInput cd) :
    RepresentsY (blMem0 cd) MOD (nlimbs cd) 0 := by
  have hn : nlimbs cd ≤ 32 := limbCount_le_32 (modulusSize cd) hv.2.2.2
  have hlimbs : yLimbs (blMem0 cd) MOD (nlimbs cd)
      = List.replicate (nlimbs cd) 0 := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [yLimbs, List.getElem_map, List.getElem_range, List.getElem_replicate]
    rw [bl0_load_zero cd hv _ (by
      obtain ⟨hBS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := cells_num
      have hn : nlimbs cd ≤ 32 := limbCount_le_32 (modulusSize cd) hv.2.2.2
      have hMOD : MOD = 0 := by decide
      have hli : i < nlimbs cd := by rw [← length_yLimbs (blMem0 cd) MOD (nlimbs cd)]; exact h1
      omega)]
    rfl
  have hdigits : limbDigits (nlimbs cd) 0 = List.replicate (nlimbs cd) 0 := by
    have h1 := (representsY_zero MOD (nlimbs cd)).2
    rw [yLimbs_zero] at h1
    exact h1.symm
  exact ⟨Nat.one_le_pow _ radix radix_pos, by rw [hlimbs, hdigits]⟩

/-- The scalar cells of the entry state: the header cells are unchanged
(`TOP := 0` writes zeros over zeros), and `Ncell` holds the limb count. -/
theorem bl0_cells (cd : ByteArray) :
    loadWord (blMem0 cd) BS = W (baseSize cd) ∧
    loadWord (blMem0 cd) ES = W (exponentSize cd) ∧
    loadWord (blMem0 cd) MS = W (modulusSize cd) ∧
    loadWord (blMem0 cd) BO = W 96 ∧
    loadWord (blMem0 cd) EO = W (96 + baseSize cd) ∧
    loadWord (blMem0 cd) MO = W (modOff cd) ∧
    loadWord (blMem0 cd) Ncell = W (nlimbs cd) := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hT0p, -, -, -, -, -⟩ := cells_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show loadWord (blMem0 cd) BS = _
    rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
      load_disj' (blmNc cd) Icell BS (W 0) (Or.inr (by omega)),
      show blmNc cd = storeWord (blmTOP cd) Ncell (W (nlimbs cd)) from rfl,
      load_disj' (blmTOP cd) Ncell BS (W (nlimbs cd)) (Or.inr (by omega)),
      show blmTOP cd = storeWord (hdrMem cd) TOP (W 0) from rfl,
      load_disj' (hdrMem cd) TOP BS (W 0) (Or.inr (by omega))]
    exact (hst6_cells cd).1
  · show loadWord (blMem0 cd) ES = _
    rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
      load_disj' (blmNc cd) Icell ES (W 0) (Or.inr (by omega)),
      show blmNc cd = storeWord (blmTOP cd) Ncell (W (nlimbs cd)) from rfl,
      load_disj' (blmTOP cd) Ncell ES (W (nlimbs cd)) (Or.inr (by omega)),
      show blmTOP cd = storeWord (hdrMem cd) TOP (W 0) from rfl,
      load_disj' (hdrMem cd) TOP ES (W 0) (Or.inr (by omega))]
    exact (hst6_cells cd).2.1
  · show loadWord (blMem0 cd) MS = _
    rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
      load_disj' (blmNc cd) Icell MS (W 0) (Or.inr (by omega)),
      show blmNc cd = storeWord (blmTOP cd) Ncell (W (nlimbs cd)) from rfl,
      load_disj' (blmTOP cd) Ncell MS (W (nlimbs cd)) (Or.inr (by omega)),
      show blmTOP cd = storeWord (hdrMem cd) TOP (W 0) from rfl,
      load_disj' (hdrMem cd) TOP MS (W 0) (Or.inr (by omega))]
    exact (hst6_cells cd).2.2.1
  · show loadWord (blMem0 cd) BO = _
    rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
      load_disj' (blmNc cd) Icell BO (W 0) (Or.inr (by omega)),
      show blmNc cd = storeWord (blmTOP cd) Ncell (W (nlimbs cd)) from rfl,
      load_disj' (blmTOP cd) Ncell BO (W (nlimbs cd)) (Or.inr (by omega)),
      show blmTOP cd = storeWord (hdrMem cd) TOP (W 0) from rfl,
      load_disj' (hdrMem cd) TOP BO (W 0) (Or.inr (by omega))]
    exact (hst6_cells cd).2.2.2.1
  · show loadWord (blMem0 cd) EO = _
    rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
      load_disj' (blmNc cd) Icell EO (W 0) (Or.inr (by omega)),
      show blmNc cd = storeWord (blmTOP cd) Ncell (W (nlimbs cd)) from rfl,
      load_disj' (blmTOP cd) Ncell EO (W (nlimbs cd)) (Or.inr (by omega)),
      show blmTOP cd = storeWord (hdrMem cd) TOP (W 0) from rfl,
      load_disj' (hdrMem cd) TOP EO (W 0) (Or.inr (by omega))]
    exact (hst6_cells cd).2.2.2.2.1
  · show loadWord (blMem0 cd) MO = _
    rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
      load_disj' (blmNc cd) Icell MO (W 0) (Or.inr (by omega)),
      show blmNc cd = storeWord (blmTOP cd) Ncell (W (nlimbs cd)) from rfl,
      load_disj' (blmTOP cd) Ncell MO (W (nlimbs cd)) (Or.inr (by omega)),
      show blmTOP cd = storeWord (hdrMem cd) TOP (W 0) from rfl,
      load_disj' (hdrMem cd) TOP MO (W 0) (Or.inr (by omega))]
    show loadWord (hdrMem cd) MO = _
    rw [show W (modOff cd) = W (96 + baseSize cd + exponentSize cd) from rfl]
    exact (hst6_cells cd).2.2.2.2.2.1
  · rw [show blMem0 cd = storeWord (blmNc cd) Icell (W 0) from rfl,
      load_disj' (blmNc cd) Icell Ncell (W 0) (Or.inr (by omega))]
    exact loadWord_storeWord_self (blmTOP cd) Ncell (W (nlimbs cd))

/-! ## The load loop -/

/-- The `lbLoad` section fully right-nested (so each statement faces its
continuation). -/
def bigLoadRest (l : ProgLabels) : List Asm :=
  [.label l.lbLoadDone] ++ (bpScanInit l ++ ([.label l.lbMScan] ++ bigMScanTop l))

def bigLoadTopR (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load MS) l.lbLoadDone ++
  (store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
  (store T1 (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))) ++
  (storeAt (.load T1) (.bin .or (loadAt (.load T1))
    (.bin .shl (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32))) (cdbCell MO))) ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lbLoad] ++ bigLoadRest l)))))

theorem bigLoadTop_eq (l : ProgLabels) :
    bigLoadTop l = bigLoadTopR l := by rfl

/-- The loop-exit landing: the `lbLoadDone` suffix. -/
def bigLoadExit (l : ProgLabels) : List Asm :=
  bpScanInit l ++ ([.label l.lbMScan] ++ bigMScanTop l)

theorem bigLoadRest_eq (l : ProgLabels) :
    bigLoadRest l = [.label l.lbLoadDone] ++ bigLoadExit l := by rfl

/-- The partial big-endian value loaded after `i` bytes: the `i`-byte prefix
of the modulus, left-shifted into place. -/
def partVal (cd : ByteArray) (i : Nat) : Nat :=
  wordVal (byteFrom cd.toList) (modOff cd) i * 256 ^ (modulusSize cd - i)

theorem partVal_zero (cd : ByteArray) : partVal cd 0 = 0 := by
  simp [partVal, wordVal]

/-- The state predicate carried through the `lbLoad` loop: `i` modulus bytes
spliced, everything else as at the entry state. -/
structure BLLoad (yst : EvmState) (cd : ByteArray) (i : Nat) : Prop where
  aw : yst.activeWords.toNat = 250
  env : yst.env.calldata = cd.toList
  icell : loadWord yst.memory Icell = W i
  mscell : loadWord yst.memory MS = W (modulusSize cd)
  mocell : loadWord yst.memory MO = W (modOff cd)
  bscell : loadWord yst.memory BS = W (baseSize cd)
  ecell : loadWord yst.memory ES = W (exponentSize cd)
  bocell : loadWord yst.memory BO = W 96
  eocell : loadWord yst.memory EO = W (96 + baseSize cd)
  ncell : loadWord yst.memory Ncell = W (nlimbs cd)
  rep : RepresentsY yst.memory MOD (nlimbs cd) (partVal cd i)
  midzero : ∀ a, 32 * nlimbs cd ≤ a → a < BS → yst.memory a = 0

/-- Cell-pinning at `activeWords = 250`. -/
theorem pin250 {q : Nat} {yst : EvmState}
    (haw : yst.activeWords.toNat = 250) (hq : q + 32 ≤ 8000) :
    exprOK (Expr.load q) yst := by
  show q < 2 ^ 256 ∧ q + 32 ≤ 32 * yst.activeWords.toNat
  rw [haw]
  omega

/-- One pinned `store c e` with the value computed. -/
theorem store_pin {c : Nat} {e : Expr} {v : U256} {yst : EvmState} {k : List Asm}
    (he : exprOK e yst) (hc : c < 2 ^ 256)
    (hpin : c + 32 ≤ 32 * yst.activeWords.toNat)
    (hval : evalExpr e yst = v) :
    ASteps programAsm ⟨store c e ++ k, [], yst⟩
      ⟨k, [], { yst with memory := storeWord yst.memory c v }⟩ := by
  have h := store_steps (model := localModel) (prog := programAsm) (c := c) (e := e)
    (k := k) (σ := []) he ⟨hc, hpin⟩
  rw [hval] at h
  exact h

/-- A pinned `storeAt` with the value computed. -/
private theorem storeAt_pin {addrE valE : Expr} {a v : U256} {yst : EvmState} {k : List Asm}
    (hv : exprOK valE yst) (ha : exprOK addrE yst)
    (hp : (evalExpr addrE yst).toNat + 32 ≤ 32 * yst.activeWords.toNat)
    (haddr : (evalExpr addrE yst).toNat = a.toNat) (hval : evalExpr valE yst = v) :
    ASteps programAsm ⟨storeAt addrE valE ++ k, [], yst⟩
      ⟨k, [], { yst with memory := storeWord yst.memory a.toNat v }⟩ := by
  have h := storeAt_steps (model := localModel) (prog := programAsm)
    (addrE := addrE) (valE := valE) (k := k) (σ := []) hv ha hp
  rw [haddr, hval] at h
  exact h

/-- A pinned `storeAt` over an `activeWords = 250` state, numeric pinning. -/
private theorem storeAt_pin' {addrE valE : Expr} {a v : U256} {yst : EvmState} {k : List Asm}
    (haw : yst.activeWords.toNat = 250)
    (hv : exprOK valE yst) (ha : exprOK addrE yst)
    (hpin : (evalExpr addrE yst).toNat + 32 ≤ 8000)
    (haddr : (evalExpr addrE yst).toNat = a.toNat) (hval : evalExpr valE yst = v) :
    ASteps programAsm ⟨storeAt addrE valE ++ k, [], yst⟩
      ⟨k, [], { yst with memory := storeWord yst.memory a.toNat v }⟩ := by
  have h := storeAt_steps (model := localModel) (prog := programAsm)
    (addrE := addrE) (valE := valE) (k := k) (σ := []) hv ha (by rw [haw]; omega)
  rw [haddr, hval] at h
  exact h

/-- Peeling the four loop-round stores off a disjoint load. -/
private theorem peel4 {m : Nat → UInt8} {q : Nat} {v0 v1 v2 v3 : U256} {L : Nat}
    (hI : Icell + 32 ≤ q ∨ q + 32 ≤ Icell) (hL : L + 32 ≤ q ∨ q + 32 ≤ L)
    (hT1 : T1 + 32 ≤ q ∨ q + 32 ≤ T1) (hT0 : T0 + 32 ≤ q ∨ q + 32 ≤ T0) :
    loadWord (storeWord (storeWord (storeWord (storeWord m T0 v0) T1 v1) L v2) Icell v3) q
      = loadWord m q := by
  rw [load_disj' _ _ _ _ hI, load_disj' _ _ _ _ hL, load_disj' _ _ _ _ hT1,
    load_disj' _ _ _ _ hT0]

/-- Four stores on disjoint windows (byte view). -/
private theorem peel4_out {m : Nat → UInt8} {a : Nat} {v0 v1 v2 v3 : U256} {L : Nat}
    (hI : ¬(Icell ≤ a ∧ a < Icell + 32)) (hL : ¬(L ≤ a ∧ a < L + 32))
    (hT1 : ¬(T1 ≤ a ∧ a < T1 + 32)) (hT0 : ¬(T0 ≤ a ∧ a < T0 + 32)) :
    storeWord (storeWord (storeWord (storeWord m T0 v0) T1 v1) L v2) Icell v3 a
      = m a := by
  rw [storeWord_out _ _ _ _ hI, storeWord_out _ _ _ _ hL,
    storeWord_out _ _ _ _ hT1, storeWord_out _ _ _ _ hT0]


/-- A list element in bang form equals the dependent form. -/
private theorem getBang {l : List Nat} {i : Nat} (h : i < l.length) : l[i]! = l[i] := by
  have hh : l[i]? = some l[i] := by simp [h]
  simp [hh]

/-- The `L`-th limb of `limbDigits n v` for `L < n`, as `v / radix^L % radix`. -/
private theorem limbDigitD {n v L : Nat} (hL : L < n) (hv : v < radix ^ n) :
    (limbDigits n v)[L]'(by rw [length_limbDigits hv]; omega) = v / radix ^ L % radix := by
  have hlen : (limbDigits n v).length = n := length_limbDigits hv
  have hLL : L < (limbDigits n v).length := by omega
  have hdiglen : (Nat.digits radix v).length ≤ n := by
    have h2 : (Nat.digits radix v ++
        List.replicate (n - (Nat.digits radix v).length) 0).length = n := by
      have h3 := hlen
      rw [show limbDigits n v = Nat.digits radix v ++
          List.replicate (n - (Nat.digits radix v).length) 0 from rfl] at h3
      exact h3
    rw [List.length_append, List.length_replicate] at h2
    omega
  have hdrop : (limbDigits n v).drop L = (Nat.digits radix v).drop L ++
      (List.replicate (n - (Nat.digits radix v).length) 0).drop (L - (Nat.digits radix v).length) := by
    rw [show limbDigits n v = Nat.digits radix v ++
        List.replicate (n - (Nat.digits radix v).length) 0 from rfl]
    exact List.drop_append
  have hval : v / radix ^ L = Nat.ofDigits radix ((limbDigits n v).drop L) := by
    rw [hdrop, Nat.ofDigits_append, List.drop_replicate, Nat.ofDigits_replicate_zero,
      Nat.mul_zero, Nat.add_zero, ← Nat.self_div_pow_eq_ofDigits_drop L v (Nat.succ_le_of_lt radix_gt_one)]
  have hcons : (limbDigits n v).drop L =
      (limbDigits n v)[L] :: (limbDigits n v).drop (L + 1) := List.drop_eq_getElem_cons hLL
  rw [hcons, Nat.ofDigits_cons] at hval
  have hlt : (limbDigits n v)[L] < radix := limbDigits_lt (List.getElem_mem hLL)
  rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem limbDigit {n v L : Nat} (hL : L < n) (hv : v < radix ^ n) :
    (limbDigits n v)[L]! = v / radix ^ L % radix := by
  rw [getBang (by rw [length_limbDigits hv]; omega)]
  exact limbDigitD hL hv

/-- The low `k + 1` bytes of limb `L` of a value whose bytes below position
`32 * L + k + 1` are zero, are zero. -/
private theorem limbDigit_mod_low {n v L k : Nat} (hL : L < n) (hv : v < radix ^ n)
    (hval : ∃ P : Nat, v = P * 256 ^ (32 * L + k + 1)) (hk : k < 32) :
    (limbDigits n v)[L]! % 256 ^ (k + 1) = 0 := by
  rw [getBang (by rw [length_limbDigits hv]; omega)]
  rw [limbDigitD hL hv]
  obtain ⟨P, hP⟩ := hval
  have h256p : (0 : Nat) < 256 ^ (32 * L) := Nat.pow_pos (by norm_num)
  have hpow : 256 ^ (32 * L + k + 1) = 256 ^ (32 * L) * 256 ^ (k + 1) := by
    rw [show 32 * L + k + 1 = 32 * L + (k + 1) from by omega, Nat.pow_add]
  have hdiv : v / 256 ^ (32 * L) = P * 256 ^ (k + 1) := by
    rw [hP, hpow, ← Nat.mul_assoc,
      show P * 256 ^ (32 * L) = 256 ^ (32 * L) * P from Nat.mul_comm _ _,
      Nat.mul_assoc, Nat.mul_div_cancel_left _ h256p]
  have hdvd : 256 ^ (k + 1) ∣ 256 ^ 32 :=
    Nat.pow_dvd_pow 256 (show k + 1 ≤ 32 by omega)
  have hradix : (radix : Nat) = 256 ^ 32 := by
    rw [show (radix : Nat) = 2 ^ 256 from rfl, two_pow_256_eq]
  rw [pow_radix L, hdiv, hradix, Nat.mod_mod_of_dvd _ hdvd]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left _ _)

/-! ## The preamble stores -/

/-- The `store_steps_exact` conclusion state, flattened. -/
private theorem exact_store_state {yst : EvmState} {c : Nat} {v : U256} {aw : Nat}
    (hc : c < 2 ^ 256) (haw : activeWordsAfter yst.activeWords.toNat c 32 = aw) :
    { touchMemory yst (c % 2 ^ 256) 32 with memory := storeWord yst.memory (c % 2 ^ 256) v } =
      { yst with memory := storeWord yst.memory c v, activeWords := W aw } := by
  have hcm : c % 2 ^ 256 = c := Nat.mod_eq_of_lt hc
  rw [hcm, show touchMemory yst c 32 =
      { yst with activeWords := BitVec.ofNat 256 (activeWordsAfter yst.activeWords.toNat c 32) }
      from rfl, haw]

/-- An unpinned store with exact `activeWords` growth. -/
private theorem store_step_exact' {c : Nat} {e : Expr} {v : U256} {aw : Nat}
    {yst : EvmState} {k : List Asm} (he : exprOK e yst) (hc : c < 2 ^ 256)
    (haw : activeWordsAfter yst.activeWords.toNat c 32 = aw)
    (hval : evalExpr e yst = v) :
    ASteps programAsm ⟨store c e ++ k, [], yst⟩
      ⟨k, [], { yst with memory := storeWord yst.memory c v, activeWords := W aw }⟩ := by
  have h := store_steps_exact (model := localModel) (prog := programAsm) (c := c)
    (e := e) (k := k) (σ := []) he
  rw [hval, exact_store_state hc haw] at h
  exact h

/-- The state after the `TOP` store (and after the `Ncell` store) of the
preamble. -/
def bl0top (cd : ByteArray) : EvmState :=
  { hst6 cd with memory := storeWord (hdrMem cd) TOP (W 0), activeWords := W 250 }

def bl0nc (cd : ByteArray) : EvmState :=
  { hst6 cd with memory := blmNc cd, activeWords := W 250 }

/-- The big-path preamble: from the header exit state through the three
stores to the `lbLoad` loop top. -/
theorem big_entry (cd : ByteArray) (hv : ValidInput cd) :
    ASteps programAsm ⟨bigEntryCode programLabels ++ progTail, [], hst6 cd⟩
      ⟨bigLoadTop programLabels ++ progTail, [], bl0 cd⟩ := by
  obtain ⟨-, hb, he, hm⟩ := hv
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have haw1 : (bl0top cd).activeWords.toNat = 250 := rfl
  have hMS1 : loadWord (storeWord (hdrMem cd) TOP (W 0)) MS = W (modulusSize cd) := by
    rw [load_disj' _ TOP MS (W 0) (Or.inr (by omega))]
    exact (hst6_cells cd).2.2.1
  rw [show bigEntryCode programLabels ++ progTail =
      store TOP (.imm 0) ++
      (store Ncell (.bin .div (.bin .add (.load MS) (.imm 31)) (.imm 32)) ++
      (store Icell (.imm 0) ++
      ([.label programLabels.lbLoad] ++ (bigLoadTop programLabels ++ progTail)))) from by
    simp only [bigEntryCode, bpEntry, List.append_assoc]]
  refine (store_step_exact' (c := TOP) (e := .imm 0) (v := W 0) (aw := 250)
    (yst := hst6 cd) trivial (by decide) (by rw [hst6_activeWords]; decide) rfl).trans ?_
  refine (store_pin (c := Ncell)
    (e := .bin .div (.bin .add (.load MS) (.imm 31)) (.imm 32))
    (v := W (nlimbs cd)) (yst := bl0top cd) ?_ (by decide)
    (by show Ncell + 32 ≤ 8000; decide) ?_).trans ?_
  · show binOK .div = true ∧
      (binOK .add = true ∧ exprOK (.load MS) (bl0top cd) ∧ exprOK (.imm 31) (bl0top cd)) ∧
      exprOK (.imm 32) (bl0top cd)
    exact ⟨rfl, ⟨rfl, pin250 haw1 (by omega), trivial⟩, trivial⟩
  · show (if (W 32 : U256) = 0 then (0 : U256)
        else (loadWord (storeWord (hdrMem cd) TOP (W 0)) MS + W 31) / W 32) = _
    rw [if_neg (by decide), hMS1, W_add (by omega), W_div (by omega) (by norm_num)]
    rfl
  · refine (store_pin (c := Icell) (e := .imm 0) (v := W 0) (yst := bl0nc cd)
      trivial (by decide) (by show Icell + 32 ≤ 8000; decide) rfl).trans ?_
    exact (label_steps (model := localModel)).trans (ASteps.refl _)

/-! ## The load loop round -/

/-- A multiple of `256 ^ (k+1)` below `256 ^ 32`, plus a byte at position
`k`, stays below `2 ^ 256`. -/
private theorem splice_lt {d b k : Nat} (hd : d % 256 ^ (k + 1) = 0)
    (hlt : d < 256 ^ 32) (hb : b < 256) (hk : k < 32) :
    d + b * 256 ^ k < 2 ^ 256 ∧ b * 256 ^ k < 2 ^ (8 * (k + 1)) := by
  have hpos : (0 : Nat) < 256 ^ k := Nat.pow_pos (by norm_num)
  have h1 : b * 256 ^ k < 256 ^ (k + 1) := by
    rw [Nat.pow_succ]
    have hble : b * 256 ^ k ≤ 255 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hdq : d / 256 ^ (k + 1) * 256 ^ (k + 1) = d := by
    have hz := Nat.div_add_mod d (256 ^ (k + 1))
    rw [hd, Nat.add_zero, Nat.mul_comm] at hz
    exact hz
  have hdvd : 256 ^ (k + 1) ∣ 256 ^ 32 := Nat.pow_dvd_pow 256 (by omega)
  have hmul : 256 ^ 32 / 256 ^ (k + 1) * 256 ^ (k + 1) = 256 ^ 32 := by
    have hz := Nat.div_add_mod (256 ^ 32) (256 ^ (k + 1))
    rwa [Nat.mod_eq_zero_of_dvd hdvd, Nat.add_zero, Nat.mul_comm] at hz
  have hq : d + 256 ^ (k + 1) ≤ 256 ^ 32 := by
    have hltq : d / 256 ^ (k + 1) * 256 ^ (k + 1) <
        256 ^ 32 / 256 ^ (k + 1) * 256 ^ (k + 1) := by
      rw [hdq, hmul]
      exact hlt
    have hltq2 : d / 256 ^ (k + 1) < 256 ^ 32 / 256 ^ (k + 1) :=
      Nat.lt_of_mul_lt_mul_right hltq
    have hfin : (d / 256 ^ (k + 1) + 1) * 256 ^ (k + 1) ≤
        256 ^ 32 / 256 ^ (k + 1) * 256 ^ (k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hmul] at hfin
    have hdq2 : (d / 256 ^ (k + 1) + 1) * 256 ^ (k + 1)
        = d + 256 ^ (k + 1) := by
      rw [Nat.add_mul, Nat.one_mul, hdq]
    rw [hdq2] at hfin
    exact hfin
  rw [show (2 : Nat) ^ (8 * (k + 1)) = 256 ^ (k + 1) from by
      rw [Nat.pow_mul]]
  refine ⟨?_, h1⟩
  rw [two_pow_256_eq]
  omega
/-! ## The load round -/

/-- The round recurrence for the partial value. -/
private theorem partVal_succ (cd : ByteArray) (i : Nat) (hi : i < modulusSize cd) :
    partVal cd (i + 1) = partVal cd i
      + (byteFrom cd.toList (modOff cd + i)).toNat * 256 ^ (modulusSize cd - 1 - i) := by
  show wordVal (byteFrom cd.toList) (modOff cd) (i + 1) * 256 ^ (modulusSize cd - (i + 1))
      = wordVal (byteFrom cd.toList) (modOff cd) i * 256 ^ (modulusSize cd - i)
        + (byteFrom cd.toList (modOff cd + i)).toNat * 256 ^ (modulusSize cd - 1 - i)
  rw [show modulusSize cd - (i + 1) = modulusSize cd - 1 - i from by omega, wordVal_succ]
  have hexp : 256 ^ (modulusSize cd - i) = 256 * 256 ^ (modulusSize cd - 1 - i) := by
    rw [show modulusSize cd - i = (modulusSize cd - 1 - i) + 1 from by omega, Nat.pow_succ,
      Nat.mul_comm]
  rw [hexp]
  ring

/-- The intermediate states of a load round (as cheap def applications). -/
def bl1st (yst : EvmState) (t0v : U256) : EvmState :=
  { yst with memory := storeWord yst.memory T0 t0v }

def bl2st (yst : EvmState) (t0v t1v : U256) : EvmState :=
  { yst with memory := storeWord (storeWord yst.memory T0 t0v) T1 t1v }

def bl3st (yst : EvmState) (t0v t1v : U256) (la : Nat) (v2 : U256) : EvmState :=
  { yst with memory := storeWord (storeWord (storeWord yst.memory T0 t0v) T1 t1v) la v2 }

/-- One round of the `lbLoad` loop: byte `i` of the modulus (big-endian) is
spliced into limb `(msize-1-i)/32` at byte position `(msize-1-i)%32`. -/
private theorem load_round {cd : ByteArray} {i : Nat} {yst : EvmState}
    (hv : ValidInput cd) (hi : i < modulusSize cd) (hinv : BLLoad yst cd i) :
    ∃ yst', BLLoad yst' cd (i + 1) ∧
      ASteps programAsm ⟨bigLoadTop programLabels ++ progTail, [], yst⟩
        ⟨bigLoadTop programLabels ++ progTail, [], yst'⟩ := by
  obtain ⟨-, hb, he, hm⟩ := hv
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have hms : (0 : Nat) < modulusSize cd := by omega
  have hn : nlimbs cd ≤ 32 := limbCount_le_32 (modulusSize cd) hm
  have hmsn : modulusSize cd ≤ 32 * nlimbs cd := width_le_limbs (modulusSize cd)
  have hLlt : (modulusSize cd - 1 - i) / 32 < nlimbs cd := by
    have h1 : modulusSize cd - 1 - i < nlimbs cd * 32 := by
      rw [Nat.mul_comm]; omega
    exact (Nat.div_lt_iff_lt_mul (by norm_num : (0 : Nat) < 32)).mpr h1
  have hk32 : (modulusSize cd - 1 - i) % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hdm : 32 * ((modulusSize cd - 1 - i) / 32) + (modulusSize cd - 1 - i) % 32
      = modulusSize cd - 1 - i :=
    Nat.div_add_mod (modulusSize cd - 1 - i) 32
  have hms256 : modulusSize cd < 2 ^ 256 := size_lt _ hm
  have hoff256 : modOff cd < 2 ^ 256 := by
    have : modOff cd = 96 + baseSize cd + exponentSize cd := rfl
    omega
  have hwordlt : wordVal (byteFrom cd.toList) (modOff cd) i < 256 ^ i :=
    wordVal_lt _ _ _
  have hvb : partVal cd i < radix ^ nlimbs cd := by
    have hQ : (0 : Nat) < 256 ^ (modulusSize cd - i) := Nat.pow_pos (by norm_num)
    have h1 : partVal cd i < 256 ^ i * 256 ^ (modulusSize cd - i) :=
      (Nat.mul_lt_mul_right hQ).mpr hwordlt
    rw [show 256 ^ i * 256 ^ (modulusSize cd - i) = 256 ^ (modulusSize cd) from by
      rw [← Nat.pow_add]; congr 1; omega] at h1
    rw [pow_radix]
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hmsn)
  have hdl : (limbDigits (nlimbs cd) (partVal cd i)).length = nlimbs cd :=
    length_limbDigits hvb
  have hLlen : (limbDigits (nlimbs cd) (partVal cd i)).length = nlimbs cd :=
    length_limbDigits hvb
  have hmem : (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
      ∈ limbDigits (nlimbs cd) (partVal cd i) := by
    rw [getBang (by rw [hLlen]; exact hLlt)]
    exact List.getElem_mem (by rw [hLlen]; exact hLlt)
  have hdigbang : (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
      < 2 ^ 256 := limbDigits_lt hmem
  have hdig32bang : (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
      < 256 ^ 32 := by rw [← two_pow_256_eq]; exact hdigbang
  have hval' : ∃ P : Nat, partVal cd i = P * 256 ^ (32 * ((modulusSize cd - 1 - i) / 32)
      + (modulusSize cd - 1 - i) % 32 + 1) := by
    refine ⟨wordVal (byteFrom cd.toList) (modOff cd) i, ?_⟩
    show wordVal (byteFrom cd.toList) (modOff cd) i * 256 ^ (modulusSize cd - i) = _
    rw [show modulusSize cd - i = 32 * ((modulusSize cd - 1 - i) / 32)
        + (modulusSize cd - 1 - i) % 32 + 1 from by omega]
  have hmod0 : (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
      % 256 ^ ((modulusSize cd - 1 - i) % 32 + 1) = 0 :=
    limbDigit_mod_low hLlt hvb hval' hk32
  have hlimbW : loadWord yst.memory (32 * ((modulusSize cd - 1 - i) / 32))
      = W (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_W hdigbang]
    have hylen : (yLimbs yst.memory MOD (nlimbs cd)).length = nlimbs cd :=
      length_yLimbs yst.memory MOD (nlimbs cd)
    have h1 : (yLimbs yst.memory MOD (nlimbs cd))[(modulusSize cd - 1 - i) / 32]!
        = (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! := by
      rw [show (yLimbs yst.memory MOD (nlimbs cd))
          = limbDigits (nlimbs cd) (partVal cd i) from hinv.rep.2]
    have h2 : (yLimbs yst.memory MOD (nlimbs cd))[(modulusSize cd - 1 - i) / 32]!
        = (loadWord yst.memory (MOD + 32 * ((modulusSize cd - 1 - i) / 32))).toNat := by
      simp [yLimbs, List.getElem?_range hLlt]
    rw [show 32 * ((modulusSize cd - 1 - i) / 32)
        = MOD + 32 * ((modulusSize cd - 1 - i) / 32) from by
        have hMOD : MOD = (0 : Nat) := by decide
        omega,
      ← h2, h1]
  have hb256 : (byteFrom cd.toList (modOff cd + i)).toNat < 256 :=
    (byteFrom cd.toList (modOff cd + i)).toNat_lt
  have hsp := splice_lt hmod0 hdig32bang hb256 hk32
  have hshl : (W (byteFrom cd.toList (modOff cd + i)).toNat)
        <<< (8 * ((modulusSize cd - 1 - i) % 32))
      = W ((byteFrom cd.toList (modOff cd + i)).toNat
          * 2 ^ (8 * ((modulusSize cd - 1 - i) % 32))) :=
    W_shl_full (by
      have h8 : 8 * ((modulusSize cd - 1 - i) % 32) ≤ 248 := by omega
      have h2p : (0 : Nat) < 2 ^ (8 * ((modulusSize cd - 1 - i) % 32)) :=
        Nat.pow_pos (by norm_num)
      have hlt1 : (byteFrom cd.toList (modOff cd + i)).toNat
          * 2 ^ (8 * ((modulusSize cd - 1 - i) % 32))
          < 256 * 2 ^ (8 * ((modulusSize cd - 1 - i) % 32)) :=
        (Nat.mul_lt_mul_right h2p).mpr hb256
      have hlt2 : 256 * 2 ^ (8 * ((modulusSize cd - 1 - i) % 32)) ≤ 2 ^ 256 := by
        rw [show (2 : Nat) ^ 256 = 2 ^ 8 * 2 ^ 248 from by norm_num]
        exact Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_right (by norm_num) h8)
      omega)
  have hyb : (byteFrom cd.toList (modOff cd + i)).toNat
      * 256 ^ ((modulusSize cd - 1 - i) % 32) < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hsp.1
  have hxj' : (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
      % (2 : Nat) ^ (8 * ((modulusSize cd - 1 - i) % 32 + 1)) = 0 := by
    rw [show (2 : Nat) ^ (8 * ((modulusSize cd - 1 - i) % 32 + 1))
        = 256 ^ ((modulusSize cd - 1 - i) % 32 + 1) from by
      rw [Nat.pow_mul]]
    exact hmod0
  have hor : (W (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!)
        ||| (W ((byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32)))
      = W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
          + (byteFrom cd.toList (modOff cd + i)).toNat
            * 256 ^ ((modulusSize cd - 1 - i) % 32)) :=
    W_or_add hdigbang hyb hsp.1 hsp.2 hxj'
  -- the states through the round
  have hi256 : i < 2 ^ 256 := by omega
  have hLa256 : 32 * ((modulusSize cd - 1 - i) / 32) < 2 ^ 256 := by
    have h1 : 32 * ((modulusSize cd - 1 - i) / 32) ≤ 32 * 31 := by
      have : (modulusSize cd - 1 - i) / 32 ≤ 31 := by omega
      exact Nat.mul_le_mul_left _ this
    omega
  refine ⟨{ yst with memory := storeWord (storeWord (storeWord (storeWord yst.memory
      T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))
      (32 * ((modulusSize cd - 1 - i) / 32))
      (W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32)))) Icell (W (i + 1)) }, ?_, ?_⟩
  · refine ⟨hinv.aw, hinv.env, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show loadWord (storeWord (storeWord (storeWord (storeWord yst.memory T0 _) T1 _)
        (32 * ((modulusSize cd - 1 - i) / 32)) _) Icell (W (i + 1))) Icell = _
      rw [loadWord_storeWord_self]
    · rw [peel4 (q := MS) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega))]
      exact hinv.mscell
    · rw [peel4 (q := MO) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega))]
      exact hinv.mocell
    · rw [peel4 (q := BS) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega))]
      exact hinv.bscell
    · rw [peel4 (q := ES) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega))]
      exact hinv.ecell
    · rw [peel4 (q := BO) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega))]
      exact hinv.bocell
    · rw [peel4 (q := EO) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega))]
      exact hinv.eocell
    · rw [peel4 (q := Ncell) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inr (by omega))]
      exact hinv.ncell
    · -- the representation update
      have hQ0 : (0 : Nat) < 256 ^ (modulusSize cd - 1 - i) :=
        Nat.pow_pos (by norm_num)
      have hQ1 : (0 : Nat) < 256 ^ (modulusSize cd - i) := Nat.pow_pos (by norm_num)
      have hdlt : partVal cd i < 256 ^ (modulusSize cd) := by
        have h1 : partVal cd i < 256 ^ i * 256 ^ (modulusSize cd - i) :=
          (Nat.mul_lt_mul_right hQ1).mpr hwordlt
        rw [show 256 ^ i * 256 ^ (modulusSize cd - i) = 256 ^ (modulusSize cd) from by
          rw [← Nat.pow_add]; congr 1; omega] at h1
        exact h1
      have hbyte : (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ (modulusSize cd - 1 - i) < 256 ^ (modulusSize cd - 1 - i + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (byteFrom cd.toList (modOff cd + i)).toNat (256 ^ (modulusSize cd - 1 - i))]
        exact (Nat.mul_lt_mul_left hQ0).mpr hb256
      have hdvd : 256 ^ (modulusSize cd - 1 - i + 1) ∣ partVal cd i := by
        obtain ⟨P, hP⟩ := hval'
        rw [hP, show 32 * ((modulusSize cd - 1 - i) / 32)
            + (modulusSize cd - 1 - i) % 32 + 1 = modulusSize cd - 1 - i + 1 from by
          rw [hdm]]
        exact Nat.dvd_mul_left _ _
      have hq : partVal cd i / 256 ^ (modulusSize cd - 1 - i + 1)
          * 256 ^ (modulusSize cd - 1 - i + 1) = partVal cd i := by
        have hz := Nat.div_add_mod (partVal cd i) (256 ^ (modulusSize cd - 1 - i + 1))
        rw [Nat.mod_eq_zero_of_dvd hdvd, Nat.add_zero, Nat.mul_comm] at hz
        exact hz
      have hdvd2 : 256 ^ (modulusSize cd - 1 - i + 1) ∣ 256 ^ (modulusSize cd) :=
        Nat.pow_dvd_pow 256 (by omega)
      have hmul : 256 ^ (modulusSize cd) / 256 ^ (modulusSize cd - 1 - i + 1)
          * 256 ^ (modulusSize cd - 1 - i + 1) = 256 ^ (modulusSize cd) := by
        have hz := Nat.div_add_mod (256 ^ (modulusSize cd))
          (256 ^ (modulusSize cd - 1 - i + 1))
        rw [Nat.mod_eq_zero_of_dvd hdvd2, Nat.add_zero, Nat.mul_comm] at hz
        exact hz
      have hq2 : partVal cd i / 256 ^ (modulusSize cd - 1 - i + 1)
          < 256 ^ (modulusSize cd) / 256 ^ (modulusSize cd - 1 - i + 1) := by
        have hlt2 : partVal cd i / 256 ^ (modulusSize cd - 1 - i + 1)
            * 256 ^ (modulusSize cd - 1 - i + 1)
            < 256 ^ (modulusSize cd) / 256 ^ (modulusSize cd - 1 - i + 1)
            * 256 ^ (modulusSize cd - 1 - i + 1) := by
          rw [hq, hmul]
          exact hdlt
        exact Nat.lt_of_mul_lt_mul_right hlt2
      have htop : partVal cd i + 256 ^ (modulusSize cd - 1 - i + 1)
          ≤ 256 ^ (modulusSize cd) := by
        calc partVal cd i + 256 ^ (modulusSize cd - 1 - i + 1)
            = (partVal cd i / 256 ^ (modulusSize cd - 1 - i + 1) + 1)
                * 256 ^ (modulusSize cd - 1 - i + 1) := by
              rw [Nat.add_mul, Nat.one_mul, hq]
          _ ≤ 256 ^ (modulusSize cd) / 256 ^ (modulusSize cd - 1 - i + 1)
                * 256 ^ (modulusSize cd - 1 - i + 1) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = 256 ^ (modulusSize cd) := hmul
      have hvb2 : partVal cd (i + 1) < radix ^ nlimbs cd := by
        rw [partVal_succ cd i hi, pow_radix]
        calc partVal cd i + (byteFrom cd.toList (modOff cd + i)).toNat
                * 256 ^ (modulusSize cd - 1 - i)
            < partVal cd i + 256 ^ (modulusSize cd - 1 - i + 1) :=
              Nat.add_lt_add_left hbyte _
          _ ≤ 256 ^ (modulusSize cd) := htop
          _ ≤ 256 ^ (32 * nlimbs cd) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
      have hrep : RepresentsY
          (storeWord (storeWord (storeWord (storeWord yst.memory
      T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))
      (32 * ((modulusSize cd - 1 - i) / 32))
      (W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32)))) Icell (W (i + 1)))
          MOD (nlimbs cd) (partVal cd (i + 1)) := by
        rw [RepresentsY_iff_value hvb2]
        have hylen : (yLimbs yst.memory MOD (nlimbs cd)).length = nlimbs cd :=
          length_yLimbs yst.memory MOD (nlimbs cd)
        have h1024 : 32 * nlimbs cd ≤ 1024 := by
          calc 32 * nlimbs cd ≤ 32 * 32 := Nat.mul_le_mul_left 32 hn
            _ = 1024 := by norm_num
        have hMOD : MOD = (0 : Nat) := by decide
        have hd0 : yLimbs (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
            MOD (nlimbs cd) = yLimbs yst.memory MOD (nlimbs cd) :=
          yLimbs_storeWord_disjoint (q := T0) (Or.inr (by omega))
        have hd1 : yLimbs (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
            T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) MOD (nlimbs cd)
            = yLimbs yst.memory MOD (nlimbs cd) := by
          have he1 : yLimbs (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
              T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) MOD (nlimbs cd)
              = yLimbs (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
                MOD (nlimbs cd) :=
            yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega))
          rw [he1, hd0]
        have hd2 : yLimbs (storeWord (storeWord (storeWord yst.memory
            T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))
            (32 * ((modulusSize cd - 1 - i) / 32))
            (W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
              + (byteFrom cd.toList (modOff cd + i)).toNat
                * 256 ^ ((modulusSize cd - 1 - i) % 32)))) MOD (nlimbs cd)
            = (yLimbs yst.memory MOD (nlimbs cd)).set ((modulusSize cd - 1 - i) / 32)
              ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
                + (byteFrom cd.toList (modOff cd + i)).toNat
                  * 256 ^ ((modulusSize cd - 1 - i) % 32)) := by
          have he2 := yLimbs_storeWord (storeWord (storeWord yst.memory
              T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))
            MOD (nlimbs cd) ((modulusSize cd - 1 - i) / 32) hLlt
            (W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
              + (byteFrom cd.toList (modOff cd + i)).toNat
                * 256 ^ ((modulusSize cd - 1 - i) % 32)))
          have he2' := he2
          rw [show MOD + 32 * ((modulusSize cd - 1 - i) / 32)
              = 32 * ((modulusSize cd - 1 - i) / 32) from by omega] at he2'
          rw [he2', toNat_W hsp.1, hd1]
        have hd3 : yLimbs (storeWord (storeWord (storeWord (storeWord yst.memory
            T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))
            (32 * ((modulusSize cd - 1 - i) / 32))
            (W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
              + (byteFrom cd.toList (modOff cd + i)).toNat
                * 256 ^ ((modulusSize cd - 1 - i) % 32)))) Icell (W (i + 1)))
            MOD (nlimbs cd)
            = (yLimbs yst.memory MOD (nlimbs cd)).set ((modulusSize cd - 1 - i) / 32)
              ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
                + (byteFrom cd.toList (modOff cd + i)).toNat
                  * 256 ^ ((modulusSize cd - 1 - i) % 32)) := by
          have he3 := yLimbs_storeWord_disjoint
            (mem := storeWord (storeWord (storeWord yst.memory
      T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))
      (32 * ((modulusSize cd - 1 - i) / 32))
      (W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32))))
            (base := MOD) (n := nlimbs cd) (q := Icell) (v := W (i + 1))
            (Or.inr (by omega))
          rw [he3, hd2]
        rw [hd3]
        have hval : Nat.ofDigits radix (yLimbs yst.memory MOD (nlimbs cd)) = partVal cd i :=
          value_of_RepresentsY hinv.rep
        have hsame : (yLimbs yst.memory MOD (nlimbs cd))[(modulusSize cd - 1 - i) / 32]!
            = (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! := by
          rw [show (yLimbs yst.memory MOD (nlimbs cd))
              = limbDigits (nlimbs cd) (partVal cd i) from hinv.rep.2]
        have hle : (yLimbs yst.memory MOD (nlimbs cd))[(modulusSize cd - 1 - i) / 32]!
            ≤ (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
              + (byteFrom cd.toList (modOff cd + i)).toNat
                * 256 ^ ((modulusSize cd - 1 - i) % 32) := by
          rw [hsame]; exact Nat.le_add_right _ _
        rw [ofDigits_set (i := (modulusSize cd - 1 - i) / 32) (by omega) hle radix, hval,
          hsame, Nat.add_sub_cancel_left,
          show radix ^ ((modulusSize cd - 1 - i) / 32)
            = 256 ^ (32 * ((modulusSize cd - 1 - i) / 32)) from pow_radix _,
          show 256 ^ (32 * ((modulusSize cd - 1 - i) / 32))
              * ((byteFrom cd.toList (modOff cd + i)).toNat
                * 256 ^ ((modulusSize cd - 1 - i) % 32))
            = (byteFrom cd.toList (modOff cd + i)).toNat
                * 256 ^ (32 * ((modulusSize cd - 1 - i) / 32)
                  + (modulusSize cd - 1 - i) % 32) from by
            rw [Nat.pow_add]
            ring,
          show 32 * ((modulusSize cd - 1 - i) / 32)
            + (modulusSize cd - 1 - i) % 32 = modulusSize cd - 1 - i from hdm,
          partVal_succ cd i hi]
      exact hrep
    · intro a ha1 ha2
      show storeWord (storeWord (storeWord (storeWord yst.memory T0 _) T1 _)
        (32 * ((modulusSize cd - 1 - i) / 32)) _) Icell (W (i + 1)) a = _
      rw [storeWord_out _ _ _ _ (by omega), storeWord_out _ _ _ _ (by omega),
        storeWord_out _ _ _ _ (by omega), storeWord_out _ _ _ _ (by omega)]
      exact hinv.midzero a ha1 ha2

  -- the execution
  rw [show bigLoadTop programLabels ++ progTail =
      jumpUnlessLt (.load Icell) (.load MS) programLabels.lbLoadDone ++
      (store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
      (store T1 (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))) ++
      (storeAt (.load T1) (.bin .or (loadAt (.load T1))
        (.bin .shl (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32))) (cdbCell MO))) ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.jump programLabels.lbLoad] ++ (bigLoadRest programLabels ++ progTail)))))) from by
    rw [bigLoadTop_eq]
    simp only [bigLoadTopR, List.append_assoc]]
  have hawS : ∀ m : Nat → UInt8,
      ({ yst with memory := m } : EvmState).activeWords.toNat = 250 := by
    intro m
    exact hinv.aw
  have hT0v1 : loadWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T0
      = W (modulusSize cd - 1 - i) := loadWord_storeWord_self _ _ _
  have hT1v2 : loadWord (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
      T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) T1
      = W (32 * ((modulusSize cd - 1 - i) / 32)) := loadWord_storeWord_self _ _ _
  have hLa2 : loadWord (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
      T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) (32 * ((modulusSize cd - 1 - i) / 32))
      = W (limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! := by
    rw [load_disj' _ T1 _ (W (32 * ((modulusSize cd - 1 - i) / 32)))
        (Or.inr (by omega)),
      load_disj' _ T0 _ (W (modulusSize cd - 1 - i)) (Or.inr (by omega))]
    exact hlimbW
  have hT0v2 : loadWord (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
      T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) T0
      = W (modulusSize cd - 1 - i) := by
    rw [load_disj' _ T1 _ (W (32 * ((modulusSize cd - 1 - i) / 32)))
        (Or.inr (by omega))]
    exact hT0v1
  have hMOv2 : loadWord (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
      T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) MO = W (modOff cd) := by
    rw [load_disj' _ T1 _ (W (32 * ((modulusSize cd - 1 - i) / 32)))
        (Or.inr (by omega)),
      load_disj' _ T0 _ (W (modulusSize cd - 1 - i)) (Or.inr (by omega))]
    exact hinv.mocell
  have hIcv2 : loadWord (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
      T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) Icell = W i := by
    rw [load_disj' _ T1 _ (W (32 * ((modulusSize cd - 1 - i) / 32)))
        (Or.inr (by omega)),
      load_disj' _ T0 _ (W (modulusSize cd - 1 - i)) (Or.inr (by omega))]
    exact hinv.icell
  have h2p8 : (2 : Nat) ^ (8 * ((modulusSize cd - 1 - i) % 32))
      = 256 ^ ((modulusSize cd - 1 - i) % 32) := by
    rw [Nat.pow_mul]
  have haw0 := hinv.aw
  have hpinT0 : T0 + 32 ≤ 32 * yst.activeWords.toNat := by omega
  refine (jumpUnlessLt_fall (model := localModel) (prog := programAsm)
    (e₁ := .load Icell) (e₂ := .load MS) (pin250 hinv.aw (by omega))
    (pin250 hinv.aw (by omega)) ?_).trans ?_
  · show (loadWord yst.memory Icell).ult (loadWord yst.memory MS)
    rw [hinv.icell, hinv.mscell]
    exact W_ult (by omega) hms256 hi
  refine (store_pin (c := T0) (e := .bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell))
    (v := W (modulusSize cd - 1 - i)) (yst := yst) ?_ (by decide)
    hpinT0 ?_).trans ?_
  · show binOK .sub = true ∧
      (binOK .sub = true ∧ exprOK (.load MS) yst ∧ exprOK (.imm 1) yst) ∧
      exprOK (.load Icell) yst
    exact ⟨rfl, ⟨rfl, pin250 hinv.aw (by omega), trivial⟩, pin250 hinv.aw (by omega)⟩
  · show (loadWord yst.memory MS - W 1) - loadWord yst.memory Icell = _
    rw [hinv.mscell, hinv.icell, W_sub (by omega) hms256, W_sub (by omega) (by omega)]
  refine (store_pin (c := T1) (e := .bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))
    (v := W (32 * ((modulusSize cd - 1 - i) / 32))) (yst := bl1st yst (W (modulusSize cd - 1 - i)))
    ?_ (by decide) (by
      simp only [bl1st]
      rw [hawS (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))]
      decide) ?_).trans ?_
  · show binOK .mul = true ∧ exprOK (.imm 32) _ ∧
      (binOK .div = true ∧ exprOK (.load T0) _ ∧ exprOK (.imm 32) _)
    exact ⟨rfl, trivial, ⟨rfl,
      pin250 (hawS (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))) (by omega),
      trivial⟩⟩
  · show W 32 * (if (W 32 : U256) = 0 then (0 : U256)
        else loadWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T0 / W 32) = _
    rw [if_neg (by decide), hT0v1, W_div (by omega) (by norm_num), W_mul]
  have haddr2 : evalExpr (Expr.load T1) (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))))
      = W (32 * ((modulusSize cd - 1 - i) / 32)) := hT1v2
  have haddrMO : (evalExpr (.bin .add (.load MO) (.load Icell)) (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))))).toNat
      = modOff cd + i := by
    show (loadWord (bl2st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32)))).memory MO
        + loadWord (bl2st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32)))).memory Icell).toNat = _
    rw [show (bl2st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32)))).memory
        = storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
          T1 (W (32 * ((modulusSize cd - 1 - i) / 32))) from rfl,
      hMOv2, hIcv2, W_add (by
        show modOff cd + i < 2 ^ 256
        have h1 : modOff cd = 96 + baseSize cd + exponentSize cd := rfl
        omega)]
    exact toNat_W (by
      have h1 : modOff cd = 96 + baseSize cd + exponentSize cd := rfl
      omega)
  have hval2 : evalExpr (.bin .or (loadAt (.load T1))
      (.bin .shl (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32))) (cdbCell MO))) (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))))
      = W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32)) := by
    show (loadWord (bl2st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32)))).memory
        (evalExpr (Expr.load T1) (bl2st yst (W (modulusSize cd - 1 - i))
          (W (32 * ((modulusSize cd - 1 - i) / 32))))).toNat)
        ||| (evalExpr (cdbCell MO) (bl2st yst (W (modulusSize cd - 1 - i))
          (W (32 * ((modulusSize cd - 1 - i) / 32))))
          <<< (W 8 * (if (W 32 : U256) = 0 then (0 : U256)
            else loadWord (bl2st yst (W (modulusSize cd - 1 - i))
              (W (32 * ((modulusSize cd - 1 - i) / 32)))).memory T0 % (W 32))).toNat) = _
    rw [haddr2, toNat_W hLa256,
      show (bl2st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32)))).memory
        = storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
          T1 (W (32 * ((modulusSize cd - 1 - i) / 32))) from rfl,
      hLa2,
      show evalExpr (cdbCell MO) (bl2st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32))))
        = evalExpr (Expr.cdb (.bin .add (.load MO) (.load Icell))) (bl2st yst
        (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))) from rfl,
      evalExpr_cdb haddrMO,
      show (bl2st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32)))).env.calldata = cd.toList from hinv.env,
      hT0v2, if_neg (by decide),
      W_mod (by omega) (by norm_num), W_mul,
      toNat_W (by omega : 8 * ((modulusSize cd - 1 - i) % 32) < 2 ^ 256), hshl, h2p8]
    exact hor

  refine (storeAt_pin' (addrE := .load T1)
    (k := store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.jump programLabels.lbLoad] ++
      (bigLoadRest programLabels ++ progTail)))
    (valE := .bin .or (loadAt (.load T1))
      (.bin .shl (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32))) (cdbCell MO)))
    (a := W (32 * ((modulusSize cd - 1 - i) / 32))) (yst := bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))))
    (hawS (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
      T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))))
    ?_ ?_ (by rw [haddr2, toNat_W hLa256]; omega)
    (by rw [haddr2, toNat_W hLa256]) hval2).trans ?_
  · simp only [exprOK]
    refine ⟨rfl, ⟨?_, ⟨by decide, ?_⟩⟩, rfl, ⟨rfl, trivial, ⟨rfl, ?_, trivial⟩⟩, ?_⟩
    · show (evalExpr (Expr.load T1) (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))))).toNat + 32
          ≤ 32 * (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))).activeWords.toNat
      rw [haddr2, toNat_W hLa256, show (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))).activeWords.toNat = 250 from hawS (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))]
      have h1024 : 32 * nlimbs cd ≤ 1024 := by
        calc 32 * nlimbs cd ≤ 32 * 32 := Nat.mul_le_mul_left 32 hn
          _ = 1024 := by norm_num
      omega
    · rw [show (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))).activeWords.toNat = 250 from hawS (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))]
      decide
    · exact pin250 (hawS (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))) (by omega)
    · show binOK .add = true ∧ exprOK (.load MO) (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))) ∧ exprOK (.load Icell) (bl2st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))))
      exact ⟨rfl, pin250 (hawS (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))) (by omega), pin250 (hawS (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))) (by omega)⟩
  · exact pin250 (hawS (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))))
      (by show T1 + 32 ≤ 8000; decide)
  have hIc3 : loadWord (bl3st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))) (32 * ((modulusSize cd - 1 - i) / 32)) W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! + (byteFrom cd.toList (modOff cd + i)).toNat * 256 ^ ((modulusSize cd - 1 - i) % 32))).memory Icell = W i := by
    rw [show (bl3st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32))) (32 * ((modulusSize cd - 1 - i) / 32)) W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! + (byteFrom cd.toList (modOff cd + i)).toNat * 256 ^ ((modulusSize cd - 1 - i) % 32))).memory = storeWord (storeWord (storeWord yst.memory
      T0 (W (modulusSize cd - 1 - i))) T1 (W (32 * ((modulusSize cd - 1 - i) / 32))))
      (32 * ((modulusSize cd - 1 - i) / 32)) W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! + (byteFrom cd.toList (modOff cd + i)).toNat * 256 ^ ((modulusSize cd - 1 - i) % 32)) from rfl,
      load_disj' _ (32 * ((modulusSize cd - 1 - i) / 32)) Icell W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]! + (byteFrom cd.toList (modOff cd + i)).toNat * 256 ^ ((modulusSize cd - 1 - i) % 32))
        (Or.inl (by omega)),
      load_disj' _ T1 Icell (W (32 * ((modulusSize cd - 1 - i) / 32))) (Or.inr (by omega)),
      load_disj' _ T0 Icell (W (modulusSize cd - 1 - i)) (Or.inr (by omega))]
    exact hinv.icell
  have heIc : exprOK (.bin .add (.load Icell) (.imm 1))
      (bl3st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))
      (32 * ((modulusSize cd - 1 - i) / 32))
      W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32))) := by
    show binOK .add = true ∧ _
    exact ⟨rfl, pin250
      (hawS (storeWord (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
        T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) (32 * ((modulusSize cd - 1 - i) / 32))
        W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
          + (byteFrom cd.toList (modOff cd + i)).toNat
            * 256 ^ ((modulusSize cd - 1 - i) % 32))))
      (by show Icell + 32 ≤ 8000; decide), trivial⟩
  have hvalIc : evalExpr (.bin .add (.load Icell) (.imm 1))
      (bl3st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))
      (32 * ((modulusSize cd - 1 - i) / 32))
      W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32))) = W (i + 1) := by
    show evalBin .add
      (loadWord (bl3st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32))) (32 * ((modulusSize cd - 1 - i) / 32))
        W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
          + (byteFrom cd.toList (modOff cd + i)).toNat
            * 256 ^ ((modulusSize cd - 1 - i) % 32))).memory Icell) (W 1) = _
    rw [hIc3, show evalBin .add (W i) (W 1) = W i + W 1 from rfl, W_add (by omega)]
  have hpin3 : Icell + 32 ≤ 32 * (bl3st yst (W (modulusSize cd - 1 - i))
      (W (32 * ((modulusSize cd - 1 - i) / 32))) (32 * ((modulusSize cd - 1 - i) / 32))
      W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32))).activeWords.toNat := by
    rw [show (bl3st yst (W (modulusSize cd - 1 - i))
        (W (32 * ((modulusSize cd - 1 - i) / 32))) (32 * ((modulusSize cd - 1 - i) / 32))
        W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32))).activeWords.toNat = 250
      from hawS (storeWord (storeWord (storeWord yst.memory T0 (W (modulusSize cd - 1 - i)))
        T1 (W (32 * ((modulusSize cd - 1 - i) / 32)))) (32 * ((modulusSize cd - 1 - i) / 32))
        W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32)))]
    show Icell + 32 ≤ 8000
    decide

  rw [toNat_W hLa256]
  exact ((store_pin (c := Icell) (e := .bin .add (.load Icell) (.imm 1))
    (k := [.jump programLabels.lbLoad] ++ (bigLoadRest programLabels ++ progTail))
    (v := W (i + 1))
    (yst := bl3st yst (W (modulusSize cd - 1 - i)) (W (32 * ((modulusSize cd - 1 - i) / 32)))
      (32 * ((modulusSize cd - 1 - i) / 32))
      W ((limbDigits (nlimbs cd) (partVal cd i))[(modulusSize cd - 1 - i) / 32]!
        + (byteFrom cd.toList (modOff cd + i)).toNat
          * 256 ^ ((modulusSize cd - 1 - i) % 32)))
    heIc (by decide) hpin3 hvalIc)).trans
    (jump_steps (model := localModel) findLbLoad)
/-! ## The load loop and the zero-scan -/

/-- The `lbLoad` loop: from the entry state, `msize` rounds leave the MOD
region representing the modulus `bytesToNatPadded cd modOff msize`. -/
theorem big_load_loop (cd : ByteArray) (hv : ValidInput cd)
    (hgt : 32 < modulusSize cd) :
    ∃ yst', BLLoad yst' cd (modulusSize cd) ∧
      ASteps programAsm ⟨bigLoadTop programLabels ++ progTail, [], bl0 cd⟩
        ⟨bigLoadExit programLabels ++ progTail, [], yst'⟩ := by
  have hv2 := hv
  obtain ⟨-, hb, he, hm⟩ := hv
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have hms : (0 : Nat) < modulusSize cd := by omega
  have hic0 : loadWord (bl0 cd).memory Icell = W 0 := by
    show loadWord (storeWord (blmNc cd) Icell (W 0)) Icell = _
    exact loadWord_storeWord_self _ _ _
  have hbn : BLLoad (bl0 cd) cd 0 := by
    refine ⟨rfl, rfl, hic0, (bl0_cells cd).2.2.1, (bl0_cells cd).2.2.2.2.2.1,
      (bl0_cells cd).1, (bl0_cells cd).2.1, (bl0_cells cd).2.2.2.1,
      (bl0_cells cd).2.2.2.2.1, (bl0_cells cd).2.2.2.2.2.2, ?_, ?_⟩
    · rw [show partVal cd 0 = 0 from partVal_zero cd]
      exact bl0_mod_zero cd hv2
    · intro a ha1 ha2
      exact bl0_zero cd a ha2
  refine loop_counted (model := localModel)
    (prog := programAsm) (top := bigLoadTop programLabels ++ progTail)
    (σ := ([] : List AVal)) (c' := bigLoadExit programLabels ++ progTail)
    (Inv := fun yst r => r ≤ modulusSize cd ∧ BLLoad yst cd (modulusSize cd - r))
    (P := fun yst => BLLoad yst cd (modulusSize cd)) ?_ ?_ (n := modulusSize cd)
    (by refine ⟨le_refl _, ?_⟩; rw [Nat.sub_self]; exact hbn)
  · intro r yst hr ⟨hrle, hinv⟩
    obtain ⟨yst2, hinv2, hst⟩ := load_round hv2 (Nat.sub_lt hms hr) hinv
    refine Or.inl ⟨yst2, ⟨by omega, ?_⟩, hst⟩
    have hshift : modulusSize cd - r + 1 = modulusSize cd - (r - 1) := by omega
    rw [hshift] at hinv2
    exact hinv2
  · intro yst ⟨hr0, hinv⟩
    have hexit : ¬ (loadWord yst.memory Icell).ult (loadWord yst.memory MS) := by
      rw [hinv.icell, hinv.mscell]
      exact W_nult (by omega) (size_lt _ hm) (by omega)
    exact ⟨hinv, jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load MS) (pin250 hinv.aw (by omega))
      (pin250 hinv.aw (by omega)) hexit findLbLoadDone⟩

/-! ## The zero-scan loop -/

/-- The modulus's limb digits, as the `lbLoad` loop leaves them. -/
def mdigits (cd : ByteArray) : List Nat :=
  limbDigits (nlimbs cd) (partVal cd (modulusSize cd))

/-- Word-level OR of the first `j` limbs (0-based, little-endian). -/
def scanWor (l : List Nat) : Nat → U256
  | 0 => 0
  | j + 1 => scanWor l j ||| W (l[j]!)

/-- Reading a limb through `yLimbs`, in bang form. -/
theorem yLimb_get {mem : Nat → UInt8} {base n i : Nat} (hi : i < n) :
    (yLimbs mem base n)[i]! = (loadWord mem (base + 32 * i)).toNat := by
  show ((List.range n).map (fun i => (loadWord mem (base + 32 * i)).toNat))[i]! = _
  rw [getBang (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]

/-- The scan state at limb index `j`: `T0` holds the OR of limbs `0..j-1`. -/
structure BMScan (yst : EvmState) (cd : ByteArray) (j : Nat) : Prop where
  aw : yst.activeWords.toNat = 250
  env : yst.env.calldata = cd.toList
  icell : loadWord yst.memory Icell = W j
  ncell : loadWord yst.memory Ncell = W (nlimbs cd)
  t0cell : loadWord yst.memory T0 = scanWor (mdigits cd) j
  mscell : loadWord yst.memory MS = W (modulusSize cd)
  mocell : loadWord yst.memory MO = W (modOff cd)
  bscell : loadWord yst.memory BS = W (baseSize cd)
  ecell : loadWord yst.memory ES = W (exponentSize cd)
  bocell : loadWord yst.memory BO = W 96
  eocell : loadWord yst.memory EO = W (96 + baseSize cd)
  rep : RepresentsY yst.memory MOD (nlimbs cd) (partVal cd (modulusSize cd))
  midzero : ∀ a, 32 * nlimbs cd ≤ a → a < BS → yst.memory a = 0

/-- Round states: after the `T0` OR store, then after the `Icell` bump. -/
def msT0 (yst : EvmState) (v : U256) : EvmState :=
  { yst with memory := storeWord yst.memory T0 v }

def msScan0 (yst : EvmState) : EvmState :=
  { msT0 yst (W 0) with memory := storeWord (msT0 yst (W 0)).memory Icell (W 0) }

def msScanJ (yst : EvmState) (v : U256) (j : Nat) : EvmState :=
  { msT0 yst v with memory := storeWord (msT0 yst v).memory Icell (W (j + 1)) }

/-- The scan preamble: two zero stores carry a load-exit state to scan entry. -/
theorem big_scan_init {cd : ByteArray} {yst : EvmState} (hv : ValidInput cd)
    (hinv : BLLoad yst cd (modulusSize cd)) :
    ∃ yst', BMScan yst' cd 0 ∧
      ASteps programAsm ⟨bigLoadExit programLabels ++ progTail, [], yst⟩
        ⟨bigMScanTop programLabels ++ progTail, [], yst'⟩ := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have hMODv : MOD = 0 := rfl
  have hn32 : nlimbs cd ≤ 32 :=
    limbCount_le_32 _ (by obtain ⟨-, -, hm⟩ := hv; omega)
  have haw : yst.activeWords.toNat = 250 := hinv.aw
  have hs1 := store_pin (c := T0) (e := .imm 0)
    (k := store Icell (.imm 0) ++ ([.label programLabels.lbMScan] ++
      (bigMScanTop programLabels ++ progTail)))
    (v := W 0) (yst := yst) (by trivial) (by decide)
    (by rw [haw]; show T0 + 32 ≤ 32 * 250; omega) (by rfl)
  have haw1 : (msT0 yst (W 0)).activeWords.toNat = 250 := haw
  have hs2 := store_pin (c := Icell) (e := .imm 0)
    (k := [.label programLabels.lbMScan] ++
      (bigMScanTop programLabels ++ progTail))
    (v := W 0) (yst := msT0 yst (W 0)) (by trivial) (by decide)
    (by rw [haw1]; show Icell + 32 ≤ 32 * 250; omega) (by rfl)
  refine ⟨msScan0 yst, ?_, ?_⟩
  · refine ⟨haw, hinv.env, ?_, hinv.ncell, ?_, hinv.mscell, hinv.mocell, hinv.bscell,
      hinv.ecell, hinv.bocell, hinv.eocell, ?_, ?_⟩
    · show loadWord (msScan0 yst).memory Icell = W 0
      rw [show (msScan0 yst).memory = storeWord (msT0 yst (W 0)).memory Icell (W 0) from rfl,
        loadWord_storeWord_self]
    · show loadWord (msScan0 yst).memory T0 = scanWor (mdigits cd) 0
      rw [show (msScan0 yst).memory = storeWord (msT0 yst (W 0)).memory Icell (W 0) from rfl,
        load_disj' _ _ _ _ (Or.inl (by omega))]
      exact (loadWord_storeWord_self _ _ _).trans rfl
    · show RepresentsY (msScan0 yst).memory MOD (nlimbs cd) (partVal cd (modulusSize cd))
      rw [show (msScan0 yst).memory = storeWord (msT0 yst (W 0)).memory Icell (W 0) from rfl]
      refine RepresentsY_storeWord_disjoint ?_ (by omega)
      show RepresentsY (msT0 yst (W 0)).memory MOD (nlimbs cd) _
      rw [show (msT0 yst (W 0)).memory = storeWord yst.memory T0 (W 0) from rfl]
      exact RepresentsY_storeWord_disjoint hinv.rep (by omega)
    · intro a ha1 ha2
      show (msScan0 yst).memory a = 0
      rw [show (msScan0 yst).memory = storeWord (msT0 yst (W 0)).memory Icell (W 0) from rfl,
        storeWord_out _ _ _ _ (by omega : ¬(Icell ≤ a ∧ a < Icell + 32)),
        show (msT0 yst (W 0)).memory = storeWord yst.memory T0 (W 0) from rfl,
        storeWord_out _ _ _ _ (by omega : ¬(T0 ≤ a ∧ a < T0 + 32))]
      exact hinv.midzero a ha1 ha2
  · rw [show bigLoadExit programLabels ++ progTail =
        store T0 (.imm 0) ++ (store Icell (.imm 0) ++
          ([.label programLabels.lbMScan] ++
            (bigMScanTop programLabels ++ progTail))) from by
        rw [bigLoadExit,
          show bpScanInit programLabels =
            store T0 (.imm 0) ++ store Icell (.imm 0) from rfl]
        simp only [List.append_assoc]]
    exact (hs1.trans hs2).trans
      (label_steps (model := localModel) (k := bigMScanTop programLabels ++
        progTail) (σ := ([] : List AVal)) (yst := msScan0 yst))

/-- The value written to `T0` in scan round `j`. -/
def scanVal (cd : ByteArray) (j : Nat) : U256 :=
  scanWor (mdigits cd) j ||| W (partVal cd (modulusSize cd) / radix ^ j % radix)

/-- The limb-word bridge for the scan round. -/
private theorem mscan_digit {cd : ByteArray} {yst : EvmState} (_hv : ValidInput cd)
    {j : Nat} (hj : j < nlimbs cd) (hinv : BMScan yst cd j) :
    (mdigits cd)[j]! = partVal cd (modulusSize cd) / radix ^ j % radix ∧
      (loadWord yst.memory (MOD + 32 * j)).toNat =
        partVal cd (modulusSize cd) / radix ^ j % radix ∧
      (loadWord yst.memory (MOD + 32 * j)) =
        W (partVal cd (modulusSize cd) / radix ^ j % radix) ∧
      partVal cd (modulusSize cd) / radix ^ j % radix < 2 ^ 256 := by
  have h1 : (yLimbs yst.memory MOD (nlimbs cd))[j]!
      = (limbDigits (nlimbs cd) (partVal cd (modulusSize cd)))[j]! := by
    rw [hinv.rep.2]
  have h2 := limbDigit (n := nlimbs cd) (v := partVal cd (modulusSize cd))
    (L := j) hj (hinv.rep.1)
  have h3 := (yLimb_get hj).symm.trans (h1.trans h2)
  refine ⟨?_, h3, ?_, ?_⟩
  · show (limbDigits (nlimbs cd) (partVal cd (modulusSize cd)))[j]! = _
    exact h2
  · apply BitVec.eq_of_toNat_eq
    rw [h3]
    exact (toNat_W (Nat.mod_lt _ radix_pos)).symm
  · exact Nat.mod_lt _ radix_pos

set_option maxHeartbeats 16000000 in
/-- The scan round's steps. -/
private theorem mscan_steps {cd : ByteArray} {yst : EvmState} (hv : ValidInput cd)
    {j : Nat} (hj : j < nlimbs cd) (hinv : BMScan yst cd j) :
    ASteps programAsm ⟨bigMScanTop programLabels ++ progTail, [], yst⟩
      ⟨bigMScanTop programLabels ++ progTail, [],
        msScanJ yst (scanVal cd j) j⟩ := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have haw : yst.activeWords.toNat = 250 := hinv.aw
  have hn32 : nlimbs cd ≤ 32 :=
    limbCount_le_32 _ (by obtain ⟨-, -, hm⟩ := hv; omega)
  have hn : nlimbs cd < 2 ^ 256 := Nat.lt_of_le_of_lt hn32 (by norm_num)
  have hjw : j < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.le_of_lt hj) hn
  have h32j : 32 * j < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 32 (by omega))
      (by norm_num : (32 : Nat) * 31 < 2 ^ 256)
  obtain ⟨-, hdigit, hlimbM, -⟩ := mscan_digit hv hj hinv
  have hmodj : MOD + 32 * j = 32 * j := Nat.zero_add _
  rw [hmodj] at hdigit hlimbM
  have hlimbW := hlimbM
  -- the OR value
  have hval : evalExpr (.bin .or (.load T0)
        (.mload (.bin .mul (.imm 32) (.load Icell)))) yst = scanVal cd j := by
    show evalBin .or (loadWord yst.memory T0)
      (loadWord yst.memory (evalExpr (.bin .mul (.imm 32) (.load Icell)) yst).toNat) = _
    rw [hinv.t0cell]
    have haddr : evalExpr (.bin .mul (.imm 32) (.load Icell)) yst = W (32 * j) := by
      show evalBin .mul (W 32) (loadWord yst.memory Icell) = _
      rw [hinv.icell]
      exact W_mul 32 j
    rw [haddr, toNat_W h32j, hlimbW]
    rfl
  -- exprOK side conditions
  have heIc : exprOK (.load Icell) yst := pin250 haw (by omega)
  have heMul : exprOK (.bin .mul (.imm 32) (.load Icell)) yst := by
    show binOK .mul = true ∧ exprOK (.imm 32) yst ∧ exprOK (.load Icell) yst
    exact ⟨by trivial, by trivial, heIc⟩
  have heOr : exprOK (.bin .or (.load T0)
      (.mload (.bin .mul (.imm 32) (.load Icell)))) yst := by
    show binOK .or = true ∧ exprOK (.load T0) yst ∧
      exprOK (Expr.mload (.bin .mul (.imm 32) (.load Icell))) yst
    refine ⟨by trivial, pin250 haw (by omega), ?_⟩
    show (evalExpr (.bin .mul (.imm 32) (.load Icell)) yst).toNat + 32
        ≤ 32 * yst.activeWords.toNat ∧
      exprOK (.bin .mul (.imm 32) (.load Icell)) yst
    have haddr : evalExpr (.bin .mul (.imm 32) (.load Icell)) yst = W (32 * j) := by
      show evalBin .mul (W 32) (loadWord yst.memory Icell) = _
      rw [hinv.icell]
      exact W_mul 32 j
    rw [haw, haddr, toNat_W h32j]
    exact ⟨by omega, heMul⟩
  -- the guard falls through
  have hltb : (evalExpr (.load Icell) yst).ult (evalExpr (.load Ncell) yst) := by
    show (loadWord yst.memory Icell).ult (loadWord yst.memory Ncell) = true
    rw [hinv.icell, hinv.ncell]
    exact W_ult hjw hn (by omega)
  have hfall := jumpUnlessLt_fall (model := localModel) (prog := programAsm)
    (l := programLabels.lbMScanDone) (e₁ := .load Icell) (e₂ := .load Ncell)
    (k := store T0 (.bin .or (.load T0)
        (.mload (.bin .mul (.imm 32) (.load Icell)))) ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++ ([.jump programLabels.lbMScan] ++
        (bpMScanDone programLabels ++ (secTailSer programLabels ++ progTail)))))
    (σ := ([] : List AVal)) heIc (pin250 haw (by omega)) hltb
  -- the T0 OR store
  have hs1 := store_pin (c := T0) (e := .bin .or (.load T0)
      (.mload (.bin .mul (.imm 32) (.load Icell))))
    (k := store Icell (.bin .add (.load Icell) (.imm 1)) ++ ([.jump programLabels.lbMScan] ++
      (bpMScanDone programLabels ++ (secTailSer programLabels ++ progTail))))
    (v := scanVal cd j) (yst := yst)
    heOr (by decide) (by rw [haw]; show T0 + 32 ≤ 32 * 250; omega) hval
  have haw1 : (msT0 yst (scanVal cd j)).activeWords.toNat = 250 := haw
  have hic1 : loadWord (msT0 yst (scanVal cd j)).memory Icell = W j := by
    rw [show (msT0 yst (scanVal cd j)).memory = storeWord yst.memory T0 (scanVal cd j) from rfl]
    exact (load_disj' yst.memory T0 Icell (scanVal cd j) (Or.inr (by omega))).trans
      hinv.icell
  -- the Icell bump
  have hvalI : evalExpr (.bin .add (.load Icell) (.imm 1)) (msT0 yst (scanVal cd j))
      = W (j + 1) := by
    show loadWord (msT0 yst (scanVal cd j)).memory Icell + W 1 = _
    rw [hic1]
    exact W_add (by omega)
  have heI2 : exprOK (.bin .add (.load Icell) (.imm 1)) (msT0 yst (scanVal cd j)) := by
    show binOK .add = true ∧ exprOK (.load Icell) (msT0 yst (scanVal cd j)) ∧
      exprOK (.imm 1) (msT0 yst (scanVal cd j))
    exact ⟨by trivial, pin250 haw1 (by omega), by trivial⟩
  have hs2 := store_pin (c := Icell) (e := .bin .add (.load Icell) (.imm 1))
    (k := [.jump programLabels.lbMScan] ++
      (bpMScanDone programLabels ++ (secTailSer programLabels ++ progTail)))
    (v := W (j + 1)) (yst := msT0 yst (scanVal cd j))
    heI2
    (by decide) (by rw [haw1]; show Icell + 32 ≤ 32 * 250; omega) hvalI
  -- the back-jump
  have hjmp : ASteps programAsm ⟨[.jump programLabels.lbMScan] ++
      (bpMScanDone programLabels ++ (secTailSer programLabels ++ progTail)),
      ([] : List AVal), msScanJ yst (scanVal cd j) j⟩
      ⟨bigMScanTop programLabels ++ progTail, [],
        msScanJ yst (scanVal cd j) j⟩ :=
    jump_steps (model := localModel) (σ := ([] : List AVal)) findLbMScan
  rw [show bigMScanTop programLabels ++ progTail =
    bpMScan programLabels ++ (bpMScanDone programLabels ++
      (secTailSer programLabels ++ progTail)) from by
      rw [bigMScanTop]; simp only [List.append_assoc]]
  rw [show bpMScan programLabels = jumpUnlessLt (.load Icell) (.load Ncell)
      programLabels.lbMScanDone ++ (store T0 (.bin .or (.load T0)
        (.mload (.bin .mul (.imm 32) (.load Icell)))) ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lbMScan])) from rfl]
  exact ((hfall.trans hs1).trans hs2).trans hjmp

set_option maxHeartbeats 16000000 in
/-- The scan invariant survives one round. -/
private theorem mscan_reinv {cd : ByteArray} {yst : EvmState} (hv : ValidInput cd)
    {j : Nat}
    (hinv : BMScan yst cd j)
    (hd : (mdigits cd)[j]! = partVal cd (modulusSize cd) / radix ^ j % radix) :
    BMScan (msScanJ yst (scanVal cd j) j) cd (j + 1) := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, hNc, hIc, hJc, hT0p, hT1p, hWc, hI2c⟩ := cells_num
  have hMODv : MOD = 0 := rfl
  have hn32 : nlimbs cd ≤ 32 :=
    limbCount_le_32 _ (by obtain ⟨-, -, hm⟩ := hv; omega)
  have haw : yst.activeWords.toNat = 250 := hinv.aw
  refine ⟨haw, hinv.env, loadWord_storeWord_self _ _ _, hinv.ncell, ?_, hinv.mscell,
    hinv.mocell, hinv.bscell, hinv.ecell, hinv.bocell, hinv.eocell, ?_, ?_⟩
  · show loadWord (msScanJ yst (scanVal cd j) j).memory T0 = scanWor (mdigits cd) (j + 1)
    rw [show (msScanJ yst (scanVal cd j) j).memory =
        storeWord (msT0 yst (scanVal cd j)).memory Icell (W (j + 1)) from rfl,
      load_disj' _ _ _ _ (Or.inl (by omega)),
      show (msT0 yst (scanVal cd j)).memory =
        storeWord yst.memory T0 (scanVal cd j) from rfl,
      loadWord_storeWord_self]
    show scanVal cd j = scanWor (mdigits cd) (j + 1)
    rw [show scanVal cd j = scanWor (mdigits cd) j ||| W ((mdigits cd)[j]!) from by
      rw [scanVal, ← hd]]
    rfl
  · show RepresentsY (msScanJ yst (scanVal cd j) j).memory MOD (nlimbs cd)
      (partVal cd (modulusSize cd))
    rw [show (msScanJ yst (scanVal cd j) j).memory =
        storeWord (msT0 yst (scanVal cd j)).memory Icell (W (j + 1)) from rfl]
    refine RepresentsY_storeWord_disjoint ?_ (by omega)
    show RepresentsY (msT0 yst (scanVal cd j)).memory MOD (nlimbs cd) _
    rw [show (msT0 yst (scanVal cd j)).memory =
      storeWord yst.memory T0 (scanVal cd j) from rfl]
    exact RepresentsY_storeWord_disjoint hinv.rep (by omega)
  · intro a ha1 ha2
    show (msScanJ yst (scanVal cd j) j).memory a = 0
    rw [show (msScanJ yst (scanVal cd j) j).memory =
        storeWord (msT0 yst (scanVal cd j)).memory Icell (W (j + 1)) from rfl,
      storeWord_out _ _ _ _ (by omega : ¬(Icell ≤ a ∧ a < Icell + 32))]
    show (msT0 yst (scanVal cd j)).memory a = 0
    rw [show (msT0 yst (scanVal cd j)).memory =
      storeWord yst.memory T0 (scanVal cd j) from rfl,
      storeWord_out _ _ _ _ (by omega : ¬(T0 ≤ a ∧ a < T0 + 32))]
    exact hinv.midzero a ha1 ha2

set_option maxHeartbeats 16000000 in
/-- One scan round: OR limb `j` into `T0`, bump `Icell`, jump back. -/
theorem mscan_round {cd : ByteArray} {yst : EvmState} (hv : ValidInput cd)
    {j : Nat} (hj : j < nlimbs cd) (hinv : BMScan yst cd j) :
    ∃ yst', BMScan yst' cd (j + 1) ∧
      ASteps programAsm ⟨bigMScanTop programLabels ++ progTail, [], yst⟩
        ⟨bigMScanTop programLabels ++ progTail, [], yst'⟩ := by
  obtain ⟨hd, -, -, -⟩ := mscan_digit hv hj hinv
  exact ⟨msScanJ yst (scanVal cd j) j, mscan_reinv hv hinv hd, mscan_steps hv hj hinv⟩

/-- The OR accumulator is zero exactly when every scanned limb is. -/
theorem scanWor_eq_zero (l : List Nat) (j : Nat)
    (hb : ∀ i, i < j → l[i]! < 2 ^ 256) :
    scanWor l j = 0 ↔ ∀ i, i < j → l[i]! = 0 := by
  induction j with
  | zero =>
    constructor
    · intro h i hi
      exact absurd hi (Nat.not_lt_zero i)
    · intro _
      rfl
  | succ n ih =>
    have ih' := ih (fun i _ => hb i (by omega))
    constructor
    · intro h i hi
      have h2 : scanWor l n = 0 ∧ W (l[n]!) = 0 := BitVec.or_eq_zero_iff.mp h
      by_cases hie : i = n
      · have hz := (W_eq_zero (hb n (by omega))).mp h2.2
        rwa [hie]
      · exact ih'.mp h2.1 i (by omega)
    · intro h
      refine BitVec.or_eq_zero_iff.mpr ⟨ih'.mpr (fun i hi => h i (by omega)), ?_⟩
      exact (W_eq_zero (hb n (by omega))).mpr (h n (by omega))

/-- `ofDigits` of an all-zero (bang-indexed) digit list is zero. -/
private theorem ofDigits_zero_of_bang : ∀ (l : List Nat),
    (∀ i, i < l.length → l[i]! = 0) → Nat.ofDigits radix l = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons d t ih =>
    intro hall
    have hd : d = 0 := by
      have hh := hall 0 (by simp)
      simpa using hh
    have ht : ∀ i, i < t.length → t[i]! = 0 := by
      intro i hi
      have hh := hall (i + 1) (by simp; omega)
      simpa using hh
    show d + radix * Nat.ofDigits radix t = 0
    rw [hd, ih ht]
    simp

/-- All limbs zero exactly when the value is zero. -/
theorem limbDigits_zero_iff {n v : Nat} (hv : v < radix ^ n) :
    (∀ i, i < n → (limbDigits n v)[i]! = 0) ↔ v = 0 := by
  constructor
  · intro h
    have hzero : Nat.ofDigits radix (limbDigits n v) = 0 :=
      ofDigits_zero_of_bang _ (by
        intro i hi
        rw [length_limbDigits hv] at hi
        exact h i hi)
    rw [← value_limbDigits n v, hzero]
  · intro h i hi
    subst h
    have hp : (0 : Nat) < radix ^ n := Nat.pow_pos radix_pos
    have g := limbDigit (n := n) (v := 0) (L := i) hi hp
    simpa using g

/-- The zero-scan loop: `nlimbs` rounds reach the dispatch with the full
OR accumulated in `T0`. -/
theorem big_zero_scan (cd : ByteArray) (hv : ValidInput cd) {yst : EvmState}
    (hinv : BMScan yst cd 0) :
    ∃ yst', BMScan yst' cd (nlimbs cd) ∧
      ASteps programAsm ⟨bigMScanTop programLabels ++ progTail, [], yst⟩
        ⟨jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
            secTailSer programLabels ++ progTail, [], yst'⟩ := by
  have hn : nlimbs cd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (limbCount_le_32 _ (by obtain ⟨-, -, hm⟩ := hv; omega)) (by norm_num)
  refine loop_counted (model := localModel)
    (prog := programAsm) (top := bigMScanTop programLabels ++ progTail)
    (σ := ([] : List AVal))
    (c' := jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
      secTailSer programLabels ++ progTail)
    (Inv := fun yst r => r ≤ nlimbs cd ∧ BMScan yst cd (nlimbs cd - r))
    (P := fun yst => BMScan yst cd (nlimbs cd)) ?_ ?_ (n := nlimbs cd)
    (by exact ⟨le_refl _, by rw [Nat.sub_self]; exact hinv⟩)
  · intro r yst hr ⟨hrle, hinv⟩
    obtain ⟨yst2, hinv2, hst⟩ := mscan_round hv (by omega) hinv
    refine Or.inl ⟨yst2, ⟨by omega, ?_⟩, hst⟩
    rw [show nlimbs cd - (r - 1) = nlimbs cd - r + 1 from by omega]
    exact hinv2
  · intro yst ⟨hr0, hinv⟩
    have hIcv : Icell = 7392 := rfl
    have hNcv : Ncell = 7360 := rfl
    simp only [Nat.sub_zero] at hinv
    have hexit : ¬ (loadWord yst.memory Icell).ult (loadWord yst.memory Ncell) := by
      rw [hinv.icell, hinv.ncell]
      exact W_nult hn hn (le_refl _)
    exact ⟨hinv, jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load Ncell)
      (pin250 hinv.aw (by omega)) (pin250 hinv.aw (by omega)) hexit findLbMScanDone⟩

/-- The digits of the represented modulus are word-sized. -/
private theorem mdigits_lt {cd : ByteArray} {yst : EvmState} {j : Nat}
    (hinv : BMScan yst cd j) (i : Nat) (hi : i < nlimbs cd) :
    (mdigits cd)[i]! < 2 ^ 256 := by
  have g := limbDigit (n := nlimbs cd) (v := partVal cd (modulusSize cd))
    (L := i) hi hinv.rep.1
  have hlt : partVal cd (modulusSize cd) / radix ^ i % radix < 2 ^ 256 := by
    have h := Nat.mod_lt (partVal cd (modulusSize cd) / radix ^ i) radix_pos
    exact h
  show (mdigits cd)[i]! < 2 ^ 256
  rw [show (mdigits cd)[i]! = partVal cd (modulusSize cd) / radix ^ i % radix from by
    show (limbDigits (nlimbs cd) (partVal cd (modulusSize cd)))[i]! = _
    exact g]
  exact hlt

/-- Dispatch on a zero modulus: jump to the serializer, state unchanged. -/
theorem big_scan_zero (cd : ByteArray) {yst : EvmState}
    (hinv : BMScan yst cd (nlimbs cd))
    (hzero : partVal cd (modulusSize cd) = 0) :
    ASteps programAsm ⟨jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
        secTailSer programLabels ++ progTail, [], yst⟩
      ⟨bpSer programLabels ++ progTail, [], yst⟩ := by
  have hT0v : T0 = 7616 := rfl
  have h0 : scanWor (mdigits cd) (nlimbs cd) = 0 := by
    rw [scanWor_eq_zero _ _ (mdigits_lt hinv)]
    intro i hi
    show (limbDigits (nlimbs cd) (partVal cd (modulusSize cd)))[i]! = 0
    rw [limbDigit hi hinv.rep.1, hzero]
    simp [radix]
  have hev : evalExpr (.load T0) yst = 0 := by
    show loadWord yst.memory T0 = 0
    rw [hinv.t0cell, h0]
  rw [show jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
        secTailSer programLabels ++ progTail =
      jumpIfZ (.load T0) programLabels.lbSer ++
        ((bigMid programLabels ++ secTailSer programLabels) ++
          progTail) from by
      simp only [List.append_assoc]]
  exact jumpIfZ_taken (model := localModel) (prog := programAsm)
    (e := .load T0) (l := programLabels.lbSer)
    (k := (bigMid programLabels ++ secTailSer programLabels) ++
      progTail)
    (pin250 hinv.aw (by omega)) hev findLbSer

/-- Dispatch on a nonzero modulus: fall into the big-modulus computation. -/
theorem big_scan_nonzero (cd : ByteArray) {yst : EvmState}
    (hinv : BMScan yst cd (nlimbs cd))
    (hnzero : partVal cd (modulusSize cd) ≠ 0) :
    loadWord yst.memory T0 ≠ 0 ∧
      ASteps programAsm ⟨jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
          secTailSer programLabels ++ progTail, [], yst⟩
        ⟨bigMid programLabels ++ (secTailSer programLabels ++ progTail),
          [], yst⟩ := by
  have hn0 : scanWor (mdigits cd) (nlimbs cd) ≠ 0 := by
    intro h0
    apply hnzero
    have hall : ∀ i, i < nlimbs cd →
        (limbDigits (nlimbs cd) (partVal cd (modulusSize cd)))[i]! = 0 := by
      intro i hi
      have hh := (scanWor_eq_zero _ _ (mdigits_lt hinv)).mp h0 i hi
      show (limbDigits (nlimbs cd) (partVal cd (modulusSize cd)))[i]! = 0
      exact hh
    have := (limbDigits_zero_iff hinv.rep.1).mp hall
    show partVal cd (modulusSize cd) = 0
    exact this
  have hT0v : T0 = 7616 := rfl
  refine ⟨by rw [hinv.t0cell]; exact hn0, ?_⟩
  have hev : evalExpr (.load T0) yst ≠ 0 := by
    show loadWord yst.memory T0 ≠ 0
    rw [hinv.t0cell]
    exact hn0
  rw [show jumpIfZ (.load T0) programLabels.lbSer ++ bigMid programLabels ++
        secTailSer programLabels ++ progTail =
      jumpIfZ (.load T0) programLabels.lbSer ++
        (bigMid programLabels ++ (secTailSer programLabels ++ progTail)) from by
      simp only [List.append_assoc]]
  exact jumpIfZ_fall (model := localModel) (prog := programAsm)
    (e := .load T0) (l := programLabels.lbSer)
    (pin250 hinv.aw (by omega)) hev

end Challenge.Modexp.Submission.Proof.BigLoad

import Challenge.Modexp.Submission.Proof.MulModProcProof
import Challenge.Modexp.Submission.Proof.BigBaseProc
import Challenge.Modexp.Submission.Proof.BigSerProc
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic

set_option warningAsError true
set_option maxHeartbeats 80000000
set_option maxRecDepth 1000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# The big path's exponent phase and full-run composition (procedure basis)

`secBigPath`'s exponent section (from `BigBase.bigBase_correct`'s exit at
`bbExpRest`): the exponent byte scan (`lbEScan`, skipping leading zero
bytes), the top-bit find (`lbInit`/`lbTop`), the accumulator seed
(`lbAccInit`, ACC := BASE), the top-bits loop (`lbTopBits`) and the
remaining-bytes loop (`lbBytes`/`lbByteBits`), each bit consuming one
squaring `callMulMod ACC` plus a conditional `callMulMod BASE` — the
MSB-first prefix invariant `ACC ≡ b ^ (exponent prefix) % m`.

`bigExp_correct` composes header → load → base → exponent → serializer for
every valid input with `32 < modulusSize`, concluding the full-run halting
statement with `spec calldata`'s bytes.
-/

namespace Challenge.Modexp.Submission.Proof.BigExpProc

open Challenge.Modexp.Submission
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proof.YulLimbs
open Challenge.Modexp.Submission.Proof.MulModProc
open Challenge.Modexp.Submission.Proof.YulMem
open Challenge.Modexp.Submission.Proof.BigLoad
open Challenge.Modexp.Submission.Proof.BigBaseProc
open Challenge.Modexp.Submission.Proof.BigSer
open Challenge.Modexp.Submission.Proofs.Algorithm (modPow_eq)
open Challenge.Modexp.Submission.Proof.Header
open YulEvmCompiler

/-- Shorthand for the 256-bit word carrying the natural `n`. -/
local notation:max "W " n:max => BitVec.ofNat 256 n
open YulSemantics.EVM (U256 EvmState loadWord storeWord b2w byteFrom)
open EvmSemantics.EVM.Precompile (bytesToNatPadded natToBytes modPow)
open Challenge.EvmProof.Bytes (bytesToNatPadded_succ bytesToNatPadded_zero_width
  bytesToNatPadded_lt_pow)

/-! ## The instantiated `addMod` contract -/

/-- `AddModProcSpec` is habitable: instantiate the frozen contract from
`Proof.AddModProcProof.addModCall_correct` with BigBase's concrete label
record, the internal `findLabel` facts (proved there), and the mulMod
section as the procedure tail. -/
def theAddModSpec : AddModProcSpec where
  correct dst src lret cont σ yst n m x y
      hn hn32 hN haw hdstN hsrcN hmodDst hmodSrc hds hsubcDst hsubcSrc
      hm hm0 hx hxm hy hym hfindRet :=
    Challenge.Modexp.Submission.Proof.AddModProcProof.addModCall_correct
      (model := localModel) (prog := programAsm)
      (dst := dst) (src := src) (lret := lret) (l := amLabels)
      (n := n) (m := m) (x := x) (y := y)
      (tail := secMulModProc programLabels) (cont := cont) (σ := σ) (yst := yst)
      (hmem := (mem_labelDefs_iff_findLabel).mpr (by rw [hfindRet]; rfl))
      findAmEntry findAmAdd findAmSubStart findAmSub findAmSel findAmDoCopy
      findAmCopy findAmDone hfindRet
      hn hn32 hN haw hdstN hsrcN hmodDst hmodSrc hds hsubcDst hsubcSrc
      hm hm0 hx hxm hy hym

/-! ## Values -/

/-- The exponent's byte offset in the calldata. -/
def eOff (cd : ByteArray) : Nat := 96 + baseSize cd

/-- The exponent value. -/
def eVal (cd : ByteArray) : Nat := bytesToNatPadded cd (eOff cd) (exponentSize cd)

/-- The exponent prefix of the first `i` bytes. -/
def ePfx (cd : ByteArray) (i : Nat) : Nat := bytesToNatPadded cd (eOff cd) i

/-- Exponent byte `i`. -/
def eByte (cd : ByteArray) (i : Nat) : Nat := (byteFrom cd.toList (eOff cd + i)).toNat

/-- The base value. -/
def bVal (cd : ByteArray) : Nat := bPre cd (baseSize cd)

theorem eByte_lt (cd : ByteArray) (i : Nat) : eByte cd i < 256 :=
  (byteFrom cd.toList (eOff cd + i)).toNat_lt

theorem ePfx_succ (cd : ByteArray) (i : Nat) :
    ePfx cd (i + 1) = ePfx cd i * 256 + eByte cd i := by
  simp only [ePfx, eByte, eOff, bytesToNatPadded_succ]

/-! ## The exponent section's fragments -/

/-- The fixed continuation after the exponent section: the serializer's
top label and body, then the halt stubs and the two procedures. -/
def beSer : List Asm := secTailSer programLabels ++ progTail

/-- The byte-bits loop body (one bit of an exponent byte). -/
def beByteBitsBody : List Asm :=
  jumpIfZ (.load Jcell) programLabels.lbNextByte ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  callMulMod ACC programLabels.lsqRet2 programLabels.lmmEntry ++
  jumpIfZ bitTest programLabels.lbByteBitsSkip ++
  callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
  [.label programLabels.lbByteBitsSkip] ++
  [.jump programLabels.lbByteBits] ++
  [.label programLabels.lbNextByte] ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump programLabels.lbBytes]

/-- The remaining-bytes loop body. -/
def beBytesBody : List Asm :=
  jumpUnlessLt (.load Icell) (.load ES) programLabels.lbSer ++
  store Wcell (cdbCell EO) ++
  store Jcell (.imm 8) ++
  [.label programLabels.lbByteBits] ++
  beByteBitsBody

/-- The top-bits loop body (one bit of the first exponent byte). -/
def beTopBitsBody : List Asm :=
  jumpIfZ (.load Jcell) programLabels.lbRest ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  callMulMod ACC programLabels.lsqRet1 programLabels.lmmEntry ++
  jumpIfZ bitTest programLabels.lbTopBitsSkip ++
  callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
  [.label programLabels.lbTopBitsSkip] ++
  [.jump programLabels.lbTopBits] ++
  [.label programLabels.lbRest] ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.label programLabels.lbBytes] ++
  beBytesBody

/-- The ACC-seed copy loop body. -/
def beSeedBody : List Asm :=
  jumpUnlessLt (.load I2) (.load Ncell) programLabels.lbAccInitDone ++
  storeAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm BASE) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump programLabels.lbAccInit] ++
  [.label programLabels.lbAccInitDone] ++
  [.label programLabels.lbTopBits] ++
  beTopBitsBody

/-- The top-bit scan body (from just after `.label lbTop`). -/
def beTopBody : List Asm :=
  jumpIfNz bitTest programLabels.lbInitAcc ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  [.jump programLabels.lbTop] ++
  [.label programLabels.lbInitAcc] ++
  store I2 (.imm 0) ++
  [.label programLabels.lbAccInit] ++
  beSeedBody

/-- From `.label lbInit` on. -/
def beFromInit : List Asm :=
  [.label programLabels.lbInit] ++
  store Jcell (.imm 7) ++
  [.label programLabels.lbTop] ++
  beTopBody

/-- The exponent scan loop body. -/
def beScanBody : List Asm :=
  jumpUnlessLt (.load Icell) (.load ES) programLabels.lbSer ++
  store Wcell (cdbCell EO) ++
  jumpIfNz (.load Wcell) programLabels.lbInit ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump programLabels.lbEScan]

/-- The whole exponent section (the code from `bbExpRest`). -/
def beExpAll : List Asm :=
  store Icell (.imm 0) ++
  [.label programLabels.lbEScan] ++
  beScanBody ++
  beFromInit

theorem bbExpRest_eq : bbExpRest programLabels = beExpAll := rfl

/-! ## Label resolutions -/

theorem findLbEScan : findLabel programLabels.lbEScan programAsm =
    some (beScanBody ++ (beFromInit ++ beSer)) := by decide

theorem findLbInit : findLabel programLabels.lbInit programAsm =
    some (store Jcell (.imm 7) ++
      ([.label programLabels.lbTop] ++ (beTopBody ++ beSer))) := by decide

theorem findLbTop : findLabel programLabels.lbTop programAsm =
    some (beTopBody ++ beSer) := by decide

theorem findLbAccInit : findLabel programLabels.lbAccInit programAsm =
    some (beSeedBody ++ beSer) := by decide

theorem findLbAccInitDone : findLabel programLabels.lbAccInitDone programAsm =
    some ([.label programLabels.lbTopBits] ++ (beTopBitsBody ++ beSer)) := by decide

theorem findLbTopBits : findLabel programLabels.lbTopBits programAsm =
    some (beTopBitsBody ++ beSer) := by decide

theorem findLbRest : findLabel programLabels.lbRest programAsm =
    some (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer))) := by decide

theorem findLbBytes : findLabel programLabels.lbBytes programAsm =
    some (beBytesBody ++ beSer) := by decide

theorem findLbByteBits : findLabel programLabels.lbByteBits programAsm =
    some (beByteBitsBody ++ beSer) := by decide

theorem findLmmEntry : findLabel programLabels.lmmEntry programAsm =
    some (mulModProcBody procLabels) := by decide

theorem findLsqRet1 : findLabel programLabels.lsqRet1 programAsm =
    some (jumpIfZ bitTest programLabels.lbTopBitsSkip ++
      (callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
        ([.label programLabels.lbTopBitsSkip] ++
          ([.jump programLabels.lbTopBits] ++
            ([.label programLabels.lbRest] ++
              (store Icell (.bin .add (.load Icell) (.imm 1)) ++
                ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))))) := by decide

theorem findLmulRet1 : findLabel programLabels.lmulRet1 programAsm =
    some ([.label programLabels.lbTopBitsSkip] ++
      ([.jump programLabels.lbTopBits] ++
        ([.label programLabels.lbRest] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))) := by decide

theorem findLsqRet2 : findLabel programLabels.lsqRet2 programAsm =
    some (jumpIfZ bitTest programLabels.lbByteBitsSkip ++
      (callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
        ([.label programLabels.lbByteBitsSkip] ++
          ([.jump programLabels.lbByteBits] ++
            ([.label programLabels.lbNextByte] ++
              (store Icell (.bin .add (.load Icell) (.imm 1)) ++
                ([.jump programLabels.lbBytes] ++ beSer))))))) := by decide

theorem findLmulRet2 : findLabel programLabels.lmulRet2 programAsm =
    some ([.label programLabels.lbByteBitsSkip] ++
      ([.jump programLabels.lbByteBits] ++
        ([.label programLabels.lbNextByte] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.jump programLabels.lbBytes] ++ beSer))))) := by decide

theorem memLsqRet1 : programLabels.lsqRet1 ∈ labelDefs programAsm := by decide
theorem memLmulRet1 : programLabels.lmulRet1 ∈ labelDefs programAsm := by decide
theorem memLsqRet2 : programLabels.lsqRet2 ∈ labelDefs programAsm := by decide
theorem memLmulRet2 : programLabels.lmulRet2 ∈ labelDefs programAsm := by decide

/-- The exponent-phase frame: the cells and limb regions every exponent-phase
lemma keeps.  Every framed cell (`ES`, `EO`, `Ncell`, `MS`) and region
(`MOD`, `BASE`) sits clear of the `mulMod` procedure's write set and the
scalar stores of the exponent loops, so the frame survives each round;
`hn32` records the limb bound the disjointness facts consume. -/
structure BEF (yst : EvmState) (cd : ByteArray) : Prop where
  aw : yst.activeWords.toNat = 250
  env : yst.env.calldata = cd.toList
  escell : loadWord yst.memory ES = W (exponentSize cd)
  eocell : loadWord yst.memory EO = W (eOff cd)
  ncell : loadWord yst.memory Ncell = W (nlimbs cd)
  mscell : loadWord yst.memory MS = W (modulusSize cd)
  modrep : RepresentsY yst.memory MOD (nlimbs cd) (modVal cd)
  baserep : RepresentsY yst.memory BASE (nlimbs cd) (bVal cd % modVal cd)
  hn32 : nlimbs cd ≤ 32

/-- The exponent-scan state: the frame with the exponent cursor and the
MSB-first prefix invariant on `ACC`. -/
structure BE (yst : EvmState) (cd : ByteArray) (i : Nat) : Prop where
  fr : BEF yst cd
  icell : loadWord yst.memory Icell = W i
  accrep : RepresentsY yst.memory ACC (nlimbs cd)
    (bVal cd ^ ePfx cd i % modVal cd)

theorem BE_of_BBExit {cd : ByteArray} {yst : EvmState}
    (hx : BBExit yst cd) :
    BE { yst with memory := storeWord yst.memory Icell (W 0) } cd 0 := by
  have hIc : (Icell : Nat) = 7392 := rfl
  have hNc : (Ncell : Nat) = 7360 := rfl
  have hMOD : (MOD : Nat) = 0 := rfl
  have hBASE : (BASE : Nat) = 1024 := rfl
  have hACC : (ACC : Nat) = 2048 := rfl
  have hn32 : nlimbs cd ≤ 32 := hx.hn32
  refine ⟨⟨hx.aw, hx.env, hx.escell, hx.eocell, ?_, hx.mscell, ?_, ?_, hn32⟩, ?_, ?_⟩
  · show loadWord (storeWord yst.memory Icell (W 0)) Ncell = _
    rw [load_disj' yst.memory Icell Ncell (W 0) (Or.inr (by omega))]
    exact hx.ncell
  · exact RepresentsY_storeWord_disjoint (v := (W 0)) (q := Icell) hx.modrep (by omega)
  · exact RepresentsY_storeWord_disjoint (v := (W 0)) (q := Icell) hx.baserep (by omega)
  · show loadWord (storeWord yst.memory Icell (W 0)) Icell = W 0
    rw [loadWord_storeWord_self]
  · have hacc := RepresentsY_storeWord_disjoint (v := (W 0)) (q := Icell)
      hx.accrep (by omega)
    have hz : bVal cd ^ ePfx cd 0 % modVal cd = 1 % modVal cd := by
      rw [ePfx, bytesToNatPadded_zero_width, Nat.pow_zero]
    exact ⟨hz ▸ hacc.1, hz ▸ hacc.2⟩

/-! ## The exponent scan -/

/-- One round of the exponent scan from `Icell = i < es`: fall the exit
test, read exponent byte `i` into `Wcell`, and either jump to `lbInit`
(byte nonzero) or bump `Icell` and jump back. -/
theorem exp_scan_round {cd : ByteArray} {yst : EvmState} {i : Nat}
    (hv : ValidInput cd) (hinv : BE yst cd i) (hi : i < exponentSize cd) :
    ((eByte cd i ≠ 0 ∧
      ASteps programAsm ⟨beScanBody ++ (beFromInit ++ beSer), [], yst⟩
        ⟨store Jcell (.imm 7) ++ ([.label programLabels.lbTop] ++
          (beTopBody ++ beSer)), [],
          { yst with memory :=
              storeWord yst.memory Wcell (W (eByte cd i)) }⟩) ∨
    (eByte cd i = 0 ∧
      ASteps programAsm ⟨beScanBody ++ (beFromInit ++ beSer), [], yst⟩
        ⟨beScanBody ++ (beFromInit ++ beSer), [],
          { yst with memory :=
              storeWord (storeWord yst.memory Wcell (W (eByte cd i))) Icell (W (i + 1)) }⟩)) := by
  have hIw : loadWord yst.memory Icell = W i := hinv.icell
  have hIcV : (Icell : Nat) = 7392 := rfl
  have hEsV : (ES : Nat) = 7200 := rfl
  have hEoV : (EO : Nat) = 7296 := rfl
  have hWcV : (Wcell : Nat) = 7456 := rfl
  have hes1024 : exponentSize cd ≤ 1024 := by
    obtain ⟨-, -, he, -⟩ := hv
    exact he
  set es := exponentSize cd with hesdef
  set eo := eOff cd with heodef
  have hb1024 : baseSize cd ≤ 1024 := by
    obtain ⟨-, hb, -, -⟩ := hv
    exact hb
  have h2048 : (2048 : Nat) < 2 ^ 255 := by decide
  have heow : eo < 2 ^ 255 := by rw [heodef, eOff]; omega
  have hi256 : i < 2 ^ 256 := Nat.lt_trans hi (size_lt _ hes1024)
  -- step 1: the exit test falls (i < es)
  have hult : (evalExpr (.load Icell) yst).ult (evalExpr (.load ES) yst) := by
    show (loadWord yst.memory Icell).ult (loadWord yst.memory ES) = true
    rw [hIw, hinv.fr.escell]
    exact W_ult hi256 (size_lt _ hes1024) hi
  have s1 : ASteps programAsm
      ⟨jumpUnlessLt (.load Icell) (.load ES) programLabels.lbSer ++
        (store Wcell (cdbCell EO) ++ (jumpIfNz (.load Wcell) programLabels.lbInit ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer))))), [], yst⟩
      ⟨store Wcell (cdbCell EO) ++ (jumpIfNz (.load Wcell) programLabels.lbInit ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer)))), [], yst⟩ :=
    jumpUnlessLt_fall (pin250 hinv.fr.aw (by omega)) (pin250 hinv.fr.aw (by omega)) hult
  -- step 2: Wcell := exponent byte i
  have heoB : eo ≤ 1120 := by rw [heodef, eOff]; omega
  have hiB : i ≤ 1024 := Nat.le_of_lt (Nat.lt_of_lt_of_le hi hes1024)
  have hbig : (2144 : Nat) < 2 ^ 256 := by norm_num
  have hWsum : (W eo + W i : U256) = W (eo + i) := W_add (by omega)
  have hToW : (W (eo + i)).toNat = eo + i := toNat_W (by omega)
  have haddr : (evalExpr (.bin .add (.load EO) (.load Icell)) yst).toNat
      = eo + i := by
    show (loadWord yst.memory EO + loadWord yst.memory Icell).toNat = eo + i
    rw [hinv.fr.eocell, hIw, hWsum, hToW]
  have hcdb : evalExpr (cdbCell EO) yst = W (eByte cd i) := by
    show evalExpr (Expr.cdb (.bin .add (.load EO) (.load Icell))) yst = _
    rw [evalExpr_cdb haddr]
    show W (byteFrom yst.env.calldata (eo + i)).toNat = _
    rw [hinv.fr.env, eByte]
  have s2 := store_pin (c := Wcell) (e := cdbCell EO) (v := W (eByte cd i))
    (k := jumpIfNz (.load Wcell) programLabels.lbInit ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer))))
    (yst := yst)
    (by
      show binOK YulSemantics.EVM.Op.add = true ∧
        exprOK (Expr.load EO) yst ∧ exprOK (Expr.load Icell) yst
      exact ⟨rfl, pin250 hinv.fr.aw (by omega), pin250 hinv.fr.aw (by omega)⟩)
    (by decide)
    (by rw [hinv.fr.aw]; show Wcell + 32 ≤ 32 * 250; omega)
    hcdb
  set S1 : EvmState :=
      { yst with memory := storeWord yst.memory Wcell (W (eByte cd i)) } with hS1def
  have hS1mem : S1.memory = storeWord yst.memory Wcell (W (eByte cd i)) := rfl
  have hS1I : loadWord S1.memory Icell = W i := by
    rw [hS1mem, load_disj' yst.memory Wcell Icell (W (eByte cd i))
      (Or.inr (by
        have hW : (Wcell : Nat) = 7456 := rfl
        have hI : (Icell : Nat) = 7392 := rfl
        omega))]
    exact hIw
  have htop : beScanBody ++ (beFromInit ++ beSer) =
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lbSer ++
        (store Wcell (cdbCell EO) ++ (jumpIfNz (.load Wcell) programLabels.lbInit ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer))))) := by
    rw [beScanBody]; simp only [List.append_assoc]
  rcases Nat.eq_zero_or_pos (eByte cd i) with hz | hnz
  · refine Or.inr ⟨hz, ?_⟩
    have hzW : evalExpr (.load Wcell) S1 = 0 := by
      show loadWord S1.memory Wcell = 0
      rw [hS1mem, loadWord_storeWord_self, hz]
      rfl
    have s3 := jumpIfNz_fall (model := localModel) (prog := programAsm)
      (e := .load Wcell) (l := programLabels.lbInit) (yst := S1)
      (σ := ([] : List AVal))
      (k := store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer)))
      (pin250 hinv.fr.aw (by omega)) hzW
    have hev : evalExpr (.bin .add (.load Icell) (.imm 1)) S1
        = W (i + 1) := by
      show loadWord S1.memory Icell + W 1 = _
      rw [hS1I, W_add (by omega : i + 1 < 2 ^ 256)]
    have s4 := store_pin (c := Icell)
      (e := .bin .add (.load Icell) (.imm 1)) (v := W (i + 1))
      (k := [.jump programLabels.lbEScan] ++ (beFromInit ++ beSer)) (yst := S1)
      (by refine ⟨rfl, pin250 hinv.fr.aw (by omega), True.intro⟩)
      (by decide) (by rw [hinv.fr.aw]; show Icell + 32 ≤ 32 * 250; omega) hev
    have s5 : ASteps programAsm
        ⟨[.jump programLabels.lbEScan] ++ (beFromInit ++ beSer), [],
          { S1 with memory := storeWord S1.memory Icell (W (i + 1)) }⟩
        ⟨beScanBody ++ (beFromInit ++ beSer), [],
          { S1 with memory := storeWord S1.memory Icell (W (i + 1)) }⟩ :=
      ASteps.single (astep_jump (model := localModel)
        (prog := programAsm) (l := programLabels.lbEScan)
        (c' := beScanBody ++ (beFromInit ++ beSer)) findLbEScan)
    rw [htop]
    exact (((s1.trans s2).trans s3).trans s4).trans s5
  · refine Or.inl ⟨fun hcon => absurd hcon (by omega), ?_⟩
    have hnW : evalExpr (.load Wcell) S1 ≠ 0 := by
      show loadWord S1.memory Wcell ≠ 0
      rw [hS1mem, loadWord_storeWord_self]
      exact W_ne_zero (by omega) (by
        have := eByte_lt cd i; omega)
    have s3 := jumpIfNz_taken (model := localModel) (prog := programAsm)
      (e := .load Wcell) (l := programLabels.lbInit) (yst := S1)
      (σ := ([] : List AVal))
      (c' := store Jcell (.imm 7) ++ ([.label programLabels.lbTop] ++
        (beTopBody ++ beSer)))
      (k := store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer)))
      (pin250 hinv.fr.aw (by omega)) hnW findLbInit
    rw [htop]
    exact (s1.trans s2).trans s3

/-- The exponent prefix at width zero. -/
theorem ePfx_zero (cd : ByteArray) : ePfx cd 0 = 0 :=
  bytesToNatPadded_zero_width cd (eOff cd)

/-- The found-branch landing: after `.label lbInitAcc`. -/
theorem findLbInitAcc : findLabel programLabels.lbInitAcc programAsm =
    some (store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
      (beSeedBody ++ beSer))) := by decide

/-- The top-bits bit-skip landing. -/
theorem findLbTopBitsSkip : findLabel programLabels.lbTopBitsSkip programAsm =
    some ([.jump programLabels.lbTopBits] ++ ([.label programLabels.lbRest] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer))))) := by decide

/-- The byte-bits bit-skip landing. -/
theorem findLbByteBitsSkip : findLabel programLabels.lbByteBitsSkip programAsm =
    some ([.jump programLabels.lbByteBits] ++ ([.label programLabels.lbNextByte] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer)))) := by decide

/-- The byte-bits counter-exhaust landing. -/
theorem findLbNextByte : findLabel programLabels.lbNextByte programAsm =
    some (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.jump programLabels.lbBytes] ++ beSer)) := by decide

/-- The seed-copy loop's label record: the `mulMod` procedure's labels with
the copy-loop field repointed at `lbAccInit`. -/
def seedLabels : MulModProcLabels :=
  { procLabels with lCopy := programLabels.lbAccInit }

/-- The seed-copy loop top resolves to the copy body plus the top-bits
continuation (definitionally the seed body's first four statements). -/
theorem findSeedCopy : findLabel seedLabels.lCopy programAsm =
    some (mulModCopyBody ACC BASE programLabels.lbAccInitDone seedLabels ++
      ([.label programLabels.lbAccInitDone] ++
        ([.label programLabels.lbTopBits] ++ (beTopBitsBody ++ beSer)))) :=
  findLbAccInit

theorem be_div_step (w n : Nat) (hn : 0 < n) :
    w / 2 ^ (n - 1) = 2 * (w / 2 ^ n) + (w / 2 ^ (n - 1)) % 2 := by
  have hnp : (2 : Nat) ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    rw [Nat.pow_succ]
  have hdd : w / 2 ^ n = (w / 2 ^ (n - 1)) / 2 := by
    rw [hnp, Nat.div_div_eq_div_mul]
  rw [hdd, Nat.div_add_mod (w / 2 ^ (n - 1)) 2]

/-- Squaring at the mod level. -/
theorem be_sq_mod (b E m x : Nat) (hx : x = b ^ E % m) :
    (x * x) % m = b ^ (2 * E) % m := by
  rw [hx, ← Nat.mul_mod, show 2 * E = E + E from by omega, Nat.pow_add]

/-- Multiplying by the reduced base at the mod level. -/
theorem be_mulbase_mod (b E m x t : Nat) (hx : x = b ^ E % m) (ht : t = b % m) :
    (x * t) % m = b ^ (E + 1) % m := by
  rw [hx, ht, ← Nat.mul_mod, Nat.pow_succ]

/-- One byte-bits round's exponent arithmetic: doubling the pending quotient
moves the `2 ^ j` window down one bit. -/
theorem be_bit_step (X wb n : Nat) (hn : 0 < n) (hn8 : n ≤ 8) :
    2 * (X * 2 ^ (8 - n) + wb / 2 ^ n) + wb / 2 ^ (n - 1) % 2
      = X * 2 ^ (8 - (n - 1)) + wb / 2 ^ (n - 1) := by
  have hpow : 2 ^ (8 - (n - 1)) = 2 ^ (8 - n) * 2 := by
    rw [show 8 - (n - 1) = 8 - n + 1 from by omega, Nat.pow_succ]
  have hd : wb / 2 ^ (n - 1) = 2 * (wb / 2 ^ n) + wb / 2 ^ (n - 1) % 2 :=
    be_div_step wb n hn
  rw [hpow, show X * (2 ^ (8 - n) * 2) = 2 * (X * 2 ^ (8 - n)) from by ring]
  omega

/-! ## Frame transfers -/

/-- Every `mulMod` scratch cell lies at or above `C1`, clear of the framed
cells and the loop counters. -/
theorem mmScratch_ge : ∀ c ∈ mulModScratch, C1 ≤ c := by decide

/-- The `mulModCall_correct` byte-frame, as a state relation. -/
def MMKeeps (yst yst' : EvmState) (n : Nat) : Prop :=
  ∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) → (q < ACC ∨ ACC + 32 * n ≤ q) →
    (q < SUBC ∨ SUBC + 32 * n ≤ q) →
    (∀ c ∈ mulModScratch, q < c ∨ c + 32 ≤ q) → (q < BPTR ∨ BPTR + 32 ≤ q) →
    yst'.memory q = yst.memory q

/-- A framed scalar cell (between `BS` and `C1`) survives a `mulMod` call. -/
theorem mm_keeps_cell {n c : Nat} {yst yst' : EvmState} (hk : MMKeeps yst yst' n)
    (hn : n ≤ 32) (hc : BS ≤ c ∧ c + 32 ≤ C1) :
    loadWord yst'.memory c = loadWord yst.memory c := by
  have hOUTv : (OUT : Nat) = 3072 := rfl
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hSUBCv : (SUBC : Nat) = 5120 := rfl
  have hBPTRv : (BPTR : Nat) = 7584 := rfl
  have hC1v : (C1 : Nat) = 7488 := rfl
  have hBSv : (BS : Nat) = 7168 := rfl
  apply loadWord_congr
  intro a ha1 ha2
  refine hk a ?_ ?_ ?_ ?_ ?_
  · omega
  · omega
  · omega
  · intro c hc2
    have hge := mmScratch_ge c hc2
    omega
  · omega

/-- A limb region ending below `ACC` survives a `mulMod` call. -/
theorem mm_keeps_rep {n R v : Nat} {yst yst' : EvmState} (hk : MMKeeps yst yst' n)
    (hn : n ≤ 32) (hR : R + 32 * n ≤ ACC)
    (h : RepresentsY yst.memory R n v) :
    RepresentsY yst'.memory R n v := by
  have hOUTv : (OUT : Nat) = 3072 := rfl
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hSUBCv : (SUBC : Nat) = 5120 := rfl
  have hBPTRv : (BPTR : Nat) = 7584 := rfl
  have hC1v : (C1 : Nat) = 7488 := rfl
  refine ⟨h.1, ?_⟩
  rw [yLimbs_congr (mem := yst'.memory) (mem' := yst.memory) ?_, h.2]
  intro a ha1 ha2
  refine hk a ?_ ?_ ?_ ?_ ?_
  · omega
  · omega
  · omega
  · intro c hc2
    have hge := mmScratch_ge c hc2
    omega
  · omega

/-- The frame survives a `mulMod` call application. -/
theorem bef_mm_keeps {cd : ByteArray} {yst yst' : EvmState}
    (hk : MMKeeps yst yst' (nlimbs cd))
    (haw : yst'.activeWords = yst.activeWords) (henv : yst'.env = yst.env)
    (hf : BEF yst cd) : BEF yst' cd := by
  have hn32 := hf.hn32
  have hMODv : (MOD : Nat) = 0 := rfl
  have hBASEv : (BASE : Nat) = 1024 := rfl
  have hACCv : (ACC : Nat) = 2048 := rfl
  refine ⟨by rw [haw]; exact hf.aw, by rw [henv]; exact hf.env,
    (mm_keeps_cell hk hn32 (c := ES) (by decide)).trans hf.escell,
    (mm_keeps_cell hk hn32 (c := EO) (by decide)).trans hf.eocell,
    (mm_keeps_cell hk hn32 (c := Ncell) (by decide)).trans hf.ncell,
    (mm_keeps_cell hk hn32 (c := MS) (by decide)).trans hf.mscell,
    mm_keeps_rep hk hn32 (by omega) hf.modrep,
    mm_keeps_rep hk hn32 (by omega) hf.baserep,
    hn32⟩

/-- The frame survives a word store to a scratch cell above `EO`. -/
theorem bef_store {cd : ByteArray} {yst : EvmState} {c : Nat} {v : U256}
    (hc : Ncell + 32 ≤ c ∧ c + 32 ≤ TOP) (hf : BEF yst cd) :
    BEF { yst with memory := storeWord yst.memory c v } cd := by
  have hn32 := hf.hn32
  have hESv : (ES : Nat) = 7200 := rfl
  have hEOv : (EO : Nat) = 7296 := rfl
  have hMSv : (MS : Nat) = 7232 := rfl
  have hNcv : (Ncell : Nat) = 7360 := rfl
  have hMODv : (MOD : Nat) = 0 := rfl
  have hBASEv : (BASE : Nat) = 1024 := rfl
  refine ⟨hf.aw, hf.env, ?_, ?_, ?_, ?_, ?_, ?_, hn32⟩
  · show loadWord (storeWord yst.memory c v) ES = _
    rw [load_disj' _ _ _ _ (Or.inr (by omega))]; exact hf.escell
  · show loadWord (storeWord yst.memory c v) EO = _
    rw [load_disj' _ _ _ _ (Or.inr (by omega))]; exact hf.eocell
  · show loadWord (storeWord yst.memory c v) Ncell = _
    rw [load_disj' _ _ _ _ (Or.inr (by omega))]; exact hf.ncell
  · show loadWord (storeWord yst.memory c v) MS = _
    rw [load_disj' _ _ _ _ (Or.inr (by omega))]; exact hf.mscell
  · exact RepresentsY_storeWord_disjoint hf.modrep (by omega)
  · exact RepresentsY_storeWord_disjoint hf.baserep (by omega)
/-- The found state: the frame with the cursor at the first nonzero exponent
byte `i0` and that byte in `Wcell`. -/
structure BEFnd (yst : EvmState) (cd : ByteArray) (i0 : Nat) : Prop where
  fr : BEF yst cd
  icell : loadWord yst.memory Icell = W i0
  wcell : loadWord yst.memory Wcell = W (eByte cd i0)
  wne : eByte cd i0 ≠ 0
  i0lt : i0 < exponentSize cd
  pfx0 : ePfx cd i0 = 0

/-- The exponent scan: from `Icell = i` with `i + n = es` and a zero byte
prefix, either find the first nonzero exponent byte `i0` (landing at the
`lbInit` continuation with the byte in `Wcell`) or exhaust the exponent
(jumping to the serializer's top with the cursor at `es`). -/
theorem exp_scan_loop {cd : ByteArray} (hv : ValidInput cd) :
    ∀ (n i : Nat), i + n = exponentSize cd →
      ∀ (yst : EvmState), BE yst cd i → ePfx cd i = 0 →
      (∃ yst' i0, BEFnd yst' cd i0 ∧
        ASteps programAsm ⟨beScanBody ++ (beFromInit ++ beSer), [], yst⟩
          ⟨store Jcell (.imm 7) ++ ([.label programLabels.lbTop] ++
            (beTopBody ++ beSer)), [], yst'⟩) ∨
      (∃ yst', BE yst' cd (exponentSize cd) ∧
        ASteps programAsm ⟨beScanBody ++ (beFromInit ++ beSer), [], yst⟩
          ⟨bpSer programLabels ++ progTail, [], yst'⟩) := by
  have hIcv : (Icell : Nat) = 7392 := rfl
  have hWcv : (Wcell : Nat) = 7456 := rfl
  intro n
  induction n with
  | zero =>
    intro i hi yst hinv _
    have hes1024 : exponentSize cd ≤ 1024 := by
      obtain ⟨-, -, he, -⟩ := hv
      exact he
    have hie : i = exponentSize cd := by omega
    have hi256 : i < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (by omega) (size_lt _ hes1024)
    right
    refine ⟨yst, by rw [← hie]; exact hinv, ?_⟩
    have hnlt : ¬ (evalExpr (.load Icell) yst).ult (evalExpr (.load ES) yst) := by
      show ¬ (loadWord yst.memory Icell).ult (loadWord yst.memory ES) = true
      rw [hinv.icell, hinv.fr.escell]
      exact W_nult hi256 (size_lt _ hes1024) (by rw [hie])
    have hcode : beScanBody ++ (beFromInit ++ beSer) =
        jumpUnlessLt (.load Icell) (.load ES) programLabels.lbSer ++
          (store Wcell (cdbCell EO) ++ (jumpIfNz (.load Wcell) programLabels.lbInit ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer))))) := by
      rw [beScanBody]; simp only [List.append_assoc]
    rw [hcode]
    exact jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load ES) (l := programLabels.lbSer)
      (c' := bpSer programLabels ++ progTail)
      (k := store Wcell (cdbCell EO) ++ (jumpIfNz (.load Wcell) programLabels.lbInit ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbEScan] ++ (beFromInit ++ beSer)))))
      (σ := ([] : List AVal)) (pin250 hinv.fr.aw (by decide))
      (pin250 hinv.fr.aw (by decide)) hnlt findLbSer
  | succ m ih =>
    intro i hi yst hinv hpfx
    have hies : i < exponentSize cd := by omega
    rcases exp_scan_round hv hinv hies with ⟨hnz, hsteps⟩ | ⟨hz, hsteps⟩
    · refine Or.inl ⟨{ yst with memory := storeWord yst.memory Wcell (W (eByte cd i)) },
        i, ⟨bef_store (c := Wcell) (by decide) hinv.fr, ?_, ?_, hnz, hies, hpfx⟩,
        hsteps⟩
      · show loadWord (storeWord yst.memory Wcell (W (eByte cd i))) Icell = W i
        rw [load_disj' yst.memory Wcell Icell (W (eByte cd i)) (Or.inr (by omega))]
        exact hinv.icell
      · exact loadWord_storeWord_self _ _ _
    · rw [hz] at hsteps
      have hn32 := hinv.fr.hn32
      have hACCv : (ACC : Nat) = 2048 := rfl
      set yst1 : EvmState :=
        { yst with memory :=
            storeWord (storeWord yst.memory Wcell (W 0)) Icell (W (i + 1)) } with hyst1
      have hfrW : BEF { yst with memory := storeWord yst.memory Wcell (W 0) } cd :=
        bef_store (c := Wcell) (by decide) hinv.fr
      have hpx : ePfx cd (i + 1) = ePfx cd i := by rw [ePfx_succ, hpfx, hz]
      have hinv1 : BE yst1 cd (i + 1) := by
        refine ⟨bef_store (c := Icell) (by decide) hfrW, ?_, ?_⟩
        · show loadWord (storeWord (storeWord yst.memory Wcell (W 0)) Icell
              (W (i + 1))) Icell = W (i + 1)
          rw [loadWord_storeWord_self]
        · rw [hpx]
          exact RepresentsY_storeWord_disjoint
            (RepresentsY_storeWord_disjoint hinv.accrep (by omega)) (by omega)
      have hpfx1 : ePfx cd (i + 1) = 0 := by rw [ePfx_succ, hpfx, hz]
      rcases ih (i + 1) (by omega) yst1 hinv1 hpfx1 with ⟨yst', i0, hfnd, hsteps2⟩ |
        ⟨yst', hBEe, hsteps2⟩
      · exact Or.inl ⟨yst', i0, hfnd, hsteps.trans hsteps2⟩
      · exact Or.inr ⟨yst', hBEe, hsteps.trans hsteps2⟩
    


/-- A framed scalar cell (between `BS` and `I2`) survives the seed copy
loop. -/
theorem cp_keeps_cell {M M' : Nat → UInt8} {n c : Nat}
    (hk : ∀ a, (a < ACC ∨ ACC + 32 * n ≤ a) → (a < I2 ∨ I2 + 32 ≤ a) → M' a = M a)
    (hn : n ≤ 32) (hc : BS ≤ c ∧ c + 32 ≤ I2) :
    loadWord M' c = loadWord M c := by
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hI2v : (I2 : Nat) = 7776 := rfl
  have hBSv : (BS : Nat) = 7168 := rfl
  apply loadWord_congr
  intro a ha1 ha2
  exact hk a (by omega) (by omega)

/-- A limb region ending below `ACC` survives the seed copy loop. -/
theorem cp_keeps_rep {M M' : Nat → UInt8} {n R v : Nat}
    (hk : ∀ a, (a < ACC ∨ ACC + 32 * n ≤ a) → (a < I2 ∨ I2 + 32 ≤ a) → M' a = M a)
    (hn : n ≤ 32) (hR : R + 32 * n ≤ ACC)
    (h : RepresentsY M R n v) : RepresentsY M' R n v := by
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hI2v : (I2 : Nat) = 7776 := rfl
  refine ⟨h.1, ?_⟩
  rw [yLimbs_congr (mem := M') (mem' := M) ?_, h.2]
  intro a ha1 ha2
  exact hk a (by omega) (by omega)

/-- At the top-bits loop head: `Jcell = jt` with `jt` pending bits of the
seed byte `eByte cd i0` (its top set bit at `jt`), and `ACC` holding the
corresponding prefix power. -/
structure BETop (yst : EvmState) (cd : ByteArray) (i0 jt : Nat) : Prop where
  fr : BEF yst cd
  icell : loadWord yst.memory Icell = W i0
  wcell : loadWord yst.memory Wcell = W (eByte cd i0)
  jcell : loadWord yst.memory Jcell = W jt
  jt7 : jt ≤ 7
  i0lt : i0 < exponentSize cd
  pfx0 : ePfx cd i0 = 0
  accrep : RepresentsY yst.memory ACC (nlimbs cd)
    (bVal cd ^ (eByte cd i0 / 2 ^ jt) % modVal cd)

/-- From the found state through the top-bit scan and the accumulator seed:
land at the top-bits loop head with `Jcell` at the seed byte's top set bit
and `ACC` seeded with the reduced base (`b ^ 1 % m`). -/
theorem exp_found {cd : ByteArray} (hv : ValidInput cd)
    (hmspos : 0 < modulusSize cd) (hm0 : modVal cd ≠ 0)
    {i0 : Nat} {yst : EvmState} (hf : BEFnd yst cd i0) :
    ∃ yst' jt, BETop yst' cd i0 jt ∧
      ASteps programAsm ⟨store Jcell (.imm 7) ++ ([.label programLabels.lbTop] ++
        (beTopBody ++ beSer)), [], yst⟩
        ⟨beTopBitsBody ++ beSer, [], yst'⟩ := by
  have hn0 : 0 < nlimbs cd := limbCount_pos hmspos
  have hn32 := hf.fr.hn32
  have hw256 : eByte cd i0 < 256 := eByte_lt cd i0
  have hw0 : eByte cd i0 ≠ 0 := hf.wne
  set w := eByte cd i0 with hwdef
  -- Jcell := 7, then the label
  have hsJ : ASteps programAsm ⟨store Jcell (.imm 7) ++ ([.label programLabels.lbTop] ++
        (beTopBody ++ beSer)), [], yst⟩
      ⟨beTopBody ++ beSer, [],
        { yst with memory := storeWord yst.memory Jcell (W 7) }⟩ :=
    (store_pin (c := Jcell) (e := .imm 7) (v := W 7)
      (k := [.label programLabels.lbTop] ++ (beTopBody ++ beSer))
      (yst := yst) (by trivial) (by decide)
      (by rw [hf.fr.aw]; show Jcell + 32 ≤ 32 * 250; decide) rfl).trans
    (label_steps (model := localModel) (σ := ([] : List AVal)))
  set y7 : EvmState := { yst with memory := storeWord yst.memory Jcell (W 7) } with hy7
  -- the top-bit scan
  have htop : ∀ (jt : Nat), jt ≤ 7 → ∀ (y2 : EvmState),
      (BEF y2 cd ∧ loadWord y2.memory Icell = W i0 ∧
        loadWord y2.memory Wcell = W w ∧ loadWord y2.memory Jcell = W jt ∧
        w ≠ 0 ∧ w < 2 ^ (jt + 1)) →
      ∃ y3 jt', (BEF y3 cd ∧ loadWord y3.memory Icell = W i0 ∧
        loadWord y3.memory Wcell = W w ∧ loadWord y3.memory Jcell = W jt' ∧
        (w / 2 ^ jt') % 2 = 1 ∧ w < 2 ^ (jt' + 1) ∧ jt' ≤ 7) ∧
        ASteps programAsm ⟨beTopBody ++ beSer, [], y2⟩
          ⟨store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
            (beSeedBody ++ beSer)), [], y3⟩ := by
    intro jt
    induction jt using Nat.strong_induction_on with
    | _ jt ih =>
      intro hle y2 ⟨hf2, hIy, hWy, hJy, hw0y, hwlt⟩
      have hbitv : evalExpr bitTest y2 = W ((w / 2 ^ jt) % 2) :=
        evalExpr_bitTest hWy hJy (by omega) (by omega)
      have hok : exprOK bitTest y2 :=
        ⟨rfl, ⟨rfl, pin250 hf2.aw (by decide), pin250 hf2.aw (by decide)⟩, trivial⟩
      have hopen : beTopBody ++ beSer =
          jumpIfNz bitTest programLabels.lbInitAcc ++
          (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
          ([.jump programLabels.lbTop] ++ ([.label programLabels.lbInitAcc] ++
          (store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
            (beSeedBody ++ beSer)))))) := by
        rw [beTopBody]; simp only [List.append_assoc]
      by_cases hbit : (w / 2 ^ jt) % 2 = 1
      · refine ⟨y2, jt, ⟨hf2, hIy, hWy, hJy, hbit, hwlt, hle⟩, ?_⟩
        rw [hopen]
        exact jumpIfNz_taken (model := localModel) (prog := programAsm)
          (e := bitTest) (l := programLabels.lbInitAcc)
          (c' := store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
            (beSeedBody ++ beSer)))
          (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
            ([.jump programLabels.lbTop] ++ ([.label programLabels.lbInitAcc] ++
            (store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
              (beSeedBody ++ beSer))))))
          (σ := ([] : List AVal)) hok
          (by rw [hbitv, hbit]; exact W_ne_zero one_ne_zero (by norm_num))
          findLbInitAcc
      · have hbit0 : (w / 2 ^ jt) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ jt) with h | h
          · exact h
          · omega
        have hjt0 : 0 < jt := by
          by_cases hz : jt = 0
          · exfalso
            subst hz
            rw [show (2 : Nat) ^ (0 + 1) = 2 from by norm_num] at hwlt
            rw [Nat.pow_zero, Nat.div_one] at hbit0
            omega
          · omega
        have hp2 : (2 : Nat) ^ (jt + 1) = 2 ^ jt * 2 := by rw [Nat.pow_succ]
        rw [hp2] at hwlt
        have hd0 : w / 2 ^ jt = 0 := by
          rcases Nat.lt_or_ge w (2 ^ jt) with h | h
          · exact Nat.div_eq_of_lt h
          · exfalso
            have h1 : w / 2 ^ jt < 2 :=
              (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))).mpr (by omega)
            have h2 : 1 ≤ w / 2 ^ jt :=
              (Nat.one_le_div_iff (Nat.pow_pos (by norm_num))).mpr h
            have h3 : w / 2 ^ jt = 1 := by omega
            rw [h3] at hbit0
            omega
        have hval : evalExpr (.bin .sub (.load Jcell) (.imm 1)) y2 = W (jt - 1) := by
          show loadWord y2.memory Jcell - W 1 = _
          rw [hJy]
          exact W_sub (by omega : (1 : Nat) ≤ jt) (by omega : jt < 2 ^ 256)
        have hfallbit : evalExpr bitTest y2 = 0 := by
          rw [hbitv, hbit0]
          rfl
        have hs : ASteps programAsm ⟨beTopBody ++ beSer, [], y2⟩
            ⟨[.jump programLabels.lbTop] ++ ([.label programLabels.lbInitAcc] ++
              (store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
                (beSeedBody ++ beSer)))), [],
              { y2 with memory := storeWord y2.memory Jcell (W (jt - 1)) }⟩ := by
          rw [hopen]
          exact (jumpIfNz_fall (model := localModel) (prog := programAsm)
              (e := bitTest) (l := programLabels.lbInitAcc)
              (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
                ([.jump programLabels.lbTop] ++ ([.label programLabels.lbInitAcc] ++
                (store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
                  (beSeedBody ++ beSer))))))
              (σ := ([] : List AVal)) hok hfallbit).trans
            (store_pin (c := Jcell) (e := .bin .sub (.load Jcell) (.imm 1))
              (v := W (jt - 1))
              (k := [.jump programLabels.lbTop] ++ ([.label programLabels.lbInitAcc] ++
                (store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
                  (beSeedBody ++ beSer)))))
              (yst := y2)
              (by
                show binOK YulSemantics.EVM.Op.sub = true ∧
                  exprOK (Expr.load Jcell) y2 ∧ exprOK (Expr.imm 1) y2
                exact ⟨rfl, pin250 hf2.aw (by decide), trivial⟩)
              (by decide) (by rw [hf2.aw]; show Jcell + 32 ≤ 32 * 250; decide)
              hval)
        have hwlt' : w < 2 ^ (jt - 1 + 1) := by
          rw [show jt - 1 + 1 = jt from by omega]
          have hpw : (0 : Nat) < 2 ^ jt := Nat.pow_pos (by norm_num)
          rcases Nat.div_eq_zero_iff.mp hd0 with h1 | h2 <;> omega
        have hfr3 : BEF { y2 with memory := storeWord y2.memory Jcell (W (jt - 1)) } cd :=
          bef_store (c := Jcell) (by decide) hf2
        have hI3 : loadWord (storeWord y2.memory Jcell (W (jt - 1))) Icell = W i0 := by
          rw [load_disj' y2.memory Jcell Icell (W (jt - 1)) (Or.inr (by
            have hJcv : (Jcell : Nat) = 7424 := rfl
            have hIcv : (Icell : Nat) = 7392 := rfl
            omega))]
          exact hIy
        have hW3 : loadWord (storeWord y2.memory Jcell (W (jt - 1))) Wcell = W w := by
          rw [load_disj' y2.memory Jcell Wcell (W (jt - 1)) (Or.inl (by
            have hJcv : (Jcell : Nat) = 7424 := rfl
            have hWcv : (Wcell : Nat) = 7456 := rfl
            omega))]
          exact hWy
        have hJ3 : loadWord (storeWord y2.memory Jcell (W (jt - 1))) Jcell = W (jt - 1) :=
          loadWord_storeWord_self _ _ _
        obtain ⟨y4, jt'', hinv4, hsteps4⟩ := ih (jt - 1) (by omega) (by omega)
          { y2 with memory := storeWord y2.memory Jcell (W (jt - 1)) }
          ⟨hfr3, hI3, hW3, hJ3, hw0y, hwlt'⟩
        exact ⟨y4, jt'', hinv4,
          (hs.trans (jump_steps (model := localModel) findLbTop)).trans hsteps4⟩
  have hfr7 : BEF y7 cd := bef_store (c := Jcell) (by decide) hf.fr
  have hI7 : loadWord (storeWord yst.memory Jcell (W 7)) Icell = W i0 := by
    rw [load_disj' yst.memory Jcell Icell (W 7) (Or.inr (by
      have hJcv : (Jcell : Nat) = 7424 := rfl
      have hIcv : (Icell : Nat) = 7392 := rfl
      omega))]
    exact hf.icell
  have hW7 : loadWord (storeWord yst.memory Jcell (W 7)) Wcell = W w := by
    rw [load_disj' yst.memory Jcell Wcell (W 7) (Or.inl (by
      have hJcv : (Jcell : Nat) = 7424 := rfl
      have hWcv : (Wcell : Nat) = 7456 := rfl
      omega))]
    exact hf.wcell
  have hJ7 : loadWord (storeWord yst.memory Jcell (W 7)) Jcell = W 7 :=
    loadWord_storeWord_self _ _ _
  have hwlt7 : w < 2 ^ (7 + 1) := by
    rw [show (2 : Nat) ^ (7 + 1) = 256 from by norm_num]
    omega
  obtain ⟨y2, jt', hinv2, hsteps2⟩ := htop 7 (by omega) y7
    ⟨hfr7, hI7, hW7, hJ7, hw0, hwlt7⟩
  obtain ⟨hf2, hI2y, hW2y, hJ2y, hbit', hwlt', hjt7⟩ := hinv2
  -- store I2 0, then the label, to the copy loop top
  have hsI2 : ASteps programAsm ⟨store I2 (.imm 0) ++ ([.label programLabels.lbAccInit] ++
        (beSeedBody ++ beSer)), [], y2⟩
      ⟨beSeedBody ++ beSer, [],
        { y2 with memory := storeWord y2.memory I2 (W 0) }⟩ :=
    (store_pin (c := I2) (e := .imm 0) (v := W 0)
      (k := [.label programLabels.lbAccInit] ++ (beSeedBody ++ beSer)) (yst := y2)
      (by trivial) (by decide)
      (by rw [hf2.aw]; show I2 + 32 ≤ 32 * 250; decide) rfl).trans
    (label_steps (model := localModel) (σ := ([] : List AVal)))
  set y8 : EvmState := { y2 with memory := storeWord y2.memory I2 (W 0) } with hy8
  have hfr8 : BEF y8 cd := bef_store (c := I2) (by decide) hf2
  have haw8 : 0x1f40 ≤ 32 * y8.activeWords.toNat := by
    have h := hfr8.aw
    omega
  have hI2v : (I2 : Nat) = 7776 := rfl
  have hIcv : (Icell : Nat) = 7392 := rfl
  have hJcv : (Jcell : Nat) = 7424 := rfl
  have hWcv : (Wcell : Nat) = 7456 := rfl
  have hnl : nlimbs cd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt hn32 (by norm_num : (32 : Nat) < 2 ^ 256)
  have hNcv : (Ncell : Nat) = 7360 := rfl
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hBASEv : (BASE : Nat) = 1024 := rfl
  have hMODv : (MOD : Nat) = 0 := rfl
  have hN2cell : (loadWord y8.memory Ncell).toNat = nlimbs cd := by
    show (loadWord (storeWord y2.memory I2 (W 0)) Ncell).toNat = nlimbs cd
    rw [load_disj' y2.memory I2 Ncell (W 0) (Or.inr (by omega)), hf2.ncell,
      toNat_W hnl]
  have hI2z : (loadWord y8.memory I2).toNat = 0 := by
    show (loadWord (storeWord y2.memory I2 (W 0)) I2).toNat = 0
    rw [loadWord_storeWord_self, toNat_W (by norm_num)]
  -- the seed copy loop
  obtain ⟨y9, hcopy, hdst9, hN9, hsrc9, hkeep9, haw9, henv9⟩ :=
    mulCopyLoop_steps (model := localModel) (prog := programAsm)
      (dstBase := ACC) (srcBase := BASE) (l := seedLabels)
      (xs := yLimbs y8.memory BASE (nlimbs cd))
      (out₀ := yLimbs y8.memory ACC (nlimbs cd))
      (n := nlimbs cd) (lExit := programLabels.lbAccInitDone)
      (c' := [.label programLabels.lbTopBits] ++ (beTopBitsBody ++ beSer))
      (k := [.label programLabels.lbAccInitDone] ++
        ([.label programLabels.lbTopBits] ++ (beTopBitsBody ++ beSer)))
      (σ := ([] : List AVal)) (S := y8)
      findSeedCopy findLbAccInitDone haw8 hn0 hn32
      (by omega) (by omega) (by omega) hN2cell hI2z rfl rfl
      (length_yLimbs _ _ _) (length_yLimbs _ _ _) (fun d hd => yLimb_lt hd)
  have hlabT : ASteps programAsm ⟨[.label programLabels.lbTopBits] ++
        (beTopBitsBody ++ beSer), [], y9⟩
      ⟨beTopBitsBody ++ beSer, [], y9⟩ :=
    label_steps (model := localModel) (σ := ([] : List AVal))
  -- the state after the copy
  have hfr9 : BEF y9 cd := by
    refine ⟨by rw [haw9]; exact hfr8.aw, by rw [henv9]; exact hfr8.env,
      (cp_keeps_cell hkeep9 hn32 (c := ES) (by decide)).trans hfr8.escell,
      (cp_keeps_cell hkeep9 hn32 (c := EO) (by decide)).trans hfr8.eocell,
      (cp_keeps_cell hkeep9 hn32 (c := Ncell) (by decide)).trans hfr8.ncell,
      (cp_keeps_cell hkeep9 hn32 (c := MS) (by decide)).trans hfr8.mscell,
      cp_keeps_rep hkeep9 hn32 (by omega) hfr8.modrep,
      cp_keeps_rep hkeep9 hn32 (by omega) hfr8.baserep,
      hn32⟩
  have hIcell9 : loadWord y9.memory Icell = W i0 :=
    (cp_keeps_cell hkeep9 hn32 (c := Icell) (by decide)).trans
      (by show loadWord (storeWord y2.memory I2 (W 0)) Icell = W i0
          rw [load_disj' y2.memory I2 Icell (W 0) (Or.inr (by omega))]
          exact hI2y)
  have hWcell9 : loadWord y9.memory Wcell = W w :=
    (cp_keeps_cell hkeep9 hn32 (c := Wcell) (by decide)).trans
      (by show loadWord (storeWord y2.memory I2 (W 0)) Wcell = W w
          rw [load_disj' y2.memory I2 Wcell (W 0) (Or.inr (by omega))]
          exact hW2y)
  have hJcell9 : loadWord y9.memory Jcell = W jt' :=
    (cp_keeps_cell hkeep9 hn32 (c := Jcell) (by decide)).trans
      (by show loadWord (storeWord y2.memory I2 (W 0)) Jcell = W jt'
          rw [load_disj' y2.memory I2 Jcell (W 0) (Or.inr (by omega))]
          exact hJ2y)
  -- at the top bit, the pending quotient is exactly one
  have hwtop : w / 2 ^ jt' = 1 := by
    have hpos : (0 : Nat) < 2 ^ jt' := Nat.pow_pos (by norm_num)
    rw [show (2 : Nat) ^ (jt' + 1) = 2 ^ jt' * 2 from by rw [Nat.pow_succ]] at hwlt'
    have hlt2 : w / 2 ^ jt' < 2 :=
      (Nat.div_lt_iff_lt_mul hpos).mpr (by omega : w < 2 * 2 ^ jt')
    rcases Nat.eq_zero_or_pos (w / 2 ^ jt') with h | h
    · rw [h, Nat.zero_mod] at hbit'
      omega
    · omega
  refine ⟨y9, jt', ⟨hfr9, hIcell9, hWcell9, hJcell9, hjt7, hf.i0lt, hf.pfx0, ?_⟩,
    ((hsJ.trans hsteps2).trans hsI2).trans (hcopy.trans hlabT)⟩
  show RepresentsY y9.memory ACC (nlimbs cd)
    (bVal cd ^ (eByte cd i0 / 2 ^ jt') % modVal cd)
  rw [← hwdef, hwtop, Nat.pow_one]
  exact ⟨hfr8.baserep.1, hdst9.trans hfr8.baserep.2⟩

/-- At the bytes loop head: `Icell = i` bytes consumed, `ACC` holding the
corresponding prefix power. -/
structure BEBytes (yst : EvmState) (cd : ByteArray) (i : Nat) : Prop where
  fr : BEF yst cd
  icell : loadWord yst.memory Icell = W i
  accrep : RepresentsY yst.memory ACC (nlimbs cd)
    (bVal cd ^ ePfx cd i % modVal cd)

/-- The squaring call (`bptr = ACC`) at a bit round: from the call site to
its continuation, with `ACC` squared and the frame plus loop cells kept. -/
theorem mm_sq {cd : ByteArray} {yst : EvmState} {x : Nat} {lret : Nat} {cont : List Asm}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : 0 < modVal cd)
    (hf : BEF yst cd) (hacc : RepresentsY yst.memory ACC (nlimbs cd) x)
    (hx : x < modVal cd)
    (hfindRet : findLabel lret programAsm = some cont)
    (hmem : lret ∈ labelDefs programAsm) :
    ∃ yst', (ASteps programAsm
        ⟨callMulMod ACC lret programLabels.lmmEntry ++ cont, [], yst⟩
        ⟨cont, [], yst'⟩ ∧
      RepresentsY yst'.memory ACC (nlimbs cd) ((x * x) % modVal cd) ∧
      BEF yst' cd ∧
      (∀ c, BS ≤ c → c + 32 ≤ C1 → loadWord yst'.memory c = loadWord yst.memory c) ∧
      (loadWord yst'.memory Ncell).toNat = nlimbs cd) := by
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hOUTv : (OUT : Nat) = 3072 := rfl
  have hSUBCv : (SUBC : Nat) = 5120 := rfl
  have hNcv : (Ncell : Nat) = 7360 := rfl
  have hnl : nlimbs cd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt hn32 (by norm_num : (32 : Nat) < 2 ^ 256)
  have hN : (loadWord yst.memory Ncell).toNat = nlimbs cd := by
    rw [hf.ncell, toNat_W hnl]
  have haw : 0x1f40 ≤ 32 * yst.activeWords.toNat := by
    have h := hf.aw
    omega
  obtain ⟨yst', hsteps, hacc', hN', hkeeps', haw', henv'⟩ :=
    mulModCall_correct (spec := theAddModSpec) (bptr := ACC) (lret := lret)
      (n := nlimbs cd) (m := modVal cd) (a := x) (b := x) (cont := cont)
      (σ := ([] : List AVal)) (yst := yst)
      hfindRet hmem findLmmEntry hn0 hn32
      (by omega) (by omega) (Or.inr (Or.inr rfl)) (by omega)
      haw hN hf.modrep hm0 hacc hx hacc
  refine ⟨yst', ⟨hsteps, hacc', bef_mm_keeps hkeeps' haw' henv' hf, ?_, hN'⟩⟩
  intro c hc1 hc2
  exact mm_keeps_cell hkeeps' hn32 ⟨hc1, hc2⟩

/-- The base-multiply call (`bptr = BASE`) at a bit round. -/
theorem mm_mul {cd : ByteArray} {yst : EvmState} {a : Nat} {lret : Nat} {cont : List Asm}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : 0 < modVal cd)
    (hf : BEF yst cd) (hacc : RepresentsY yst.memory ACC (nlimbs cd) a)
    (ha : a < modVal cd)
    (hfindRet : findLabel lret programAsm = some cont)
    (hmem : lret ∈ labelDefs programAsm) :
    ∃ yst', (ASteps programAsm
        ⟨callMulMod BASE lret programLabels.lmmEntry ++ cont, [], yst⟩
        ⟨cont, [], yst'⟩ ∧
      RepresentsY yst'.memory ACC (nlimbs cd)
        ((a * (bVal cd % modVal cd)) % modVal cd) ∧
      BEF yst' cd ∧
      (∀ c, BS ≤ c → c + 32 ≤ C1 → loadWord yst'.memory c = loadWord yst.memory c) ∧
      (loadWord yst'.memory Ncell).toNat = nlimbs cd) := by
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hBASEv : (BASE : Nat) = 1024 := rfl
  have hOUTv : (OUT : Nat) = 3072 := rfl
  have hSUBCv : (SUBC : Nat) = 5120 := rfl
  have hNcv : (Ncell : Nat) = 7360 := rfl
  have hnl : nlimbs cd < 2 ^ 256 :=
    Nat.lt_of_le_of_lt hn32 (by norm_num : (32 : Nat) < 2 ^ 256)
  have hN : (loadWord yst.memory Ncell).toNat = nlimbs cd := by
    rw [hf.ncell, toNat_W hnl]
  have haw : 0x1f40 ≤ 32 * yst.activeWords.toNat := by
    have h := hf.aw
    omega
  obtain ⟨yst', hsteps, hacc', hN', hkeeps', haw', henv'⟩ :=
    mulModCall_correct (spec := theAddModSpec) (bptr := BASE) (lret := lret)
      (n := nlimbs cd) (m := modVal cd) (a := a) (b := bVal cd % modVal cd)
      (cont := cont) (σ := ([] : List AVal)) (yst := yst)
      hfindRet hmem findLmmEntry hn0 hn32
      (by omega) (by omega) (Or.inl (by omega)) (by omega)
      haw hN hf.modrep hm0 hacc ha hf.baserep
  refine ⟨yst', ⟨hsteps, hacc', bef_mm_keeps hkeeps' haw' henv' hf, ?_, hN'⟩⟩
  intro c hc1 hc2
  exact mm_keeps_cell hkeeps' hn32 ⟨hc1, hc2⟩

/-- One top-bits round: decrement `Jcell`, square `ACC`, and conditionally
multiply by `BASE` — moving the pending quotient one bit down. -/
theorem exp_topbits_round {cd : ByteArray} {i0 r : Nat} {yst : EvmState}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : modVal cd ≠ 0)
    (hr : 0 < r) (hinv : BETop yst cd i0 r) :
    ∃ yst', BETop yst' cd i0 (r - 1) ∧
      ASteps programAsm ⟨beTopBitsBody ++ beSer, [], yst⟩
        ⟨beTopBitsBody ++ beSer, [], yst'⟩ := by
  have hm0pos : 0 < modVal cd := Nat.pos_of_ne_zero hm0
  have hf := hinv.fr
  set w := eByte cd i0 with hwdef
  have hw256 : w < 256 := eByte_lt cd i0
  set x := bVal cd ^ (w / 2 ^ r) % modVal cd with hxdef
  have hxl : x < modVal cd := Nat.mod_lt _ hm0pos
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hJcv : (Jcell : Nat) = 7424 := rfl
  have hIcv : (Icell : Nat) = 7392 := rfl
  have hWcv : (Wcell : Nat) = 7456 := rfl
  have hopen : beTopBitsBody ++ beSer =
      jumpIfZ (.load Jcell) programLabels.lbRest ++
      (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      (callMulMod ACC programLabels.lsqRet1 programLabels.lmmEntry ++
      (jumpIfZ bitTest programLabels.lbTopBitsSkip ++
      (callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
      ([.label programLabels.lbTopBitsSkip] ++
      ([.jump programLabels.lbTopBits] ++
      ([.label programLabels.lbRest] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))))))) := by
    rw [beTopBitsBody]; simp only [List.append_assoc]
  rw [hopen]
  -- step 1: fall the counter test
  have hjt7 := hinv.jt7
  have hfall : evalExpr (.load Jcell) yst ≠ 0 := by
    show loadWord yst.memory Jcell ≠ 0
    rw [hinv.jcell]
    exact W_ne_zero (by omega) (by omega)
  have s1 := jumpIfZ_fall (model := localModel) (prog := programAsm)
    (e := .load Jcell) (l := programLabels.lbRest)
    (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      (callMulMod ACC programLabels.lsqRet1 programLabels.lmmEntry ++
      (jumpIfZ bitTest programLabels.lbTopBitsSkip ++
      (callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
      ([.label programLabels.lbTopBitsSkip] ++
      ([.jump programLabels.lbTopBits] ++
      ([.label programLabels.lbRest] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer))))))))))
    (σ := ([] : List AVal)) (pin250 hf.aw (by decide)) hfall
  -- step 2: Jcell := r - 1
  have hval : evalExpr (.bin .sub (.load Jcell) (.imm 1)) yst = W (r - 1) := by
    show loadWord yst.memory Jcell - W 1 = _
    rw [hinv.jcell]
    exact W_sub (by omega : (1 : Nat) ≤ r) (by omega : r < 2 ^ 256)
  have s2 := store_pin (c := Jcell) (e := .bin .sub (.load Jcell) (.imm 1))
    (v := W (r - 1))
    (k := callMulMod ACC programLabels.lsqRet1 programLabels.lmmEntry ++
      (jumpIfZ bitTest programLabels.lbTopBitsSkip ++
      (callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
      ([.label programLabels.lbTopBitsSkip] ++
      ([.jump programLabels.lbTopBits] ++
      ([.label programLabels.lbRest] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))))))
    (yst := yst)
    (by
      show binOK YulSemantics.EVM.Op.sub = true ∧
        exprOK (Expr.load Jcell) yst ∧ exprOK (Expr.imm 1) yst
      exact ⟨rfl, pin250 hf.aw (by decide), trivial⟩)
    (by decide) (by rw [hf.aw]; show Jcell + 32 ≤ 32 * 250; decide) hval
  set yJ : EvmState := { yst with memory := storeWord yst.memory Jcell (W (r - 1)) } with hyJ
  have hfrJ : BEF yJ cd := bef_store (c := Jcell) (by decide) hf
  have haccJ : RepresentsY yJ.memory ACC (nlimbs cd)
      (bVal cd ^ (w / 2 ^ r) % modVal cd) :=
    RepresentsY_storeWord_disjoint hinv.accrep (by omega)
  have hicJ : loadWord yJ.memory Icell = W i0 := by
    show loadWord (storeWord yst.memory Jcell (W (r - 1))) Icell = W i0
    rw [load_disj' yst.memory Jcell Icell (W (r - 1)) (Or.inr (by omega))]
    exact hinv.icell
  have hwJ : loadWord yJ.memory Wcell = W w := by
    show loadWord (storeWord yst.memory Jcell (W (r - 1))) Wcell = W w
    rw [load_disj' yst.memory Jcell Wcell (W (r - 1)) (Or.inl (by omega))]
    exact hinv.wcell
  have hjJ : loadWord yJ.memory Jcell = W (r - 1) := loadWord_storeWord_self _ _ _
  -- step 3: the squaring call
  obtain ⟨yQ, hsq, haccQ, hfrQ, hcellQ, hNQ⟩ :=
    mm_sq hn0 hn32 hm0pos hfrJ haccJ hxl findLsqRet1 memLsqRet1
  have hicQ : loadWord yQ.memory Icell = W i0 :=
    (hcellQ Icell (by decide) (by decide)).trans hicJ
  have hwQ : loadWord yQ.memory Wcell = W w :=
    (hcellQ Wcell (by decide) (by decide)).trans hwJ
  have hjQ : loadWord yQ.memory Jcell = W (r - 1) :=
    (hcellQ Jcell (by decide) (by decide)).trans hjJ
  have hbit : evalExpr bitTest yQ = W ((w / 2 ^ (r - 1)) % 2) :=
    evalExpr_bitTest hwQ hjQ (by omega) (by omega)
  have hok : exprOK bitTest yQ :=
    ⟨rfl, ⟨rfl, pin250 hfrQ.aw (by decide), pin250 hfrQ.aw (by decide)⟩, trivial⟩
  have hsqm : (x * x) % modVal cd = bVal cd ^ (2 * (w / 2 ^ r)) % modVal cd :=
    be_sq_mod (b := bVal cd) (E := w / 2 ^ r) (m := modVal cd) (x := x) rfl
  by_cases hb : (w / 2 ^ (r - 1)) % 2 = 1
  · -- multiply by the base, then loop
    have hfall2 : evalExpr bitTest yQ ≠ 0 := by
      rw [hbit, hb]
      exact W_ne_zero one_ne_zero (by norm_num)
    have s3 := jumpIfZ_fall (model := localModel) (prog := programAsm)
      (e := bitTest) (l := programLabels.lbTopBitsSkip)
      (k := callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
        ([.label programLabels.lbTopBitsSkip] ++
        ([.jump programLabels.lbTopBits] ++
        ([.label programLabels.lbRest] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))))
      (σ := ([] : List AVal)) hok hfall2
    obtain ⟨yM, hmul, haccM, hfrM, hcellM, hNM⟩ :=
      mm_mul hn0 hn32 hm0pos hfrQ haccQ (Nat.mod_lt _ hm0pos) findLmulRet1 memLmulRet1
    have hlab : ASteps programAsm
        ⟨[.label programLabels.lbTopBitsSkip] ++ ([.jump programLabels.lbTopBits] ++
          ([.label programLabels.lbRest] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer))))), [], yM⟩
        ⟨[.jump programLabels.lbTopBits] ++ ([.label programLabels.lbRest] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))), [], yM⟩ :=
      label_steps (model := localModel) (σ := ([] : List AVal))
    have hjmp : ASteps programAsm
        ⟨[.jump programLabels.lbTopBits] ++ ([.label programLabels.lbRest] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))), [], yM⟩
        ⟨beTopBitsBody ++ beSer, [], yM⟩ :=
      jump_steps (model := localModel) (σ := ([] : List AVal)) findLbTopBits
    have hval2 : bVal cd ^ (w / 2 ^ (r - 1)) % modVal cd
        = ((x * x) % modVal cd * (bVal cd % modVal cd)) % modVal cd := by
      have hmulm : ((x * x) % modVal cd * (bVal cd % modVal cd)) % modVal cd
          = bVal cd ^ (2 * (w / 2 ^ r) + 1) % modVal cd :=
        be_mulbase_mod (b := bVal cd) (E := 2 * (w / 2 ^ r)) (m := modVal cd)
          (x := (x * x) % modVal cd) (t := bVal cd % modVal cd) hsqm rfl
      have hdd := be_div_step w r hr
      rw [hb] at hdd
      rw [← hdd] at hmulm
      exact hmulm.symm
    refine ⟨yM, ⟨hfrM, (hcellM Icell (by decide) (by decide)).trans hicQ,
      (hcellM Wcell (by decide) (by decide)).trans hwQ,
      (hcellM Jcell (by decide) (by decide)).trans hjQ,
      by omega, hinv.i0lt, hinv.pfx0, ?_⟩,
      (((s1.trans s2).trans hsq).trans s3).trans (hmul.trans (hlab.trans hjmp))⟩
    show RepresentsY yM.memory ACC (nlimbs cd)
      (bVal cd ^ (eByte cd i0 / 2 ^ (r - 1)) % modVal cd)
    rw [← hwdef, hval2]
    exact haccM
  · -- bit clear: skip the multiply, loop
    have hzero2 : evalExpr bitTest yQ = 0 := by
      rw [hbit]
      rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ (r - 1)) with h | h
      · rw [h]; rfl
      · exact absurd h hb
    have s3 := jumpIfZ_taken (model := localModel) (prog := programAsm)
      (e := bitTest) (l := programLabels.lbTopBitsSkip)
      (c' := [.jump programLabels.lbTopBits] ++ ([.label programLabels.lbRest] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))
      (k := callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
        ([.label programLabels.lbTopBitsSkip] ++
        ([.jump programLabels.lbTopBits] ++
        ([.label programLabels.lbRest] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))))
      (σ := ([] : List AVal)) hok hzero2 findLbTopBitsSkip
    have hjmp : ASteps programAsm
        ⟨[.jump programLabels.lbTopBits] ++ ([.label programLabels.lbRest] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))), [], yQ⟩
        ⟨beTopBitsBody ++ beSer, [], yQ⟩ :=
      jump_steps (model := localModel) (σ := ([] : List AVal)) findLbTopBits
    have hb0 : (w / 2 ^ (r - 1)) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ (r - 1)) with h | h
      · exact h
      · exact absurd h hb
    have hdd := be_div_step w r hr
    rw [hb0] at hdd
    refine ⟨yQ, ⟨hfrQ, hicQ, hwQ, hjQ, by omega, hinv.i0lt, hinv.pfx0, ?_⟩,
      ((s1.trans s2).trans hsq).trans (s3.trans hjmp)⟩
    show RepresentsY yQ.memory ACC (nlimbs cd)
      (bVal cd ^ (eByte cd i0 / 2 ^ (r - 1)) % modVal cd)
    rw [← hwdef, hdd, Nat.add_zero, ← hsqm]
    exact haccQ

/-- The top-bits loop: from the entry invariant down to `Jcell = 0`, landing
at the bytes loop head with the whole seed byte consumed. -/
theorem exp_topbits {cd : ByteArray} (hv : ValidInput cd) {i0 jt : Nat} {yst : EvmState}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : modVal cd ≠ 0)
    (hinv : BETop yst cd i0 jt) :
    ∃ yst', BEBytes yst' cd (i0 + 1) ∧
      ASteps programAsm ⟨beTopBitsBody ++ beSer, [], yst⟩
        ⟨beBytesBody ++ beSer, [], yst'⟩ := by
  have hes1024 : exponentSize cd ≤ 1024 := by
    obtain ⟨-, -, he, -⟩ := hv
    exact he
  -- the exit: the counter test jumps to the `lbRest` landing, state unchanged
  have hexit : ∀ yst2 : EvmState, (0 ≤ jt ∧ BETop yst2 cd i0 0) →
      BETop yst2 cd i0 0 ∧
        ASteps programAsm ⟨beTopBitsBody ++ beSer, [], yst2⟩
          ⟨store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)), [], yst2⟩ := by
    intro yst2 hpair
    obtain ⟨_, hinv2⟩ := hpair
    have hf2 := hinv2.fr
    have hz : evalExpr (.load Jcell) yst2 = 0 := by
      show loadWord yst2.memory Jcell = 0
      rw [hinv2.jcell]
      rfl
    refine ⟨hinv2, ?_⟩
    rw [show beTopBitsBody ++ beSer =
        jumpIfZ (.load Jcell) programLabels.lbRest ++
        (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callMulMod ACC programLabels.lsqRet1 programLabels.lmmEntry ++
        (jumpIfZ bitTest programLabels.lbTopBitsSkip ++
        (callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
        ([.label programLabels.lbTopBitsSkip] ++
        ([.jump programLabels.lbTopBits] ++
        ([.label programLabels.lbRest] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))))))))) from by
      rw [beTopBitsBody]; simp only [List.append_assoc]]
    exact jumpIfZ_taken (model := localModel) (prog := programAsm)
      (e := .load Jcell) (l := programLabels.lbRest)
      (c' := store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))
      (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callMulMod ACC programLabels.lsqRet1 programLabels.lmmEntry ++
        (jumpIfZ bitTest programLabels.lbTopBitsSkip ++
        (callMulMod BASE programLabels.lmulRet1 programLabels.lmmEntry ++
        ([.label programLabels.lbTopBitsSkip] ++
        ([.jump programLabels.lbTopBits] ++
        ([.label programLabels.lbRest] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer))))))))))
      (σ := ([] : List AVal)) (pin250 hf2.aw (by decide)) hz findLbRest
  have hround : ∀ {r2 : Nat} {yst2 : EvmState}, 0 < r2 →
      (r2 ≤ jt ∧ BETop yst2 cd i0 r2) →
      (∃ yst', (r2 - 1 ≤ jt ∧ BETop yst' cd i0 (r2 - 1)) ∧
        ASteps programAsm ⟨beTopBitsBody ++ beSer, [], yst2⟩
          ⟨beTopBitsBody ++ beSer, [], yst'⟩) ∨
      (BETop yst2 cd i0 0 ∧
        ASteps programAsm ⟨beTopBitsBody ++ beSer, [], yst2⟩
          ⟨store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)), [], yst2⟩) := by
    intro r2 yst2 hr2 hinvid
    obtain ⟨hr2le, hinv2⟩ := hinvid
    obtain ⟨yR, hinvR, hstepsR⟩ := exp_topbits_round hn0 hn32 hm0 hr2 hinv2
    exact Or.inl ⟨yR, ⟨by omega, hinvR⟩, hstepsR⟩
  obtain ⟨yF, hPF, hsteps⟩ :=
    loop_counted (model := localModel) (prog := programAsm)
      (top := beTopBitsBody ++ beSer) (σ := ([] : List AVal))
      (c' := store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)))
      (Inv := fun yst2 r2 => r2 ≤ jt ∧ BETop yst2 cd i0 r2)
      (P := fun yst2 => BETop yst2 cd i0 0)
      hround hexit (n := jt) ⟨le_refl _, hinv⟩
  -- the byte-seeded exit: bump the cursor and enter the bytes loop
  have hi0lt := hPF.i0lt
  have hfF := hPF.fr
  have hval : evalExpr (.bin .add (.load Icell) (.imm 1)) yF = W (i0 + 1) := by
    show loadWord yF.memory Icell + W 1 = _
    rw [hPF.icell]
    exact W_add (by omega : i0 + 1 < 2 ^ 256)
  have hsI : ASteps programAsm
      ⟨store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)), [], yF⟩
      ⟨[.label programLabels.lbBytes] ++ (beBytesBody ++ beSer), [],
        { yF with memory := storeWord yF.memory Icell (W (i0 + 1)) }⟩ :=
    store_pin (c := Icell) (e := .bin .add (.load Icell) (.imm 1))
      (v := W (i0 + 1))
      (k := [.label programLabels.lbBytes] ++ (beBytesBody ++ beSer)) (yst := yF)
      (by
        show binOK YulSemantics.EVM.Op.add = true ∧
          exprOK (Expr.load Icell) yF ∧ exprOK (Expr.imm 1) yF
        exact ⟨rfl, pin250 hfF.aw (by decide), trivial⟩)
      (by decide) (by rw [hfF.aw]; show Icell + 32 ≤ 32 * 250; decide) hval
  set yst3 : EvmState :=
    { yF with memory := storeWord yF.memory Icell (W (i0 + 1)) } with hyst3
  have hfr3 : BEF yst3 cd := bef_store (c := Icell) (by decide) hfF
  have hacc0 : bVal cd ^ (eByte cd i0 / 2 ^ 0) % modVal cd
      = bVal cd ^ eByte cd i0 % modVal cd := by
    rw [Nat.pow_zero, Nat.div_one]
  have hacc3 : RepresentsY (storeWord yF.memory Icell (W (i0 + 1))) ACC (nlimbs cd)
      (bVal cd ^ ePfx cd (i0 + 1) % modVal cd) := by
    rw [ePfx_succ, hPF.pfx0, Nat.zero_mul, Nat.zero_add, ← hacc0]
    exact RepresentsY_storeWord_disjoint hPF.accrep (by
      have hACCv : (ACC : Nat) = 2048 := rfl
      have hIcv : (Icell : Nat) = 7392 := rfl
      have hn32F := hfF.hn32
      omega)
  have hlab : ASteps programAsm ⟨[.label programLabels.lbBytes] ++
      (beBytesBody ++ beSer), [], yst3⟩ ⟨beBytesBody ++ beSer, [], yst3⟩ :=
    label_steps (model := localModel) (σ := ([] : List AVal))
  exact ⟨yst3, ⟨hfr3, loadWord_storeWord_self _ _ _, hacc3⟩,
    (hsteps.trans hsI).trans hlab⟩

/-! ## The remaining-bytes loops -/

/-- At the byte-bits loop head: `Jcell = j` pending bits of exponent byte
`i` (in `Wcell`), with the prefix-scaled window invariant on `ACC`. -/
structure BEBits (yst : EvmState) (cd : ByteArray) (i j : Nat) : Prop where
  fr : BEF yst cd
  icell : loadWord yst.memory Icell = W i
  wcell : loadWord yst.memory Wcell = W (eByte cd i)
  jcell : loadWord yst.memory Jcell = W j
  j8 : j ≤ 8
  ilt : i < exponentSize cd
  accrep : RepresentsY yst.memory ACC (nlimbs cd)
    (bVal cd ^ (ePfx cd i * 2 ^ (8 - j) + eByte cd i / 2 ^ j) % modVal cd)

/-- One byte-bits round: square, conditionally multiply, one bit down. -/
theorem exp_bytebits_round {cd : ByteArray} {i r : Nat} {yst : EvmState}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : modVal cd ≠ 0)
    (hr : 0 < r) (hr8 : r ≤ 8) (hinv : BEBits yst cd i r) :
    ∃ yst', BEBits yst' cd i (r - 1) ∧
      ASteps programAsm ⟨beByteBitsBody ++ beSer, [], yst⟩
        ⟨beByteBitsBody ++ beSer, [], yst'⟩ := by
  have hm0pos : 0 < modVal cd := Nat.pos_of_ne_zero hm0
  have hf := hinv.fr
  set w := eByte cd i with hwdef
  have hw256 : w < 256 := eByte_lt cd i
  set x := bVal cd ^ (ePfx cd i * 2 ^ (8 - r) + w / 2 ^ r) % modVal cd with hxdef
  have hxl : x < modVal cd := Nat.mod_lt _ hm0pos
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hJcv : (Jcell : Nat) = 7424 := rfl
  have hIcv : (Icell : Nat) = 7392 := rfl
  have hWcv : (Wcell : Nat) = 7456 := rfl
  have hopen : beByteBitsBody ++ beSer =
      jumpIfZ (.load Jcell) programLabels.lbNextByte ++
      (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      (callMulMod ACC programLabels.lsqRet2 programLabels.lmmEntry ++
      (jumpIfZ bitTest programLabels.lbByteBitsSkip ++
      (callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
      ([.label programLabels.lbByteBitsSkip] ++
      ([.jump programLabels.lbByteBits] ++
      ([.label programLabels.lbNextByte] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.jump programLabels.lbBytes] ++ beSer))))))))) := by
    rw [beByteBitsBody]; simp only [List.append_assoc]
  rw [hopen]
  -- step 1: fall the counter test
  have hj8 := hinv.j8
  have hfall : evalExpr (.load Jcell) yst ≠ 0 := by
    show loadWord yst.memory Jcell ≠ 0
    rw [hinv.jcell]
    exact W_ne_zero (by omega) (by omega)
  have s1 := jumpIfZ_fall (model := localModel) (prog := programAsm)
    (e := .load Jcell) (l := programLabels.lbNextByte)
    (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      (callMulMod ACC programLabels.lsqRet2 programLabels.lmmEntry ++
      (jumpIfZ bitTest programLabels.lbByteBitsSkip ++
      (callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
      ([.label programLabels.lbByteBitsSkip] ++
      ([.jump programLabels.lbByteBits] ++
      ([.label programLabels.lbNextByte] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.jump programLabels.lbBytes] ++ beSer)))))))))
    (σ := ([] : List AVal)) (pin250 hf.aw (by decide)) hfall
  -- step 2: Jcell := r - 1
  have hval : evalExpr (.bin .sub (.load Jcell) (.imm 1)) yst = W (r - 1) := by
    show loadWord yst.memory Jcell - W 1 = _
    rw [hinv.jcell]
    exact W_sub (by omega : (1 : Nat) ≤ r) (by omega : r < 2 ^ 256)
  have s2 := store_pin (c := Jcell) (e := .bin .sub (.load Jcell) (.imm 1))
    (v := W (r - 1))
    (k := callMulMod ACC programLabels.lsqRet2 programLabels.lmmEntry ++
      (jumpIfZ bitTest programLabels.lbByteBitsSkip ++
      (callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
      ([.label programLabels.lbByteBitsSkip] ++
      ([.jump programLabels.lbByteBits] ++
      ([.label programLabels.lbNextByte] ++
      (store Icell (.bin .add (.load Icell) (.imm 1)) ++
      ([.jump programLabels.lbBytes] ++ beSer))))))))
    (yst := yst)
    (by
      show binOK YulSemantics.EVM.Op.sub = true ∧
        exprOK (Expr.load Jcell) yst ∧ exprOK (Expr.imm 1) yst
      exact ⟨rfl, pin250 hf.aw (by decide), trivial⟩)
    (by decide) (by rw [hf.aw]; show Jcell + 32 ≤ 32 * 250; decide) hval
  set yJ : EvmState := { yst with memory := storeWord yst.memory Jcell (W (r - 1)) } with hyJ
  have hfrJ : BEF yJ cd := bef_store (c := Jcell) (by decide) hf
  have haccJ : RepresentsY yJ.memory ACC (nlimbs cd)
      (bVal cd ^ (ePfx cd i * 2 ^ (8 - r) + w / 2 ^ r) % modVal cd) :=
    RepresentsY_storeWord_disjoint hinv.accrep (by omega)
  have hicJ : loadWord yJ.memory Icell = W i := by
    show loadWord (storeWord yst.memory Jcell (W (r - 1))) Icell = W i
    rw [load_disj' yst.memory Jcell Icell (W (r - 1)) (Or.inr (by omega))]
    exact hinv.icell
  have hwJ : loadWord yJ.memory Wcell = W w := by
    show loadWord (storeWord yst.memory Jcell (W (r - 1))) Wcell = W w
    rw [load_disj' yst.memory Jcell Wcell (W (r - 1)) (Or.inl (by omega))]
    exact hinv.wcell
  have hjJ : loadWord yJ.memory Jcell = W (r - 1) := loadWord_storeWord_self _ _ _
  -- step 3: the squaring call
  obtain ⟨yQ, hsq, haccQ, hfrQ, hcellQ, hNQ⟩ :=
    mm_sq hn0 hn32 hm0pos hfrJ haccJ hxl findLsqRet2 memLsqRet2
  have hicQ : loadWord yQ.memory Icell = W i :=
    (hcellQ Icell (by decide) (by decide)).trans hicJ
  have hwQ : loadWord yQ.memory Wcell = W w :=
    (hcellQ Wcell (by decide) (by decide)).trans hwJ
  have hjQ : loadWord yQ.memory Jcell = W (r - 1) :=
    (hcellQ Jcell (by decide) (by decide)).trans hjJ
  have hbit : evalExpr bitTest yQ = W ((w / 2 ^ (r - 1)) % 2) :=
    evalExpr_bitTest hwQ hjQ (by omega) (by omega)
  have hok : exprOK bitTest yQ :=
    ⟨rfl, ⟨rfl, pin250 hfrQ.aw (by decide), pin250 hfrQ.aw (by decide)⟩, trivial⟩
  have hsqm : (x * x) % modVal cd
      = bVal cd ^ (2 * (ePfx cd i * 2 ^ (8 - r) + w / 2 ^ r)) % modVal cd :=
    be_sq_mod (b := bVal cd) (E := ePfx cd i * 2 ^ (8 - r) + w / 2 ^ r)
      (m := modVal cd) (x := x) rfl
  have hbt := be_bit_step (ePfx cd i) w r hr hr8
  by_cases hb : (w / 2 ^ (r - 1)) % 2 = 1
  · -- multiply by the base, then loop
    rw [hb] at hbt
    have hfall2 : evalExpr bitTest yQ ≠ 0 := by
      rw [hbit, hb]
      exact W_ne_zero one_ne_zero (by norm_num)
    have s3 := jumpIfZ_fall (model := localModel) (prog := programAsm)
      (e := bitTest) (l := programLabels.lbByteBitsSkip)
      (k := callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
        ([.label programLabels.lbByteBitsSkip] ++
        ([.jump programLabels.lbByteBits] ++
        ([.label programLabels.lbNextByte] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer))))))
      (σ := ([] : List AVal)) hok hfall2
    obtain ⟨yM, hmul, haccM, hfrM, hcellM, hNM⟩ :=
      mm_mul hn0 hn32 hm0pos hfrQ haccQ (Nat.mod_lt _ hm0pos) findLmulRet2 memLmulRet2
    have hlab : ASteps programAsm
        ⟨[.label programLabels.lbByteBitsSkip] ++ ([.jump programLabels.lbByteBits] ++
          ([.label programLabels.lbNextByte] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbBytes] ++ beSer)))), [], yM⟩
        ⟨[.jump programLabels.lbByteBits] ++ ([.label programLabels.lbNextByte] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbBytes] ++ beSer))), [], yM⟩ :=
      label_steps (model := localModel) (σ := ([] : List AVal))
    have hjmp : ASteps programAsm
        ⟨[.jump programLabels.lbByteBits] ++ ([.label programLabels.lbNextByte] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbBytes] ++ beSer))), [], yM⟩
        ⟨beByteBitsBody ++ beSer, [], yM⟩ :=
      jump_steps (model := localModel) (σ := ([] : List AVal)) findLbByteBits
    refine ⟨yM, ⟨hfrM, (hcellM Icell (by decide) (by decide)).trans hicQ,
      (hcellM Wcell (by decide) (by decide)).trans hwQ,
      (hcellM Jcell (by decide) (by decide)).trans hjQ,
      by omega, hinv.ilt, ?_⟩,
      (((s1.trans s2).trans hsq).trans s3).trans (hmul.trans (hlab.trans hjmp))⟩
    show RepresentsY yM.memory ACC (nlimbs cd)
      (bVal cd ^ (ePfx cd i * 2 ^ (8 - (r - 1)) + eByte cd i / 2 ^ (r - 1))
        % modVal cd)
    have hval2 : bVal cd ^ (2 * (ePfx cd i * 2 ^ (8 - r) + w / 2 ^ r) + 1) % modVal cd
        = ((x * x) % modVal cd * (bVal cd % modVal cd)) % modVal cd :=
      (be_mulbase_mod (b := bVal cd) (E := 2 * (ePfx cd i * 2 ^ (8 - r) + w / 2 ^ r))
        (m := modVal cd) (x := (x * x) % modVal cd) (t := bVal cd % modVal cd)
        hsqm rfl).symm
    rw [← hwdef, ← hbt, hval2]
    exact haccM
  · -- bit clear: skip the multiply, loop
    have hzero2 : evalExpr bitTest yQ = 0 := by
      rw [hbit]
      rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ (r - 1)) with h | h
      · rw [h]; rfl
      · exact absurd h hb
    have s3 := jumpIfZ_taken (model := localModel) (prog := programAsm)
      (e := bitTest) (l := programLabels.lbByteBitsSkip)
      (c' := [.jump programLabels.lbByteBits] ++ ([.label programLabels.lbNextByte] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer))))
      (k := callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
        ([.label programLabels.lbByteBitsSkip] ++
        ([.jump programLabels.lbByteBits] ++
        ([.label programLabels.lbNextByte] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer))))))
      (σ := ([] : List AVal)) hok hzero2 findLbByteBitsSkip
    have hjmp : ASteps programAsm
        ⟨[.jump programLabels.lbByteBits] ++ ([.label programLabels.lbNextByte] ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lbBytes] ++ beSer))), [], yQ⟩
        ⟨beByteBitsBody ++ beSer, [], yQ⟩ :=
      jump_steps (model := localModel) (σ := ([] : List AVal)) findLbByteBits
    have hb0 : (w / 2 ^ (r - 1)) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ (r - 1)) with h | h
      · exact h
      · exact absurd h hb
    rw [hb0] at hbt
    refine ⟨yQ, ⟨hfrQ, hicQ, hwQ, hjQ, by omega, hinv.ilt, ?_⟩,
      ((s1.trans s2).trans hsq).trans (s3.trans hjmp)⟩
    show RepresentsY yQ.memory ACC (nlimbs cd)
      (bVal cd ^ (ePfx cd i * 2 ^ (8 - (r - 1)) + eByte cd i / 2 ^ (r - 1))
        % modVal cd)
    rw [← hwdef, ← hbt, Nat.add_zero, ← hsqm]
    exact haccQ

/-- The byte-bits loop: eight rounds consume exponent byte `i`, bump the
cursor, and return to the bytes loop head. -/
theorem exp_bytebits {cd : ByteArray} (hv : ValidInput cd) {i : Nat} {yst : EvmState}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : modVal cd ≠ 0)
    (hinv : BEBits yst cd i 8) :
    ∃ yst', BEBytes yst' cd (i + 1) ∧
      ASteps programAsm ⟨beByteBitsBody ++ beSer, [], yst⟩
        ⟨beBytesBody ++ beSer, [], yst'⟩ := by
  have hexit : ∀ yst2 : EvmState, (0 ≤ 8 ∧ BEBits yst2 cd i 0) →
      BEBits yst2 cd i 0 ∧
        ASteps programAsm ⟨beByteBitsBody ++ beSer, [], yst2⟩
          ⟨store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.jump programLabels.lbBytes] ++ beSer), [], yst2⟩ := by
    intro yst2 hpair
    obtain ⟨_, hinv2⟩ := hpair
    have hf2 := hinv2.fr
    have hz : evalExpr (.load Jcell) yst2 = 0 := by
      show loadWord yst2.memory Jcell = 0
      rw [hinv2.jcell]
      rfl
    refine ⟨hinv2, ?_⟩
    rw [show beByteBitsBody ++ beSer =
        jumpIfZ (.load Jcell) programLabels.lbNextByte ++
        (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callMulMod ACC programLabels.lsqRet2 programLabels.lmmEntry ++
        (jumpIfZ bitTest programLabels.lbByteBitsSkip ++
        (callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
        ([.label programLabels.lbByteBitsSkip] ++
        ([.jump programLabels.lbByteBits] ++
        ([.label programLabels.lbNextByte] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer))))))))) from by
      rw [beByteBitsBody]; simp only [List.append_assoc]]
    exact jumpIfZ_taken (model := localModel) (prog := programAsm)
      (e := .load Jcell) (l := programLabels.lbNextByte)
      (c' := store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer))
      (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (callMulMod ACC programLabels.lsqRet2 programLabels.lmmEntry ++
        (jumpIfZ bitTest programLabels.lbByteBitsSkip ++
        (callMulMod BASE programLabels.lmulRet2 programLabels.lmmEntry ++
        ([.label programLabels.lbByteBitsSkip] ++
        ([.jump programLabels.lbByteBits] ++
        ([.label programLabels.lbNextByte] ++
        (store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer)))))))))
      (σ := ([] : List AVal)) (pin250 hf2.aw (by decide)) hz findLbNextByte
  have hround : ∀ {r2 : Nat} {yst2 : EvmState}, 0 < r2 →
      (r2 ≤ 8 ∧ BEBits yst2 cd i r2) →
      (∃ yst', (r2 - 1 ≤ 8 ∧ BEBits yst' cd i (r2 - 1)) ∧
        ASteps programAsm ⟨beByteBitsBody ++ beSer, [], yst2⟩
          ⟨beByteBitsBody ++ beSer, [], yst'⟩) ∨
      (BEBits yst2 cd i 0 ∧
        ASteps programAsm ⟨beByteBitsBody ++ beSer, [], yst2⟩
          ⟨store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.jump programLabels.lbBytes] ++ beSer), [], yst2⟩) := by
    intro r2 yst2 hr2 hinvid
    obtain ⟨hr2le, hinv2⟩ := hinvid
    obtain ⟨yR, hinvR, hstepsR⟩ :=
      exp_bytebits_round hn0 hn32 hm0 hr2 hr2le hinv2
    exact Or.inl ⟨yR, ⟨by omega, hinvR⟩, hstepsR⟩
  obtain ⟨yF, hPF, hsteps⟩ :=
    loop_counted (model := localModel) (prog := programAsm)
      (top := beByteBitsBody ++ beSer) (σ := ([] : List AVal))
      (c' := store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer))
      (Inv := fun yst2 r2 => r2 ≤ 8 ∧ BEBits yst2 cd i r2)
      (P := fun yst2 => BEBits yst2 cd i 0)
      hround hexit (n := 8) ⟨le_refl _, hinv⟩
  -- the byte-consumed exit: bump the cursor and jump back to the bytes loop
  have hes1024 : exponentSize cd ≤ 1024 := by
    obtain ⟨-, -, he, -⟩ := hv
    exact he
  have hilt := hPF.ilt
  have hfF := hPF.fr
  have hval : evalExpr (.bin .add (.load Icell) (.imm 1)) yF = W (i + 1) := by
    show loadWord yF.memory Icell + W 1 = _
    rw [hPF.icell]
    exact W_add (by omega : i + 1 < 2 ^ 256)
  have hsI : ASteps programAsm
      ⟨store Icell (.bin .add (.load Icell) (.imm 1)) ++
        ([.jump programLabels.lbBytes] ++ beSer), [], yF⟩
      ⟨beBytesBody ++ beSer, [],
        { yF with memory := storeWord yF.memory Icell (W (i + 1)) }⟩ := by
    refine (store_pin (c := Icell) (e := .bin .add (.load Icell) (.imm 1))
      (v := W (i + 1))
      (k := [.jump programLabels.lbBytes] ++ beSer) (yst := yF)
      (by
        show binOK YulSemantics.EVM.Op.add = true ∧
          exprOK (Expr.load Icell) yF ∧ exprOK (Expr.imm 1) yF
        exact ⟨rfl, pin250 hfF.aw (by decide), trivial⟩)
      (by decide) (by rw [hfF.aw]; show Icell + 32 ≤ 32 * 250; decide) hval).trans
      (jump_steps (model := localModel) (σ := ([] : List AVal)) findLbBytes)
  have hfrI : BEF { yF with memory := storeWord yF.memory Icell (W (i + 1)) } cd :=
    bef_store (c := Icell) (by decide) hfF
  have hwF : eByte cd i < 256 := eByte_lt cd i
  have hacc := hPF.accrep
  rw [show (2 : Nat) ^ (8 - 0) = 256 from by norm_num, Nat.pow_zero, Nat.div_one] at hacc
  have haccI : RepresentsY (storeWord yF.memory Icell (W (i + 1))) ACC (nlimbs cd)
      (bVal cd ^ (ePfx cd i * 256 + eByte cd i) % modVal cd) :=
    RepresentsY_storeWord_disjoint hacc (by
      have hACCv : (ACC : Nat) = 2048 := rfl
      have hIcv : (Icell : Nat) = 7392 := rfl
      have hn32F := hfF.hn32
      omega)
  refine ⟨{ yF with memory := storeWord yF.memory Icell (W (i + 1)) },
    ⟨hfrI, loadWord_storeWord_self _ _ _, ?_⟩, hsteps.trans hsI⟩
  rw [ePfx_succ]
  exact haccI

/-- One bytes round: consume exponent byte `i` — guard, fetch, eight bit
rounds, cursor bump — returning to the loop head. -/
theorem exp_bytes_round {cd : ByteArray} (hv : ValidInput cd) {i : Nat} {yst : EvmState}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : modVal cd ≠ 0)
    (hi : i < exponentSize cd) (hinv : BEBytes yst cd i) :
    ∃ yst', BEBytes yst' cd (i + 1) ∧
      ASteps programAsm ⟨beBytesBody ++ beSer, [], yst⟩
        ⟨beBytesBody ++ beSer, [], yst'⟩ := by
  have hf := hinv.fr
  have hes1024 : exponentSize cd ≤ 1024 := by
    obtain ⟨-, -, he, -⟩ := hv
    exact he
  have hb1024 : baseSize cd ≤ 1024 := by
    obtain ⟨-, hb, -, -⟩ := hv
    exact hb
  have hi256 : i < 2 ^ 256 := Nat.lt_of_le_of_lt (by omega) (size_lt _ hes1024)
  have hIcv : (Icell : Nat) = 7392 := rfl
  have hJcv : (Jcell : Nat) = 7424 := rfl
  have hWcv : (Wcell : Nat) = 7456 := rfl
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hn32f := hn32
  -- the guard falls
  have hult : (evalExpr (.load Icell) yst).ult (evalExpr (.load ES) yst) := by
    show (loadWord yst.memory Icell).ult (loadWord yst.memory ES) = true
    rw [hinv.icell, hf.escell]
    exact W_ult hi256 (size_lt _ hes1024) hi
  have hopen : beBytesBody ++ beSer =
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lbSer ++
      (store Wcell (cdbCell EO) ++ (store Jcell (.imm 8) ++
      ([.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer)))) := by
    rw [beBytesBody]; simp only [List.append_assoc]
  rw [hopen]
  -- Wcell := exponent byte i
  set eo := eOff cd with heodef
  have heoB : eo ≤ 1120 := by rw [heodef, eOff]; omega
  have hiB : i ≤ 1024 := by omega
  have hWsum : (W eo + W i : U256) = W (eo + i) := W_add (by omega)
  have hToW : (W (eo + i)).toNat = eo + i := toNat_W (by omega)
  have haddr : (evalExpr (.bin .add (.load EO) (.load Icell)) yst).toNat
      = eo + i := by
    show (loadWord yst.memory EO + loadWord yst.memory Icell).toNat = eo + i
    rw [hf.eocell, hinv.icell, hWsum, hToW]
  have hcdb : evalExpr (cdbCell EO) yst = W (eByte cd i) := by
    show evalExpr (Expr.cdb (.bin .add (.load EO) (.load Icell))) yst = _
    rw [evalExpr_cdb haddr]
    show W (byteFrom yst.env.calldata (eo + i)).toNat = _
    rw [hf.env, eByte]
  -- the round's straight-line prefix
  have hstep1 : ASteps programAsm ⟨beBytesBody ++ beSer, [], yst⟩
      ⟨store Wcell (cdbCell EO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer))), [], yst⟩ :=
    jumpUnlessLt_fall (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load ES) (l := programLabels.lbSer)
      (k := store Wcell (cdbCell EO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer))))
      (σ := ([] : List AVal)) (pin250 hf.aw (by decide))
      (pin250 hf.aw (by decide)) hult
  have hstep2 : ASteps programAsm
      ⟨store Wcell (cdbCell EO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer))), [], yst⟩
      ⟨store Jcell (.imm 8) ++ ([.label programLabels.lbByteBits] ++
        (beByteBitsBody ++ beSer)), [],
        { yst with memory := storeWord yst.memory Wcell (W (eByte cd i)) }⟩ :=
    store_pin (c := Wcell) (e := cdbCell EO) (v := W (eByte cd i))
      (k := store Jcell (.imm 8) ++ ([.label programLabels.lbByteBits] ++
        (beByteBitsBody ++ beSer)))
      (yst := yst)
      (by
        show exprOK (Expr.bin .add (Expr.load EO) (Expr.load Icell)) yst
        exact ⟨rfl, pin250 hf.aw (by decide), pin250 hf.aw (by decide)⟩)
      (by decide) (by rw [hf.aw]; show Wcell + 32 ≤ 32 * 250; decide) hcdb
  set yW : EvmState :=
    { yst with memory := storeWord yst.memory Wcell (W (eByte cd i)) } with hyW
  have hstep3 : ASteps programAsm
      ⟨store Jcell (.imm 8) ++ ([.label programLabels.lbByteBits] ++
        (beByteBitsBody ++ beSer)), [], yW⟩
      ⟨[.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer), [],
        { yW with memory := storeWord yW.memory Jcell (W 8) }⟩ :=
    store_pin (c := Jcell) (e := .imm 8) (v := W 8)
      (k := [.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer))
      (yst := yW) (by trivial) (by decide)
      (by rw [hf.aw]; show Jcell + 32 ≤ 32 * 250; decide) rfl
  set yWJ : EvmState :=
    { yW with memory := storeWord yW.memory Jcell (W 8) } with hyWJ
  have hstep4 : ASteps programAsm
      ⟨[.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer), [], yWJ⟩
      ⟨beByteBitsBody ++ beSer, [], yWJ⟩ :=
    label_steps (model := localModel) (σ := ([] : List AVal))
  -- the entry invariant of the bit loop
  have hfrW : BEF yW cd := bef_store (c := Wcell) (by decide) hf
  have hfrWJ : BEF yWJ cd := bef_store (c := Jcell) (by decide) hfrW
  have hicWJ : loadWord yWJ.memory Icell = W i := by
    show loadWord (storeWord (storeWord yst.memory Wcell (W (eByte cd i)))
        Jcell (W 8)) Icell = W i
    rw [load_disj' _ _ _ _ (Or.inr (by omega)), load_disj' _ _ _ _ (Or.inr (by omega))]
    exact hinv.icell
  have hwcWJ : loadWord yWJ.memory Wcell = W (eByte cd i) := by
    show loadWord (storeWord (storeWord yst.memory Wcell (W (eByte cd i)))
        Jcell (W 8)) Wcell = _
    rw [load_disj' _ _ _ _ (Or.inl (by omega))]
    exact loadWord_storeWord_self _ _ _
  have hjcWJ : loadWord yWJ.memory Jcell = W 8 := loadWord_storeWord_self _ _ _
  have hent : ePfx cd i * 2 ^ (8 - 8) + eByte cd i / 2 ^ 8 = ePfx cd i := by
    rw [show (8 : Nat) - 8 = 0 from rfl, Nat.pow_zero, Nat.mul_one,
      show (2 : Nat) ^ 8 = 256 from by norm_num, Nat.div_eq_of_lt (eByte_lt cd i),
      Nat.add_zero]
  have haccWJ : RepresentsY yWJ.memory ACC (nlimbs cd)
      (bVal cd ^ (ePfx cd i * 2 ^ (8 - 8) + eByte cd i / 2 ^ 8) % modVal cd) := by
    rw [hent]
    exact RepresentsY_storeWord_disjoint
      (RepresentsY_storeWord_disjoint hinv.accrep (by omega)) (by omega)
  obtain ⟨yB, hbytes, hstepsB⟩ :=
    exp_bytebits hv hn0 hn32 hm0
      ⟨hfrWJ, hicWJ, hwcWJ, hjcWJ, (by decide : 8 ≤ 8), hi, haccWJ⟩
  exact ⟨yB, hbytes, ((hstep1.trans hstep2).trans hstep3).trans (hstep4.trans hstepsB)⟩

/-- The exponent phase's exit contract at the serializer top. -/
structure BEX (yst : EvmState) (cd : ByteArray) : Prop where
  aw : yst.activeWords.toNat = 250
  mscell : loadWord yst.memory MS = W (modulusSize cd)
  accrep : RepresentsY yst.memory ACC (nlimbs cd) (bVal cd ^ eVal cd % modVal cd)

/-- The bytes loop: from the byte after the seed to the end of the exponent,
jumping to the serializer with the whole exponent consumed. -/
theorem exp_bytes_loop {cd : ByteArray} (hv : ValidInput cd) {i0 : Nat} {yst : EvmState}
    (hn0 : 0 < nlimbs cd) (hn32 : nlimbs cd ≤ 32) (hm0 : modVal cd ≠ 0)
    (hi0 : i0 + 1 ≤ exponentSize cd) (hinv : BEBytes yst cd (i0 + 1)) :
    ∃ yst', BEX yst' cd ∧
      ASteps programAsm ⟨beBytesBody ++ beSer, [], yst⟩
        ⟨bpSer programLabels ++ progTail, [], yst'⟩ := by
  have hf := hinv.fr
  have hes1024 : exponentSize cd ≤ 1024 := by
    obtain ⟨-, -, he, -⟩ := hv
    exact he
  have hround : ∀ {r2 : Nat} {yst2 : EvmState}, 0 < r2 →
      (r2 ≤ exponentSize cd - (i0 + 1) ∧
          BEBytes yst2 cd (exponentSize cd - r2)) →
      (∃ yst', (r2 - 1 ≤ exponentSize cd - (i0 + 1) ∧
          BEBytes yst' cd (exponentSize cd - (r2 - 1))) ∧
        ASteps programAsm ⟨beBytesBody ++ beSer, [], yst2⟩
          ⟨beBytesBody ++ beSer, [], yst'⟩) ∨
      (BEBytes yst2 cd (exponentSize cd) ∧
        ASteps programAsm ⟨beBytesBody ++ beSer, [], yst2⟩
          ⟨bpSer programLabels ++ progTail, [], yst2⟩) := by
    intro r2 yst2 hr2 hinvid
    obtain ⟨hr2le, hinv2⟩ := hinvid
    obtain ⟨yst', hinv', hst⟩ :=
      exp_bytes_round hv hn0 hn32 hm0
        (by omega : exponentSize cd - r2 < exponentSize cd) hinv2
    refine Or.inl ⟨yst', ⟨by omega, ?_⟩, hst⟩
    rw [show exponentSize cd - (r2 - 1) = exponentSize cd - r2 + 1 from by omega]
    exact hinv'
  have hexit : ∀ yst2 : EvmState,
      (0 ≤ exponentSize cd - (i0 + 1) ∧
          BEBytes yst2 cd (exponentSize cd - 0)) →
      BEBytes yst2 cd (exponentSize cd) ∧
        ASteps programAsm ⟨beBytesBody ++ beSer, [], yst2⟩
          ⟨bpSer programLabels ++ progTail, [], yst2⟩ := by
    intro yst2 ⟨_, hinv2⟩
    have hf2 := hinv2.fr
    have hes256 : exponentSize cd < 2 ^ 256 := size_lt _ hes1024
    have hnlt : ¬ (evalExpr (.load Icell) yst2).ult (evalExpr (.load ES) yst2) := by
      show ¬ (loadWord yst2.memory Icell).ult (loadWord yst2.memory ES) = true
      rw [hinv2.icell, hf2.escell]
      exact W_nult (by omega) hes256 (by omega)
    refine ⟨hinv2, ?_⟩
    rw [show beBytesBody ++ beSer =
        jumpUnlessLt (.load Icell) (.load ES) programLabels.lbSer ++
        (store Wcell (cdbCell EO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer)))) from by
      rw [beBytesBody]; simp only [List.append_assoc]]
    exact jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (e₁ := .load Icell) (e₂ := .load ES) (l := programLabels.lbSer)
      (c' := bpSer programLabels ++ progTail)
      (k := store Wcell (cdbCell EO) ++ (store Jcell (.imm 8) ++
        ([.label programLabels.lbByteBits] ++ (beByteBitsBody ++ beSer))))
      (σ := ([] : List AVal)) (pin250 hf2.aw (by decide))
      (pin250 hf2.aw (by decide)) hnlt findLbSer
  obtain ⟨yF, hPF, hsteps⟩ :=
    loop_counted (model := localModel) (prog := programAsm)
      (top := beBytesBody ++ beSer) (σ := ([] : List AVal))
      (c' := bpSer programLabels ++ progTail)
      (Inv := fun yst2 r2 => r2 ≤ exponentSize cd - (i0 + 1) ∧
        BEBytes yst2 cd (exponentSize cd - r2))
      (P := fun yst2 => BEBytes yst2 cd (exponentSize cd))
      hround hexit (n := exponentSize cd - (i0 + 1))
      (yst := yst) ⟨by omega, by
        rw [show exponentSize cd - (exponentSize cd - (i0 + 1)) = i0 + 1 from by omega]
        exact hinv⟩
  exact ⟨yF, ⟨hPF.fr.aw, hPF.fr.mscell, hPF.accrep⟩, hsteps⟩

/-- The exponent section composed: from the base phase's exit state to the
serializer top with `ACC` holding `b ^ e % m` (the zero-exponent case
already has `ACC = 1 % m = b ^ 0 % m`). -/
theorem big_exp {cd : ByteArray} (hv : ValidInput cd) (hmspos : 0 < modulusSize cd)
    (hm0 : modVal cd ≠ 0) {yst : EvmState} (hx : BBExit yst cd) :
    ∃ yst', BEX yst' cd ∧
      ASteps programAsm ⟨beExpAll ++ beSer, [], yst⟩
        ⟨bpSer programLabels ++ progTail, [], yst'⟩ := by
  have hn0 : 0 < nlimbs cd := limbCount_pos hmspos
  have hn32 := hx.hn32
  set y0 : EvmState := { yst with memory := storeWord yst.memory Icell (W 0) } with hy0
  have hs0 : ASteps programAsm ⟨beExpAll ++ beSer, [], yst⟩
      ⟨beScanBody ++ (beFromInit ++ beSer), [], y0⟩ := by
    rw [show beExpAll ++ beSer = store Icell (.imm 0) ++
        ([.label programLabels.lbEScan] ++
          (beScanBody ++ (beFromInit ++ beSer))) from by
      rw [beExpAll]; simp only [List.append_assoc]]
    exact (store_pin (c := Icell) (e := .imm 0) (v := W 0)
      (k := [.label programLabels.lbEScan] ++ (beScanBody ++ (beFromInit ++ beSer)))
      (yst := yst) (by trivial) (by decide)
      (by rw [hx.aw]; show Icell + 32 ≤ 32 * 250; decide) rfl).trans
      (label_steps (model := localModel) (σ := ([] : List AVal)))
  have hBE := BE_of_BBExit hx
  rcases exp_scan_loop hv (exponentSize cd) 0 (by omega) y0 hBE (ePfx_zero cd) with
    ⟨yF, i0, hfnd, hstepsS⟩ | ⟨yE, hBEe, hstepsS⟩
  · have hi0lt := hfnd.i0lt
    obtain ⟨y2, jt, htop, hstepsT⟩ := exp_found hv hmspos hm0 hfnd
    obtain ⟨y3, hbytes, hstepsB⟩ := exp_topbits hv hn0 hn32 hm0 htop
    obtain ⟨y4, hbx, hstepsE⟩ :=
      exp_bytes_loop hv hn0 hn32 hm0 (by omega : i0 + 1 ≤ exponentSize cd) hbytes
    exact ⟨y4, hbx, (hs0.trans hstepsS).trans ((hstepsT.trans hstepsB).trans hstepsE)⟩
  · exact ⟨yE, ⟨hBEe.fr.aw, hBEe.fr.mscell, hBEe.accrep⟩, hs0.trans hstepsS⟩

/-! ## The full-run composition -/

/-- The spec bridge: the specification bytes are the `modulusSize`-byte
encoding of `modPow b e m` at the program's three padded reads. -/
theorem spec_eq_modPow (calldata : ByteArray) (hms : 32 < modulusSize calldata) :
    spec calldata =
      natToBytes (modPow (bVal calldata) (eVal calldata) (modVal calldata))
        (modulusSize calldata) := by
  show (if modulusSize calldata = 0 then ByteArray.empty else
      natToBytes (modPow (bytesToNatPadded calldata 96 (baseSize calldata))
        (bytesToNatPadded calldata (96 + baseSize calldata) (exponentSize calldata))
        (bytesToNatPadded calldata (96 + baseSize calldata + exponentSize calldata)
          (modulusSize calldata))) (modulusSize calldata)) = _
  rw [if_neg (by omega), modVal_eq]
  rfl

/-- The modulus value fits the declared width. -/
theorem modVal_lt (calldata : ByteArray) :
    modVal calldata < 256 ^ modulusSize calldata := by
  rw [modVal_eq]
  exact bytesToNatPadded_lt_pow calldata (modOff calldata) (modulusSize calldata)

/-- The big path's full run: header → load → base → exponent → serialize,
halting with exactly `spec calldata` for every valid input with
`32 < modulusSize`. -/
theorem bigExp_correct (calldata : ByteArray) (hvalid : ValidInput calldata)
    (hms : 32 < modulusSize calldata) :
    ∃ (b : AConf) (yst' : EvmState),
      ASteps programAsm ⟨programAsm, [], initYst (assemble programInstrs) calldata⟩ b ∧
      AHalt programAsm b yst' ∧
      yst'.halted = some (.ret, (spec calldata).toList) := by
  have hA := header_big calldata hvalid hms
    (rest := secWordPath programLabels ++ (secBigPath programLabels ++ progTail))
    (c' := bigEntryCode programLabels ++ progTail) findLbig
  have hB := big_entry calldata hvalid
  obtain ⟨yL, hBL, hC⟩ := big_load_loop calldata hvalid hms
  obtain ⟨yS0, hBS0, hD1⟩ := big_scan_init hvalid hBL
  obtain ⟨yS, hBSn, hE⟩ := big_zero_scan calldata hvalid hBS0
  have hACCv : (ACC : Nat) = 2048 := rfl
  have hBSv : (BS : Nat) = 7168 := rfl
  -- the initial configuration, stated over the section spelling (a
  -- propositional transport; the definitional equality is too costly)
  have hstart : (⟨programAsm, [], y0c calldata⟩ : AConf) =
      ⟨secHeader programLabels ++ (secWordPath programLabels ++
        (secBigPath programLabels ++ progTail)), [], y0c calldata⟩ := by
    rw [programAsm_eq]
    rfl
  have hA' : ASteps programAsm ⟨programAsm, [], y0c calldata⟩
      ⟨bigEntryCode programLabels ++ progTail, [], hst6 calldata⟩ :=
    hstart.symm ▸ hA
  by_cases hmz : partVal calldata (modulusSize calldata) = 0
  · -- zero modulus: the zero-scan dispatches straight to the serializer
    have hF := big_scan_zero calldata hBSn hmz
    have hn0 : 0 < nlimbs calldata := limbCount_pos (by omega)
    have hn32 : nlimbs calldata ≤ 32 :=
      limbCount_le_32 _ (by obtain ⟨-, -, hm⟩ := hvalid; omega)
    have hrep0 : RepresentsY yS.memory ACC (nlimbs calldata) 0 :=
      rep_zero_of_zero hn0 (fun a ha1 ha2 =>
        hBSn.midzero a (by omega) (by omega))
    obtain ⟨b, yst', hS, hHalt, hD⟩ :=
      big_ser_ret calldata hvalid (by omega) hrep0
        (Nat.pow_pos (by norm_num : (0 : Nat) < 256)) hBSn.mscell hBSn.aw
    refine ⟨b, yst', ?_, hHalt, ?_⟩
    · exact (((((hA'.trans hB).trans hC).trans hD1).trans hE).trans hF).trans hS
    · rw [spec_eq_modPow calldata hms, modPow_eq,
          if_pos (show modVal calldata = 0 from hmz)]
      exact hD
  · -- nonzero modulus: the full base reduction, exponent phase, serialize
    obtain ⟨-, hF⟩ := big_scan_nonzero calldata hBSn hmz
    have hm0 : modVal calldata ≠ 0 := hmz
    have hm0pos : 0 < modVal calldata := Nat.pos_of_ne_zero hm0
    obtain ⟨yB, hBB, hG⟩ := bigBase_correct hvalid hms hBSn hm0
    obtain ⟨yE, hBX, hHx⟩ := big_exp hvalid (by omega) hm0 hBB
    have haltlt : bVal calldata ^ eVal calldata % modVal calldata
        < 256 ^ modulusSize calldata :=
      Nat.lt_trans (Nat.mod_lt _ hm0pos) (modVal_lt calldata)
    obtain ⟨b, yst', hS, hHalt, hD⟩ :=
      big_ser_ret calldata hvalid (by omega) hBX.accrep haltlt hBX.mscell hBX.aw
    refine ⟨b, yst', ?_, hHalt, ?_⟩
    · exact ((((((hA'.trans hB).trans hC).trans hD1).trans hE).trans hF).trans hG).trans
        (hHx.trans hS)
    · rw [spec_eq_modPow calldata hms, modPow_eq, if_neg hm0]
      exact hD

end Challenge.Modexp.Submission.Proof.BigExpProc

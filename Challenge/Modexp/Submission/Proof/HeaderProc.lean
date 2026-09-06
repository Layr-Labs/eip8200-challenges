import Challenge.Modexp.Submission.Program
import Challenge.Modexp.Submission.AsmLib
import Challenge.Modexp.Submission.Proof.YulMem
import Challenge.EvmProof.Bytes
import Mathlib.Tactic

set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
# Functional correctness of the MODEXP header fragment

`secHeader` parses the EIP-198 size words out of the calldata, enforces the
EIP-7823 operand-size bound (any declared size `> 1024` jumps to `invalid`),
returns the empty byte string when `msize = 0`, computes the operand offsets
`BO/EO/MO`, and dispatches on `msize > 32` to the big path.

This module proves the three header outcomes for every `ValidInput calldata`
(all sizes `≤ 1024`), and documents the exact exit state handed to the word
path and to the big path:

* memory: only the six scalar cells are written — `BS = bsize`, `ES = esize`,
  `MS = msize`, `BO = 96`, `EO = 96 + bsize`, `MO = 96 + bsize + esize`
  (as 256-bit words over the fresh all-zero memory);
* `activeWords = 230` exactly (the six stores raise the high-water mark from
  0, one word at a time, through the scalar cell range);
* the operand regions (`MOD/BASE/ACC/OUT/ONE/SUBC/RET`, addresses `< BS`)
  are untouched, hence all zero.

The generic helpers at the top (the program's structural view, label
resolution, word arithmetic, the calldata bridge) are the shared base for
the other proof modules; this file is also where the reconstructed section
view of `programAsm` (`ProgLabels`, `programLabels`, the `sec*` spellings
and `programAsm_eq`) lives for the whole proof tree. The big-path
consumers are `Proof/BigLoad.lean` and `Proof/BigSer.lean`.
-/

namespace Challenge.Modexp.Submission.Proof.Header

open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState wordFrom byteFrom byteAt loadWord storeWord
  storeByte readBytes touchMemory activeWordsAfter b2w)
open Challenge.Modexp.Submission (Expr store storeAt storeAt8 jumpIfNz jumpIfZ
  jumpUnlessLt cdbCell bitTest compileExpr loadAt evalExpr exprOK callAddMod
  callMulMod
  BS ES MS BO EO MO Ncell Icell Jcell Wcell T0 T1 T2 RET TOP ONE ACC BASE MOD OUT
  SUBC programAsm localModel initYst programInstrs)
open Challenge.Modexp.Submission.Proof.YulMem (wordVal wordVal_succ wordVal_lt
  byteAt_wordFrom_first wordFrom_eq wordFrom_toNat loadWord_storeWord_self
  loadWord_storeWord_disjoint)
open Challenge.Modexp (baseSize exponentSize modulusSize spec ValidInput)
open EvmSemantics.EVM.Precompile (bytesToNatPadded)
open Challenge.EvmProof.Bytes (bytesToNatPadded_zero_width bytesToNatPadded_succ
  bytesToNatPadded_lt_pow)

/-! ## Generic label resolution -/

/-- A label defined past a prefix resolves inside the rest of the program. -/
theorem findLabel_pre {l : Label} : ∀ {pre rest : List Asm}, l ∉ labelDefs pre →
    findLabel l (pre ++ rest) = findLabel l rest
  | [], _, _ => rfl
  | i :: pre, rest, h => by
    show (if i = Asm.label l then some ((pre ++ rest)) else findLabel l (pre ++ rest)) = _
    rw [if_neg]
    · exact findLabel_pre (fun hm => h (by simp [labelDefs_cons, hm]))
    · intro hc; exact h (by simp [labelDefs_cons, hc, Asm.defines])

/-- A label resolves to the code immediately after its (first) definition. -/
theorem findLabel_here {l : Label} : ∀ {pre post : List Asm}, l ∉ labelDefs pre →
    findLabel l (pre ++ (Asm.label l :: post)) = some post
  | [], _, _ => by simp [findLabel]
  | i :: pre, post, h => by
    show findLabel l (i :: (pre ++ (Asm.label l :: post))) = _
    rw [findLabel]
    have hne : ¬ i = Asm.label l := fun hc => h (by simp [labelDefs_cons, hc, Asm.defines])
    rw [if_neg hne]
    exact findLabel_here (fun hm => h (by simp [labelDefs_cons, hm]))

/-! ## The program's structural view

`Program.lean` builds the procedure-variant program with a label-generator
monad and exports only the flat `programAsm` (plus `programInstrs`). The
proofs consume a section view instead; this module reconstructs it: the
label record `ProgLabels` (fields named as in `genProgram`, carrying the
values `genProgram 0` allocates), the six section spellings (header, word
path, big path and halt stubs, then the two procedure bodies the calls
dispatch to), and the concatenation law `programAsm_eq`, which holds by
kernel `rfl` since both sides evaluate `genProgram 0`. The arithmetic call
sites inside `secBigPath` use the procedure-call helpers `callAddMod` /
`callMulMod`; the header, word path, `lbLoad`/`lbMScan` and
`lbSerLoop`/`lbReturn` regions are instruction-identical to the inlined
variant these proofs originally targeted. -/

/-- Every program label, in `genProgram`'s allocation order (fields named
as there; the concrete `programLabels` carries the values `genProgram 0`
allocates). -/
structure ProgLabels : Type where
  /- header -/
  linvalid : Nat
  lretEmpty : Nat
  lbig : Nat
  /- word path -/
  lwZeroMod : Nat
  lwbLoop : Nat
  lwbDone : Nat
  lweScan : Nat
  lweExpZero : Nat
  lwInit : Nat
  lweTop : Nat
  lweBits : Nat
  lweBitsInit : Nat
  lweRest : Nat
  lweBytes : Nat
  lweByteBits : Nat
  lweNext : Nat
  lweSer : Nat
  /- big path -/
  lbLoad : Nat
  lbLoadDone : Nat
  lbMScan : Nat
  lbMScanDone : Nat
  lbBase : Nat
  lbBaseBits : Nat
  lbBaseBitsSkip : Nat
  lbBaseNext : Nat
  lbBaseDone : Nat
  lbEScan : Nat
  lbInit : Nat
  lbTop : Nat
  lbInitAcc : Nat
  lbAccInit : Nat
  lbAccInitDone : Nat
  lbTopBits : Nat
  lbTopBitsSkip : Nat
  lbRest : Nat
  lbBytes : Nat
  lbByteBits : Nat
  lbByteBitsSkip : Nat
  lbNextByte : Nat
  lbSer : Nat
  lbSerLoop : Nat
  lbReturn : Nat
  /- addMod procedure -/
  lamEntry : Nat
  lamAdd : Nat
  lamSubStart : Nat
  amSub : Nat
  lamSel : Nat
  lamDoCopy : Nat
  lamCopy : Nat
  lamDone : Nat
  /- mulModBig procedure -/
  lmmEntry : Nat
  lmScanTop : Nat
  lmTopBit : Nat
  lmCopy : Nat
  lmBits : Nat
  lmNextLimb : Nat
  lmZero : Nat
  lmZeroLoop : Nat
  lmDone : Nat
  lmRetCopy : Nat
  lmExit : Nat
  /- call return labels -/
  lamCallBase1 : Nat
  lamCallBase2 : Nat
  lamCallAccInit : Nat
  lsqRet1 : Nat
  lmulRet1 : Nat
  lsqRet2 : Nat
  lmulRet2 : Nat
  lmSqRet : Nat
  lmAddRet : Nat

/-- The labels as allocated by `genProgram` from state `0`. -/
def programLabels : ProgLabels := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69⟩

def secHeader (l : ProgLabels) : List Asm := 
  store BS (.cdload (.imm 0)) ++
  store ES (.cdload (.imm 32)) ++
  store MS (.cdload (.imm 64)) ++
  jumpIfNz (.bin .or (.bin .or (.bin .lt (.imm 1024) (.load BS))
      (.bin .lt (.imm 1024) (.load ES))) (.bin .lt (.imm 1024) (.load MS))) l.linvalid ++
  jumpIfZ (.load MS) l.lretEmpty ++
  store BO (.imm 96) ++
  store EO (.bin .add (.imm 96) (.load BS)) ++
  store MO (.bin .add (.load EO) (.load ES)) ++
  jumpIfNz (.bin .lt (.imm 32) (.load MS)) l.lbig

def secWordPath (l : ProgLabels) : List Asm := 
  store TOP (.imm 0) ++
  store T0 (.bin .shr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
    (.cdload (.load MO))) ++
  jumpIfZ (.load T0) l.lwZeroMod ++
  store T1 (.imm 0) ++
  store Icell (.imm 0) ++
  -- base reduction
  [.label l.lwbLoop] ++
  jumpUnlessLt (.load Icell) (.load BS) l.lwbDone ++
  store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
    (cdbCell BO) (.load T0)) ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lwbLoop] ++
  [.label l.lwbDone] ++
  -- scan exponent for first nonzero byte
  store Icell (.imm 0) ++
  [.label l.lweScan] ++
  jumpUnlessLt (.load Icell) (.load ES) l.lweExpZero ++
  store Wcell (cdbCell EO) ++
  jumpIfNz (.load Wcell) l.lwInit ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lweScan] ++
  -- exponent zero: acc := 1 mod m
  [.label l.lweExpZero] ++
  store T2 (.bin .mod (.imm 1) (.load T0)) ++
  [.jump l.lweSer] ++
  -- found: seed acc with the base at the top set bit
  [.label l.lwInit] ++
  store Jcell (.imm 7) ++
  [.label l.lweTop] ++
  jumpIfNz bitTest l.lweBitsInit ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  [.jump l.lweTop] ++
  [.label l.lweBitsInit] ++
  store T2 (.load T1) ++
  [.label l.lweBits] ++
  jumpIfZ (.load Jcell) l.lweRest ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
  jumpIfZ bitTest l.lweBits ++
  store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
  [.jump l.lweBits] ++
  -- remaining bytes
  [.label l.lweRest] ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.label l.lweBytes] ++
  jumpUnlessLt (.load Icell) (.load ES) l.lweSer ++
  store Wcell (cdbCell EO) ++
  store Jcell (.imm 8) ++
  [.label l.lweByteBits] ++
  jumpIfZ (.load Jcell) l.lweNext ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
  jumpIfZ bitTest l.lweByteBits ++
  store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
  [.jump l.lweByteBits] ++
  [.label l.lweNext] ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lweBytes] ++
  -- zero modulus: result zero
  [.label l.lwZeroMod] ++
  store T2 (.imm 0) ++
  -- serialize: RET word := acc << ((32 - msize) * 8); return RET, msize
  [.label l.lweSer] ++
  store RET (.bin .shl (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
    (.load T2)) ++
  (compileExpr (.load MS) ++ compileExpr (.imm RET) ++ [.op .ret])

def secBigPath (l : ProgLabels) : List Asm := 
  [.label l.lbig] ++
  store TOP (.imm 0) ++
  store Ncell (.bin .div (.bin .add (.load MS) (.imm 31)) (.imm 32)) ++
  -- load modulus big-endian into MOD limbs
  store Icell (.imm 0) ++
  [.label l.lbLoad] ++
  jumpUnlessLt (.load Icell) (.load MS) l.lbLoadDone ++
  store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
  store T1 (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32))) ++
  storeAt (.load T1) (.bin .or (loadAt (.load T1))
    (.bin .shl (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32))) (cdbCell MO))) ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lbLoad] ++
  [.label l.lbLoadDone] ++
  -- modulus zero scan
  store T0 (.imm 0) ++
  store Icell (.imm 0) ++
  [.label l.lbMScan] ++
  jumpUnlessLt (.load Icell) (.load Ncell) l.lbMScanDone ++
  store T0 (.bin .or (.load T0) (loadAt (.bin .mul (.imm 32) (.load Icell)))) ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lbMScan] ++
  [.label l.lbMScanDone] ++
  jumpIfZ (.load T0) l.lbSer ++
  -- ONE := 1
  store ONE (.imm 1) ++
  -- base reduction (bitwise Horner)
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
  -- ACC := 1 mod m
  callAddMod ACC ONE l.lamCallAccInit l.lamEntry ++
  -- exponent scan
  store Icell (.imm 0) ++
  [.label l.lbEScan] ++
  jumpUnlessLt (.load Icell) (.load ES) l.lbSer ++
  store Wcell (cdbCell EO) ++
  jumpIfNz (.load Wcell) l.lbInit ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lbEScan] ++
  -- found: top set bit
  [.label l.lbInit] ++
  store Jcell (.imm 7) ++
  [.label l.lbTop] ++
  jumpIfNz bitTest l.lbInitAcc ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  [.jump l.lbTop] ++
  [.label l.lbInitAcc] ++
  -- acc := base
  store I2 (.imm 0) ++
  [.label l.lbAccInit] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lbAccInitDone ++
  storeAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm BASE) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lbAccInit] ++
  [.label l.lbAccInitDone] ++
  -- top byte's remaining bits
  [.label l.lbTopBits] ++
  jumpIfZ (.load Jcell) l.lbRest ++
  store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  callMulMod ACC l.lsqRet1 l.lmmEntry ++
  jumpIfZ bitTest l.lbTopBitsSkip ++
  callMulMod BASE l.lmulRet1 l.lmmEntry ++
  [.label l.lbTopBitsSkip] ++
  [.jump l.lbTopBits] ++
  -- remaining bytes
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
  [.jump l.lbBytes] ++
  -- serialize
  [.label l.lbSer] ++
  store Icell (.imm 0) ++
  [.label l.lbSerLoop] ++
  jumpUnlessLt (.load Icell) (.load MS) l.lbReturn ++
  store T0 (.bin .sub (.bin .sub (.load MS) (.imm 1)) (.load Icell)) ++
  storeAt8 (.bin .add (.imm RET) (.load Icell))
    (.bin .shr (.bin .mul (.imm 8) (.bin .mod (.load T0) (.imm 32)))
      (loadAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.bin .div (.load T0) (.imm 32)))))) ++
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  [.jump l.lbSerLoop] ++
  [.label l.lbReturn] ++
  (compileExpr (.load MS) ++ compileExpr (.imm RET) ++ [.op .ret])

def secAddModProc (l : ProgLabels) : List Asm := 
  [.label l.lamEntry] ++
  store C1 (.imm 0) ++
  store I2 (.imm 0) ++
  [.label l.lamAdd] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lamSubStart ++
  store AOFF (.bin .mul (.imm 32) (.load I2)) ++
  store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
  store AY (loadAt (.bin .add (.load ASRC) (.load AOFF))) ++
  store AS (.bin .add (.load AX) (.load AY)) ++
  store AZ (.bin .add (.load AS) (.load C1)) ++
  store C1 (.bin .or (.bin .lt (.load AS) (.load AX)) (.bin .lt (.load AZ) (.load AS))) ++
  storeAt (.bin .add (.load ADST) (.load AOFF)) (.load AZ) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lamAdd] ++
  [.label l.lamSubStart] ++
  store C2 (.imm 0) ++
  store I2 (.imm 0) ++
  [.label l.amSub] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lamSel ++
  store AOFF (.bin .mul (.imm 32) (.load I2)) ++
  store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
  store AY (loadAt (.load AOFF)) ++
  store AS (.bin .sub (.load AX) (.load AY)) ++
  store AZ (.bin .sub (.load AS) (.load C2)) ++
  store C2 (.bin .or (.bin .lt (.load AX) (.load AY)) (.bin .lt (.load AS) (.load C2))) ++
  storeAt (.bin .add (.imm SUBC) (.load AOFF)) (.load AZ) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.amSub] ++
  [.label l.lamSel] ++
  jumpIfNz (.bin .or (.load C1) (.un .iszero (.load C2))) l.lamDoCopy ++
  [.jump l.lamDone] ++
  [.label l.lamDoCopy] ++
  store I2 (.imm 0) ++
  [.label l.lamCopy] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lamDone ++
  storeAt (.bin .add (.load ADST) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lamCopy] ++
  [.label l.lamDone] ++
  [.dynJump]

def secMulModProc (l : ProgLabels) : List Asm := 
  [.label l.lmmEntry] ++
  store HIcell (.load Ncell) ++
  [.label l.lmScanTop] ++
  jumpIfZ (.load HIcell) l.lmZero ++
  store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
  jumpIfZ (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) l.lmScanTop ++
  store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
  store T1 (.imm 256) ++
  [.label l.lmTopBit] ++
  store T1 (.bin .sub (.load T1) (.imm 1)) ++
  jumpIfZ (bitTestOf T0 T1) l.lmTopBit ++
  -- out := a
  store I2 (.imm 0) ++
  [.label l.lmCopy] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lmBits ++
  storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lmCopy] ++
  [.label l.lmBits] ++
  jumpIfZ (.load T1) l.lmNextLimb ++
  store T1 (.bin .sub (.load T1) (.imm 1)) ++
  store ADST (.imm OUT) ++ store ASRC (.imm OUT) ++
  [.pushLabel l.lmSqRet, .jump l.lamEntry, .label l.lmSqRet] ++
  jumpIfZ (bitTestOf T0 T1) l.lmBits ++
  store ADST (.imm OUT) ++ store ASRC (.imm ACC) ++
  [.pushLabel l.lmAddRet, .jump l.lamEntry, .label l.lmAddRet] ++
  [.jump l.lmBits] ++
  [.label l.lmNextLimb] ++
  jumpIfZ (.load HIcell) l.lmDone ++
  store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
  store T1 (.imm 256) ++
  store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
  [.jump l.lmBits] ++
  [.label l.lmZero] ++
  store I2 (.imm 0) ++
  [.label l.lmZeroLoop] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lmDone ++
  storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2))) (.imm 0) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lmZeroLoop] ++
  -- ACC := OUT: the product lands in OUT, but the documented call contract
  -- (`ACC := ACC · BPTR mod MOD`) and every caller expect it in ACC.
  [.label l.lmDone] ++
  store I2 (.imm 0) ++
  [.label l.lmRetCopy] ++
  jumpUnlessLt (.load I2) (.load Ncell) l.lmExit ++
  storeAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lmRetCopy] ++
  [.label l.lmExit] ++
  [.dynJump]

def secHalt (l : ProgLabels) : List Asm := 
  [.label l.linvalid, .op .invalid] ++
  [.label l.lretEmpty, .push (BitVec.ofNat 256 0), .push (BitVec.ofNat 256 0), .op .ret] ++
  [.jump l.lretEmpty]

/-- The program's trailing sections: the halt stubs and the two procedure
bodies (everything after `secBigPath`). -/
def progTail : List Asm :=
  secHalt programLabels ++ secAddModProc programLabels ++ secMulModProc programLabels

set_option maxHeartbeats 0 in
/-- The program is its six sections in order, exactly as `genProgram`
concatenates them (the procedure bodies trail the halt stubs). Deciding the
equation forces both sides once (cheap: full evaluation of the program is
~1s kernel work), whereas a structural `rfl` degenerates because the
generator's let-bound chunks and the spelled sections only align after
normalization. -/
theorem programAsm_eq :
    programAsm = secHeader programLabels ++ secWordPath programLabels ++
      secBigPath programLabels ++ progTail := by decide

/-- Resolve a label defined in `secHalt` (after every other section, but
before the procedure bodies that trail it). The section-membership premises
are discharged by `decide` on the concrete program. -/
theorem resolve_haltLabel {lbl : Label} {pre tail : List Asm}
    (h1 : lbl ∉ labelDefs (secHeader programLabels))
    (h2 : lbl ∉ labelDefs (secWordPath programLabels))
    (h3 : lbl ∉ labelDefs (secBigPath programLabels))
    (hp : lbl ∉ labelDefs pre)
    (hsplit : progTail = pre ++ [Asm.label lbl] ++ tail) :
    findLabel lbl programAsm = some tail := by
  rw [programAsm_eq, hsplit]
  simp only [List.append_assoc]
  rw [findLabel_pre h1, findLabel_pre h2, findLabel_pre h3]
  exact findLabel_here hp

/-! ## Word arithmetic -/

/-- Shorthand for the 256-bit word carrying the natural `n`. -/
local notation:max "W " n:max => BitVec.ofNat 256 n

theorem two_pow_256_eq : (2 : Nat) ^ 256 = 256 ^ 32 := by
  rw [show (2 : Nat) ^ 256 = (2 : Nat) ^ (8 * 32) from by norm_num, Nat.pow_mul]

theorem toNat_W {n : Nat} (h : n < 2 ^ 256) : (W n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem W_eq_zero {n : Nat} (h : n < 2 ^ 256) : W n = 0 ↔ n = 0 := by
  constructor
  · intro he
    have h2 : (W n).toNat = 0 := by rw [he]; rfl
    rwa [toNat_W h] at h2
  · intro he; subst he; rfl

theorem W_ne_zero {n : Nat} (hn : n ≠ 0) (h : n < 2 ^ 256) : W n ≠ 0 :=
  fun he => hn ((W_eq_zero h).mp he)

theorem W_ult {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a < b) :
    (W a).ult (W b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact decide_eq_true h

theorem W_nult {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : b ≤ a) :
    ¬ (W a).ult (W b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact fun hc => absurd (of_decide_eq_true hc) (Nat.not_lt.2 h)

theorem W_add {a b : Nat} (h : a + b < 2 ^ 256) : W a + W b = W (a + b) := by
  have ha : a < 2 ^ 256 := by omega
  have hb : b < 2 ^ 256 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_W ha, toNat_W hb, toNat_W h, Nat.mod_eq_of_lt h]

theorem W_sub {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 256) :
    W a - W b = W (a - b) := by
  have hlt : a - b < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  have hbw : b < 2 ^ 256 := Nat.lt_of_le_of_lt hb ha
  apply BitVec.eq_of_toNat_eq
  have hEq : 2 ^ 256 - b + a = 2 ^ 256 + (a - b) := by omega
  have e1 : (W a - W b).toNat = (2 ^ 256 - b + a) % 2 ^ 256 := by
    simp only [BitVec.toNat_sub, toNat_W ha, toNat_W hbw]
  rw [e1, hEq, toNat_W hlt, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

theorem W_mul (a b : Nat) : W a * W b = W (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [← Nat.mul_mod]

theorem W_div {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    W a / W b = W (a / b) := by
  apply BitVec.eq_of_toNat_eq
  have hab : (W a / W b).toNat = (W a).toNat / (W b).toNat := by simp
  rw [hab, toNat_W ha, toNat_W hb, toNat_W (Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha)]

theorem W_mod {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    W a % W b = W (a % b) := by
  apply BitVec.eq_of_toNat_eq
  have hab : (W a % W b).toNat = (W a).toNat % (W b).toNat := by simp
  rw [hab, toNat_W ha, toNat_W hb, toNat_W (Nat.lt_of_le_of_lt (Nat.mod_le a b) ha)]

theorem W_shr {v : Nat} (hv : v < 2 ^ 256) (k : Nat) :
    W v >>> k = W (v / 2 ^ k) := by
  have hlt : v / 2 ^ k < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]

/-! ## The calldata bridge -/

/-- `bytesToNatPadded` is the big-endian `wordVal` of the calldata bytes. -/
theorem bytesToNatPadded_wordVal (b : ByteArray) (p k : Nat) :
    bytesToNatPadded b p k = wordVal (byteFrom b.toList) p k := by
  induction k generalizing p with
  | zero => rw [bytesToNatPadded_zero_width]; rfl
  | succ k ih =>
      rw [bytesToNatPadded_succ, ih, wordVal_succ]

/-- The `calldataload` word's value is the 32-byte padded read. -/
theorem wordFrom_toNat_bytes (calldata : ByteArray) (p : Nat) :
    (wordFrom calldata.toList p).toNat =
      bytesToNatPadded calldata p 32 := by
  rw [wordFrom_toNat, bytesToNatPadded_wordVal]

/-- The `calldataload` word, as a value word. -/
theorem wordFrom_eq_W (calldata : ByteArray) (p : Nat) :
    wordFrom calldata.toList p = W (bytesToNatPadded calldata p 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [wordFrom_toNat_bytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have hV := bytesToNatPadded_lt_pow calldata p 32
  rwa [show (256 : Nat) ^ 32 = 2 ^ 256 from two_pow_256_eq.symm] at hV

/-- A size word below `2 ^ 256`. -/
theorem size_lt (n : Nat) (h : n ≤ 1024) : n < 2 ^ 256 := by
  have h2 : (1024 : Nat) < 2 ^ 256 := by norm_num
  omega

/-- `byte(0, calldataload p)` is the calldata byte at `p`, as a word. -/
theorem evalExpr_cdb {e : Expr} {yst : EvmState} {p : Nat}
    (haddr : (evalExpr e yst).toNat = p) :
    evalExpr (Expr.cdb e) yst = W (byteFrom yst.env.calldata p).toNat := by
  have h1 : evalExpr (Expr.cdb e) yst
      = evalBin .byte (0 : U256) (wordFrom yst.env.calldata p) := by
    simp only [evalExpr, haddr]
  rw [h1]
  show (if 32 ≤ (0 : U256).toNat then 0
      else (wordFrom yst.env.calldata p >>> (248 - 8 * (0 : U256).toNat)) &&& 255) = _
  rw [show ((0 : U256)).toNat = 0 from rfl]
  norm_num only
  show (wordFrom yst.env.calldata p >>> 248) &&& 255 = _
  have h31 : (8 : Nat) * 31 = 248 := by norm_num
  have hXlt : (wordFrom yst.env.calldata p >>> 248).toNat < 256 := by
    have hb := BitVec.isLt (wordFrom yst.env.calldata p)
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hb ⊢
    have hpow : (2 : Nat) ^ 248 * 256 = 2 ^ 256 := by
      rw [show (256 : Nat) = (2 : Nat) ^ 8 from by norm_num, ← Nat.pow_add]
      norm_num
    omega
  have hshift : (wordFrom yst.env.calldata p >>> 248).toNat
      = (byteFrom yst.env.calldata p).toNat := by
    have hh := byteAt_wordFrom_first (data := yst.env.calldata) (p := p)
    simp only [byteAt, h31] at hh
    have hcong := congrArg UInt8.toNat hh
    rw [show (UInt8.ofNat (wordFrom yst.env.calldata p >>> 248).toNat).toNat
        = (wordFrom yst.env.calldata p >>> 248).toNat % 256 from by simp,
      Nat.mod_eq_of_lt hXlt] at hcong
    exact hcong
  have hlt : (byteFrom yst.env.calldata p).toNat < 2 ^ 256 :=
    (byteFrom yst.env.calldata p).toNat_lt.trans (by norm_num)
  apply BitVec.eq_of_toNat_eq
  have e2 : ((wordFrom yst.env.calldata p >>> 248) &&& (255 : U256)).toNat
      = (wordFrom yst.env.calldata p >>> 248).toNat &&& 255 := by
    simp only [BitVec.toNat_and]
    rfl
  rw [e2, hshift]
  have hand : (byteFrom yst.env.calldata p).toNat &&& 255
      = (byteFrom yst.env.calldata p).toNat := by
    have hmod := Nat.and_two_pow_sub_one_eq_mod (byteFrom yst.env.calldata p).toNat 8
    norm_num at hmod
    omega
  rw [hand, toNat_W hlt]

/-- `evalBin .lt` on value words, zero case. -/
theorem evalBin_lt_zero {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : b ≤ a) : evalBin .lt (W a) (W b) = 0 := by
  show b2w ((W a).ult (W b)) = 0
  simp only [W_nult ha hb h, b2w]
  rfl

/-- `evalBin .lt` on value words, nonzero case. -/
theorem evalBin_lt_ne {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : a < b) : evalBin .lt (W a) (W b) ≠ 0 := by
  show b2w ((W a).ult (W b)) ≠ 0
  simp only [W_ult ha hb h, b2w]
  decide

/-! ## The header fragment -/

/-- The Yul-side initial state the challenge fixes. -/
def y0c (calldata : ByteArray) : EvmState :=
  initYst (assemble programInstrs) calldata

theorem y0c_memory (calldata : ByteArray) : (y0c calldata).memory = fun _ => 0 := rfl

theorem y0c_activeWords (calldata : ByteArray) : (y0c calldata).activeWords.toNat = 0 := rfl

theorem y0c_calldata (calldata : ByteArray) :
    (y0c calldata).env.calldata = calldata.toList := rfl

/-- The header's memory as a store chain: the six scalar-cell writes over
the fresh zero memory, in execution order `BS, ES, MS, BO, EO, MO`. -/
def mem0 : Nat → UInt8 := fun _ => 0

def memBS (cd : ByteArray) : Nat → UInt8 := storeWord mem0 BS (W (baseSize cd))

def memES (cd : ByteArray) : Nat → UInt8 := storeWord (memBS cd) ES (W (exponentSize cd))

/-- The memory at the `msize = 0` branch point (after `BS/ES/MS`). -/
def memMS (cd : ByteArray) : Nat → UInt8 := storeWord (memES cd) MS (W (modulusSize cd))

def memBO (cd : ByteArray) : Nat → UInt8 := storeWord (memMS cd) BO (W 96)

def memEO (cd : ByteArray) : Nat → UInt8 := storeWord (memBO cd) EO (W (96 + baseSize cd))

def memMO (cd : ByteArray) : Nat → UInt8 :=
  storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd))

def hdrMem (cd : ByteArray) : Nat → UInt8 := memMO cd

/-- The header states after each store (`BS`→225, `ES`→226, `MS`→227,
`BO`→228, `EO`→229, `MO`→230 active words). The `msize = 0` return branches
at `hst3`, so the offset cells are still zero there. -/
def hst1 (cd : ByteArray) : EvmState :=
  { y0c cd with memory := memBS cd, activeWords := W 225 }

def hst2 (cd : ByteArray) : EvmState :=
  { hst1 cd with memory := memES cd, activeWords := W 226 }

def hst3 (cd : ByteArray) : EvmState :=
  { hst2 cd with memory := memMS cd, activeWords := W 227 }

def hst4 (cd : ByteArray) : EvmState :=
  { hst3 cd with memory := memBO cd, activeWords := W 228 }

def hst5 (cd : ByteArray) : EvmState :=
  { hst4 cd with memory := memEO cd, activeWords := W 229 }

/-- The header's exit state: the six scalar cells written (`hdrMem`),
`activeWords` exactly 230, the environment untouched. This is the state both
compute paths are entered with. -/
def hst6 (cd : ByteArray) : EvmState :=
  { hst5 cd with memory := memMO cd, activeWords := W 230 }

theorem hst1_activeWords (cd : ByteArray) : (hst1 cd).activeWords.toNat = 225 := rfl

theorem hst2_activeWords (cd : ByteArray) : (hst2 cd).activeWords.toNat = 226 := rfl

theorem hst3_activeWords (cd : ByteArray) : (hst3 cd).activeWords.toNat = 227 := rfl

theorem hst4_activeWords (cd : ByteArray) : (hst4 cd).activeWords.toNat = 228 := rfl

theorem hst5_activeWords (cd : ByteArray) : (hst5 cd).activeWords.toNat = 229 := rfl

/-- `activeWords` of the exit state is exactly 230. -/
theorem hst6_activeWords (cd : ByteArray) : (hst6 cd).activeWords.toNat = 230 := rfl

/-- The exit state's environment is the initial one (calldata unchanged). -/
theorem hst6_env (cd : ByteArray) : (hst6 cd).env.calldata = cd.toList := rfl

theorem hst3_env (cd : ByteArray) : (hst3 cd).env.calldata = cd.toList := rfl

/-- The numeric cell addresses, as one decidable block. -/
theorem cells_num :
    BS = 7168 ∧ ES = 7200 ∧ MS = 7232 ∧ BO = 7264 ∧ EO = 7296 ∧ MO = 7328 ∧
      Ncell = 7360 ∧ Icell = 7392 ∧ TOP = 7968 ∧ T0 = 7616 ∧ T1 = 7648 ∧
      Jcell = 7424 ∧ Wcell = 7456 ∧ I2 = 7776 := by decide

/-- Disjoint-load helper on plain memory functions. -/
private theorem load_disj (m : Nat → UInt8) (p q : Nat) (v : U256)
    (h : p + 32 ≤ q ∨ q + 32 ≤ p) :
    loadWord (storeWord m p v) q = loadWord m q :=
  loadWord_storeWord_disjoint h

/-- A store strictly above the address leaves it untouched. -/
private theorem store_out (m : Nat → UInt8) (p : Nat) (v : U256) (a : Nat)
    (h : a < p) : storeWord m p v a = m a := by
  show (if p ≤ a ∧ a < p + 32 then byteAt v (31 - (a - p)) else m a) = m a
  rw [if_neg (by omega : ¬ (p ≤ a ∧ a < p + 32))]

/-- The scalar cells of `memMS`. -/
theorem memMS_cells (cd : ByteArray) :
    loadWord (memMS cd) BS = W (baseSize cd) ∧
    loadWord (memMS cd) ES = W (exponentSize cd) ∧
    loadWord (memMS cd) MS = W (modulusSize cd) := by
  obtain ⟨hBS, hES, hMS, -, -, -, -, -, -, -, -, -, -, -⟩ := cells_num
  refine ⟨?_, ?_, ?_⟩
  · rw [show memMS cd = storeWord (memES cd) MS (W (modulusSize cd)) from rfl,
      load_disj (memES cd) MS BS _ (Or.inr (by omega)),
      show memES cd = storeWord (memBS cd) ES (W (exponentSize cd)) from rfl,
      load_disj (memBS cd) ES BS _ (Or.inr (by omega)),
      show memBS cd = storeWord mem0 BS (W (baseSize cd)) from rfl]
    exact loadWord_storeWord_self mem0 BS (W (baseSize cd))
  · rw [show memMS cd = storeWord (memES cd) MS (W (modulusSize cd)) from rfl,
      load_disj (memES cd) MS ES _ (Or.inr (by omega))]
    exact loadWord_storeWord_self (memBS cd) ES (W (exponentSize cd))
  · rw [show memMS cd = storeWord (memES cd) MS (W (modulusSize cd)) from rfl]
    exact loadWord_storeWord_self (memES cd) MS (W (modulusSize cd))

/-- The scalar cells of the header's exit memory (and of the two intermediate
offset memories). -/
theorem hdrMem_cells (cd : ByteArray) :
    loadWord (hdrMem cd) BS = W (baseSize cd) ∧
    loadWord (hdrMem cd) ES = W (exponentSize cd) ∧
    loadWord (hdrMem cd) MS = W (modulusSize cd) ∧
    loadWord (hdrMem cd) BO = W 96 ∧
    loadWord (hdrMem cd) EO = W (96 + baseSize cd) ∧
    loadWord (hdrMem cd) MO = W (96 + baseSize cd + exponentSize cd) ∧
    loadWord (memBO cd) BS = W (baseSize cd) ∧
    loadWord (memBO cd) ES = W (exponentSize cd) ∧
    loadWord (memBO cd) MS = W (modulusSize cd) ∧
    loadWord (memEO cd) BS = W (baseSize cd) ∧
    loadWord (memEO cd) ES = W (exponentSize cd) ∧
    loadWord (memEO cd) MS = W (modulusSize cd) ∧
    loadWord (memEO cd) EO = W (96 + baseSize cd) := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, -, -, -, -, -, -, -, -⟩ := cells_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show hdrMem cd = memMO cd from rfl,
      show memMO cd = storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd)) from rfl,
      load_disj (memEO cd) MO BS _ (Or.inr (by omega)),
      show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
      load_disj (memBO cd) EO BS _ (Or.inr (by omega)),
      show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO BS _ (Or.inr (by omega))]
    exact (memMS_cells cd).1
  · rw [show hdrMem cd = memMO cd from rfl,
      show memMO cd = storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd)) from rfl,
      load_disj (memEO cd) MO ES _ (Or.inr (by omega)),
      show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
      load_disj (memBO cd) EO ES _ (Or.inr (by omega)),
      show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO ES _ (Or.inr (by omega))]
    exact (memMS_cells cd).2.1
  · rw [show hdrMem cd = memMO cd from rfl,
      show memMO cd = storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd)) from rfl,
      load_disj (memEO cd) MO MS _ (Or.inr (by omega)),
      show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
      load_disj (memBO cd) EO MS _ (Or.inr (by omega)),
      show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO MS _ (Or.inr (by omega))]
    exact (memMS_cells cd).2.2
  · rw [show hdrMem cd = memMO cd from rfl,
      show memMO cd = storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd)) from rfl,
      load_disj (memEO cd) MO BO _ (Or.inr (by omega)),
      show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
      load_disj (memBO cd) EO BO _ (Or.inr (by omega))]
    exact loadWord_storeWord_self (memMS cd) BO (W 96)
  · rw [show hdrMem cd = memMO cd from rfl,
      show memMO cd = storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd)) from rfl,
      load_disj (memEO cd) MO EO _ (Or.inr (by omega))]
    exact loadWord_storeWord_self (memBO cd) EO (W (96 + baseSize cd))
  · rw [show hdrMem cd = memMO cd from rfl,
      show memMO cd = storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd)) from rfl]
    exact loadWord_storeWord_self (memEO cd) MO (W (96 + baseSize cd + exponentSize cd))
  · rw [show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO BS _ (Or.inr (by omega))]
    exact (memMS_cells cd).1
  · rw [show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO ES _ (Or.inr (by omega))]
    exact (memMS_cells cd).2.1
  · rw [show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO MS _ (Or.inr (by omega))]
    exact (memMS_cells cd).2.2
  · rw [show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
      load_disj (memBO cd) EO BS _ (Or.inr (by omega)),
      show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO BS _ (Or.inr (by omega))]
    exact (memMS_cells cd).1
  · rw [show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
      load_disj (memBO cd) EO ES _ (Or.inr (by omega)),
      show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO ES _ (Or.inr (by omega))]
    exact (memMS_cells cd).2.1
  · rw [show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
      load_disj (memBO cd) EO MS _ (Or.inr (by omega)),
      show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
      load_disj (memMS cd) BO MS _ (Or.inr (by omega))]
    exact (memMS_cells cd).2.2
  · rw [show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl]
    exact loadWord_storeWord_self (memBO cd) EO (W (96 + baseSize cd))

/-- The scalar cells of the header's exit state (and of `hst3`). -/
theorem hst6_cells (cd : ByteArray) :
    loadWord (hst6 cd).memory BS = W (baseSize cd) ∧
    loadWord (hst6 cd).memory ES = W (exponentSize cd) ∧
    loadWord (hst6 cd).memory MS = W (modulusSize cd) ∧
    loadWord (hst6 cd).memory BO = W 96 ∧
    loadWord (hst6 cd).memory EO = W (96 + baseSize cd) ∧
    loadWord (hst6 cd).memory MO = W (96 + baseSize cd + exponentSize cd) ∧
    loadWord (hst3 cd).memory BS = W (baseSize cd) ∧
    loadWord (hst3 cd).memory ES = W (exponentSize cd) ∧
    loadWord (hst3 cd).memory MS = W (modulusSize cd) :=
  ⟨(hdrMem_cells cd).1, (hdrMem_cells cd).2.1, (hdrMem_cells cd).2.2.1,
    (hdrMem_cells cd).2.2.2.1, (hdrMem_cells cd).2.2.2.2.1,
    (hdrMem_cells cd).2.2.2.2.2.1, (memMS_cells cd).1, (memMS_cells cd).2.1,
    (memMS_cells cd).2.2⟩

/-- Everything below the scalar block (`BS`) is still fresh zero memory: no
header store touches the operand regions `MOD/BASE/ACC/OUT/ONE/SUBC/RET`. -/
theorem hst6_zero (cd : ByteArray) : ∀ a, a < BS → (hst6 cd).memory a = 0 := by
  obtain ⟨hBS, hES, hMS, hBO, hEO, hMO, -, -, -, -, -, -, -, -⟩ := cells_num
  intro a ha
  show hdrMem cd a = 0
  rw [show hdrMem cd = memMO cd from rfl,
    show memMO cd = storeWord (memEO cd) MO (W (96 + baseSize cd + exponentSize cd)) from rfl,
    store_out _ _ _ a (by omega),
    show memEO cd = storeWord (memBO cd) EO (W (96 + baseSize cd)) from rfl,
    store_out _ _ _ a (by omega),
    show memBO cd = storeWord (memMS cd) BO (W 96) from rfl,
    store_out _ _ _ a (by omega),
    show memMS cd = storeWord (memES cd) MS (W (modulusSize cd)) from rfl,
    store_out _ _ _ a (by omega),
    show memES cd = storeWord (memBS cd) ES (W (exponentSize cd)) from rfl,
    store_out _ _ _ a (by omega),
    show memBS cd = storeWord mem0 BS (W (baseSize cd)) from rfl,
    store_out _ _ _ a (by omega)]
  rfl

/-- The same freshness fact for `hst3`. -/
theorem hst3_zero (cd : ByteArray) : ∀ a, a < BS → (hst3 cd).memory a = 0 := by
  obtain ⟨hBS, hES, hMS, -, -, -, -, -, -, -, -, -, -, -⟩ := cells_num
  intro a ha
  show memMS cd a = 0
  rw [show memMS cd = storeWord (memES cd) MS (W (modulusSize cd)) from rfl,
    store_out _ _ _ a (by omega),
    show memES cd = storeWord (memBS cd) ES (W (exponentSize cd)) from rfl,
    store_out _ _ _ a (by omega),
    show memBS cd = storeWord mem0 BS (W (baseSize cd)) from rfl,
    store_out _ _ _ a (by omega)]
  rfl

/-! ### The header chain -/

/-- The header section, right-associated so each statement faces its
continuation. -/
def hdrChain (l : ProgLabels) (rest : List Asm) : List Asm :=
  store BS (.cdload (.imm 0)) ++
    (store ES (.cdload (.imm 32)) ++
    (store MS (.cdload (.imm 64)) ++
    (jumpIfNz (.bin .or (.bin .or (.bin .lt (.imm 1024) (.load BS))
      (.bin .lt (.imm 1024) (.load ES))) (.bin .lt (.imm 1024) (.load MS))) l.linvalid ++
    (jumpIfZ (.load MS) l.lretEmpty ++
    (store BO (.imm 96) ++
    (store EO (.bin .add (.imm 96) (.load BS)) ++
    (store MO (.bin .add (.load EO) (.load ES)) ++
    (jumpIfNz (.bin .lt (.imm 32) (.load MS)) l.lbig ++ rest))))))))

theorem secHeader_append (rest : List Asm) :
    secHeader programLabels ++ rest = hdrChain programLabels rest := by rfl

/-- `calldataload 0` is the base-size word. -/
private theorem evalExpr_BS (cd : ByteArray) :
    evalExpr (.cdload (.imm 0)) (y0c cd) = W (baseSize cd) := by
  show wordFrom (y0c cd).env.calldata ((W 0).toNat) = _
  rw [y0c_calldata, show ((W 0 : U256)).toNat = 0 from rfl, wordFrom_eq_W]
  rfl

private theorem evalExpr_ES (cd : ByteArray) :
    evalExpr (.cdload (.imm 32)) (y0c cd) = W (exponentSize cd) := by
  show wordFrom (y0c cd).env.calldata ((W 32).toNat) = _
  rw [y0c_calldata, show ((W 32 : U256)).toNat = 32 from rfl, wordFrom_eq_W]
  rfl

private theorem evalExpr_MS (cd : ByteArray) :
    evalExpr (.cdload (.imm 64)) (y0c cd) = W (modulusSize cd) := by
  show wordFrom (y0c cd).env.calldata ((W 64).toNat) = _
  rw [y0c_calldata, show ((W 64 : U256)).toNat = 64 from rfl, wordFrom_eq_W]
  rfl

/-- A cell load pinned at a known `activeWords` value. -/
private theorem pin_load {q : Nat} {yst : EvmState} {aw : Nat}
    (hq : q < 2 ^ 256) (haw : yst.activeWords.toNat = aw) (hpin : q + 32 ≤ 32 * aw) :
    exprOK (Expr.load q) yst := by
  show q < 2 ^ 256 ∧ q + 32 ≤ 32 * yst.activeWords.toNat
  rw [haw]
  exact ⟨hq, hpin⟩

/-- The `store_steps_exact` conclusion state, flattened. -/
private theorem exact_store_state {yst : EvmState} {c : Nat} {v : U256} {aw : Nat}
    (hc : c < 2 ^ 256) (haw : activeWordsAfter yst.activeWords.toNat c 32 = aw) :
    { touchMemory yst (c % 2 ^ 256) 32 with memory := storeWord yst.memory (c % 2 ^ 256) v } =
      { yst with memory := storeWord yst.memory c v, activeWords := W aw } := by
  have hcm : c % 2 ^ 256 = c := Nat.mod_eq_of_lt hc
  rw [hcm, show touchMemory yst c 32 =
      { yst with activeWords := BitVec.ofNat 256 (activeWordsAfter yst.activeWords.toNat c 32) }
      from rfl, haw]

/-- One header store: exact `activeWords` growth plus the memory write. -/
private theorem store_step {c : Nat} {e : Expr} {v : U256} {aw : Nat} {yst : EvmState}
    {k : List Asm}
    (he : exprOK e yst) (hc : c < 2 ^ 256)
    (haw : activeWordsAfter yst.activeWords.toNat c 32 = aw)
    (hval : evalExpr e yst = v) :
    ASteps programAsm ⟨store c e ++ k, [], yst⟩
      ⟨k, [], { yst with memory := storeWord yst.memory c v, activeWords := W aw }⟩ := by
  have h := store_steps_exact (model := localModel) (prog := programAsm) (c := c)
    (e := e) (k := k) (σ := []) he
  rw [hval, exact_store_state hc haw] at h
  exact h

/-- The six header stores, one lemma each, with the exact resulting state. -/
private theorem step_BS (cd : ByteArray) {k : List Asm} :
    ASteps programAsm ⟨store BS (.cdload (.imm 0)) ++ k, [], y0c cd⟩ ⟨k, [], hst1 cd⟩ :=
  store_step (c := BS) (e := .cdload (.imm 0)) (v := W (baseSize cd)) (aw := 225)
    (yst := y0c cd) trivial (by decide)
    (by rw [y0c_activeWords]; decide) (evalExpr_BS cd)

private theorem step_ES (cd : ByteArray) {k : List Asm} :
    ASteps programAsm ⟨store ES (.cdload (.imm 32)) ++ k, [], hst1 cd⟩ ⟨k, [], hst2 cd⟩ :=
  store_step (c := ES) (e := .cdload (.imm 32)) (v := W (exponentSize cd)) (aw := 226)
    (yst := hst1 cd) trivial (by decide)
    (by rw [hst1_activeWords]; decide) (evalExpr_ES cd)

private theorem step_MS (cd : ByteArray) {k : List Asm} :
    ASteps programAsm ⟨store MS (.cdload (.imm 64)) ++ k, [], hst2 cd⟩ ⟨k, [], hst3 cd⟩ :=
  store_step (c := MS) (e := .cdload (.imm 64)) (v := W (modulusSize cd)) (aw := 227)
    (yst := hst2 cd) trivial (by decide)
    (by rw [hst2_activeWords]; decide) (evalExpr_MS cd)

private theorem step_BO (cd : ByteArray) {k : List Asm} :
    ASteps programAsm ⟨store BO (.imm 96) ++ k, [], hst3 cd⟩ ⟨k, [], hst4 cd⟩ :=
  store_step (c := BO) (e := .imm 96) (v := W 96) (aw := 228)
    (yst := hst3 cd) trivial (by decide)
    (by rw [hst3_activeWords]; decide) rfl

private theorem step_EO (cd : ByteArray) (hb : baseSize cd ≤ 1024) {k : List Asm} :
    ASteps programAsm
      ⟨store EO (.bin .add (.imm 96) (.load BS)) ++ k, [], hst4 cd⟩ ⟨k, [], hst5 cd⟩ := by
  refine store_step (c := EO) (e := .bin .add (.imm 96) (.load BS))
    (v := W (96 + baseSize cd)) (aw := 229) (yst := hst4 cd) ?_ (by decide)
    (by rw [hst4_activeWords]; decide) ?_
  · show binOK .add = true ∧ exprOK (.imm 96) (hst4 cd) ∧
      exprOK (Expr.load BS) (hst4 cd)
    exact ⟨rfl, trivial, pin_load (by decide) (hst4_activeWords cd) (by decide)⟩
  · show evalBin .add (W 96) (loadWord (memBO cd) BS) = _
    rw [show loadWord (memBO cd) BS = W (baseSize cd)
        from (hdrMem_cells cd).2.2.2.2.2.2.1]
    show W 96 + W (baseSize cd) = _
    rw [W_add (a := 96) (b := baseSize cd) (by omega)]

private theorem step_MO (cd : ByteArray) (hb : baseSize cd ≤ 1024)
    (he : exponentSize cd ≤ 1024) {k : List Asm} :
    ASteps programAsm
      ⟨store MO (.bin .add (.load EO) (.load ES)) ++ k, [], hst5 cd⟩ ⟨k, [], hst6 cd⟩ := by
  refine store_step (c := MO) (e := .bin .add (.load EO) (.load ES))
    (v := W (96 + baseSize cd + exponentSize cd)) (aw := 230) (yst := hst5 cd) ?_
    (by decide) (by rw [hst5_activeWords]; decide) ?_
  · show binOK .add = true ∧ exprOK (Expr.load EO) (hst5 cd) ∧
      exprOK (Expr.load ES) (hst5 cd)
    exact ⟨rfl, pin_load (by decide) (hst5_activeWords cd) (by decide),
      pin_load (by decide) (hst5_activeWords cd) (by decide)⟩
  · show evalBin .add (loadWord (memEO cd) EO) (loadWord (memEO cd) ES) = _
    rw [show loadWord (memEO cd) EO = W (96 + baseSize cd)
        from (hdrMem_cells cd).2.2.2.2.2.2.2.2.2.2.2.2,
      show loadWord (memEO cd) ES = W (exponentSize cd)
        from (hdrMem_cells cd).2.2.2.2.2.2.2.2.2.2.1]
    show W (96 + baseSize cd) + W (exponentSize cd) = _
    rw [W_add (a := 96 + baseSize cd) (b := exponentSize cd) (by omega)]

/-- The EIP-7823 bound check falls through for a valid input. -/
private theorem check_falls (cd : ByteArray) (hv : ValidInput cd) {k : List Asm} :
    ASteps programAsm
      ⟨jumpIfNz (.bin .or (.bin .or (.bin .lt (.imm 1024) (.load BS))
        (.bin .lt (.imm 1024) (.load ES))) (.bin .lt (.imm 1024) (.load MS)))
        programLabels.linvalid ++ k, [], hst3 cd⟩ ⟨k, [], hst3 cd⟩ := by
  obtain ⟨-, hb, he, hm⟩ := hv
  have hchk : ((evalBin .lt (W 1024) (loadWord (memMS cd) BS)
      ||| evalBin .lt (W 1024) (loadWord (memMS cd) ES))
      ||| evalBin .lt (W 1024) (loadWord (memMS cd) MS)) = 0 := by
    rw [show loadWord (memMS cd) BS = W (baseSize cd) from (memMS_cells cd).1,
      show loadWord (memMS cd) ES = W (exponentSize cd) from (memMS_cells cd).2.1,
      show loadWord (memMS cd) MS = W (modulusSize cd) from (memMS_cells cd).2.2,
      evalBin_lt_zero (by norm_num) (size_lt _ hb) (by omega),
      evalBin_lt_zero (by norm_num) (size_lt _ he) (by omega),
      evalBin_lt_zero (by norm_num) (size_lt _ hm) (by omega)]
    rfl
  refine jumpIfNz_fall (model := localModel) (prog := programAsm)
    (e := .bin .or (.bin .or (.bin .lt (.imm 1024) (.load BS))
      (.bin .lt (.imm 1024) (.load ES))) (.bin .lt (.imm 1024) (.load MS)))
    ?_ ?_
  · show binOK .or = true ∧
      (binOK .or = true ∧
        (binOK .lt = true ∧ exprOK (.imm 1024) (hst3 cd) ∧
          exprOK (Expr.load BS) (hst3 cd)) ∧
        (binOK .lt = true ∧ exprOK (.imm 1024) (hst3 cd) ∧
          exprOK (Expr.load ES) (hst3 cd))) ∧
      (binOK .lt = true ∧ exprOK (.imm 1024) (hst3 cd) ∧
        exprOK (Expr.load MS) (hst3 cd))
    exact ⟨rfl, ⟨rfl, ⟨rfl, trivial, pin_load (by decide) (hst3_activeWords cd) (by decide)⟩,
      ⟨rfl, trivial, pin_load (by decide) (hst3_activeWords cd) (by decide)⟩⟩,
      rfl, trivial, pin_load (by decide) (hst3_activeWords cd) (by decide)⟩
  · show ((evalBin .lt (W 1024) (loadWord (memMS cd) BS)
        ||| evalBin .lt (W 1024) (loadWord (memMS cd) ES))
      ||| evalBin .lt (W 1024) (loadWord (memMS cd) MS)) = 0
    exact hchk

/-- The header from the initial state to the `msize = 0` branch point
(just after the `BS/ES/MS` stores and the EIP-7823 bound check, at the
`jumpIfZ (.load MS) lretEmpty` dispatch). -/
theorem header_to_ms (cd : ByteArray) (hv : ValidInput cd) {rest : List Asm} :
    ASteps programAsm ⟨secHeader programLabels ++ rest, [], y0c cd⟩
      ⟨jumpIfZ (.load MS) programLabels.lretEmpty ++
        (store BO (.imm 96) ++
        (store EO (.bin .add (.imm 96) (.load BS)) ++
        (store MO (.bin .add (.load EO) (.load ES)) ++
        (jumpIfNz (.bin .lt (.imm 32) (.load MS)) programLabels.lbig ++ rest)))),
        [], hst3 cd⟩ := by
  rw [secHeader_append]
  exact (step_BS cd).trans
    ((step_ES cd).trans ((step_MS cd).trans (check_falls cd hv)))

/-- The header from the `msize = 0` branch point to the big-dispatch
(requires `msize ≠ 0`): the three offset-cell stores run, each raising
`activeWords` by one word. -/
theorem header_ms_to_dispatch (cd : ByteArray) (hv : ValidInput cd)
    (hms : modulusSize cd ≠ 0) {rest : List Asm} :
    ASteps programAsm
      ⟨jumpIfZ (.load MS) programLabels.lretEmpty ++
        (store BO (.imm 96) ++
        (store EO (.bin .add (.imm 96) (.load BS)) ++
        (store MO (.bin .add (.load EO) (.load ES)) ++
        (jumpIfNz (.bin .lt (.imm 32) (.load MS)) programLabels.lbig ++ rest)))),
        [], hst3 cd⟩
      ⟨jumpIfNz (.bin .lt (.imm 32) (.load MS)) programLabels.lbig ++ rest, [], hst6 cd⟩ := by
  obtain ⟨-, hb, he, hm⟩ := hv
  refine (jumpIfZ_fall (model := localModel) (prog := programAsm)
    (e := Expr.load MS) (pin_load (by decide) (hst3_activeWords cd) (by decide))
    ?_).trans ?_
  · show loadWord (memMS cd) MS ≠ 0
    rw [(memMS_cells cd).2.2]
    exact W_ne_zero hms (size_lt _ hm)
  · exact (step_BO cd).trans
      ((step_EO cd hb).trans (step_MO cd hb he))

/-- The dead code trailing the halt stubs' `.ret`: the halt section's jump
back to `lretEmpty` (never reached — `ret` halts first) and the two
procedure bodies. -/
def haltDeadTail : List Asm :=
  [Asm.jump programLabels.lretEmpty] ++ secAddModProc programLabels ++
    secMulModProc programLabels

/-- The `msize = 0` branch: the header halts with the empty return, which is
`spec calldata` for a zero-size modulus. -/
theorem header_retEmpty (cd : ByteArray) (hv : ValidInput cd)
    (hms : modulusSize cd = 0) {rest : List Asm} :
    ∃ (b : AConf) (yst' : EvmState),
      ASteps programAsm ⟨secHeader programLabels ++ rest, [], y0c cd⟩ b ∧
      AHalt programAsm b yst' ∧
      yst'.halted = some (.ret, (spec cd).toList) := by
  have hfind : findLabel programLabels.lretEmpty programAsm =
      some ([Asm.push 0, Asm.push 0, Asm.op .ret] ++ haltDeadTail) :=
    resolve_haltLabel
      (pre := [Asm.label programLabels.linvalid, Asm.op .invalid])
      (by decide) (by decide) (by decide) (by decide) rfl
  have hz : loadWord (memMS cd) MS = 0 := by
    rw [(memMS_cells cd).2.2, hms]
    rfl
  have h5 : some (YulSemantics.EVM.HaltKind.ret, readBytes (hst3 cd).memory 0 0) =
      some (YulSemantics.EVM.HaltKind.ret, (spec cd).toList) := by
    rw [show readBytes (hst3 cd).memory 0 0 = [] from rfl,
      show (spec cd).toList = [] from by simp [spec, hms]]
  exact ⟨{ code := Asm.op .ret :: haltDeadTail, stk := words [0, 0], yst := hst3 cd },
    { touchMemory (hst3 cd) (0 : U256).toNat (0 : U256).toNat with
      halted := some (.ret, readBytes (hst3 cd).memory (0 : U256).toNat (0 : U256).toNat) },
    (header_to_ms cd hv).trans
      ((jumpIfZ_taken (model := localModel) (prog := programAsm)
        (e := Expr.load MS) (pin_load (by decide) (hst3_activeWords cd) (by decide))
        hz hfind).trans
        ((ASteps.single AStep.push).trans (ASteps.single AStep.push))),
    ahalt_ret (model := localModel) (prog := programAsm)
      (p := 0) (s := 0) (k := haltDeadTail) (σ := []) (yst := hst3 cd),
    h5⟩

/-- The word-path outcome: for `0 < msize ≤ 32` the header falls through to
the word path with the documented exit state. -/
theorem header_word (cd : ByteArray) (hv : ValidInput cd)
    (h0 : 0 < modulusSize cd) (hle : modulusSize cd ≤ 32) {rest : List Asm} :
    ASteps programAsm ⟨secHeader programLabels ++ rest, [], y0c cd⟩
      ⟨rest, [], hst6 cd⟩ := by
  have hne : modulusSize cd ≠ 0 := by omega
  refine (header_to_ms cd hv).trans
    ((header_ms_to_dispatch cd hv hne).trans ?_)
  have hexpr : exprOK (.bin .lt (.imm 32) (.load MS)) (hst6 cd) := by
    show binOK .lt = true ∧ exprOK (.imm 32) (hst6 cd) ∧
      exprOK (Expr.load MS) (hst6 cd)
    exact ⟨rfl, trivial, pin_load (by decide) (hst6_activeWords cd) (by decide)⟩
  have hv32 : evalBin .lt (W 32) (loadWord (memMO cd) MS) = 0 := by
    rw [show loadWord (memMO cd) MS = W (modulusSize cd)
        from (hdrMem_cells cd).2.2.1,
      evalBin_lt_zero (by norm_num) (size_lt _ (hv.2.2.2)) (by omega)]
  exact jumpIfNz_fall (model := localModel) (prog := programAsm)
    (e := .bin .lt (.imm 32) (.load MS)) hexpr hv32

/-- The big-path outcome: for `msize > 32` the header jumps to `.label lbig`
(the big-path entry code `c'`, resolved by the caller against the concrete
program) with the same exit state. -/
theorem header_big (cd : ByteArray) (hv : ValidInput cd)
    (hgt : 32 < modulusSize cd) {rest c' : List Asm}
    (hfind : findLabel programLabels.lbig programAsm = some c') :
    ASteps programAsm ⟨secHeader programLabels ++ rest, [], y0c cd⟩
      ⟨c', [], hst6 cd⟩ := by
  have hne : modulusSize cd ≠ 0 := by omega
  refine (header_to_ms cd hv).trans
    ((header_ms_to_dispatch cd hv hne).trans ?_)
  have hexpr : exprOK (.bin .lt (.imm 32) (.load MS)) (hst6 cd) := by
    show binOK .lt = true ∧ exprOK (.imm 32) (hst6 cd) ∧
      exprOK (Expr.load MS) (hst6 cd)
    exact ⟨rfl, trivial, pin_load (by decide) (hst6_activeWords cd) (by decide)⟩
  have hv32 : evalBin .lt (W 32) (loadWord (memMO cd) MS) ≠ 0 := by
    rw [show loadWord (memMO cd) MS = W (modulusSize cd)
        from (hdrMem_cells cd).2.2.1]
    exact evalBin_lt_ne (by norm_num) (size_lt _ (hv.2.2.2)) hgt
  exact jumpIfNz_taken (model := localModel) (prog := programAsm)
    (e := .bin .lt (.imm 32) (.load MS)) hexpr hv32 hfind

end Challenge.Modexp.Submission.Proof.Header

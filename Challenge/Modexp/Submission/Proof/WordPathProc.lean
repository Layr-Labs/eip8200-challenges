import Challenge.Modexp.Submission.Program
import Challenge.Modexp.Submission.Proof.HeaderProc
import EvmSemantics.EVM.Precompile
import Challenge.Modexp.Submission.AsmLib
import Challenge.Modexp.Submission.Proof.YulMem
import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.EvmProof.Bytes
import Mathlib.Tactic

set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

/-!
# Functional correctness of the MODEXP word path

`secWordPath` is the `msize ≤ 32` compute path of the MODEXP program: a
`MULMOD`-based Horner reduction of the base, an exponent scan that skips
leading zero bytes, MSB-first square-and-multiply over the exponent bits
(value-dependent: the multiply is skipped on zero bits), and a fixed-width
big-endian serialization. This module proves that the path, entered with the
header's scalar cells set, halts by returning exactly `spec calldata`.

The entry predicate assumed here (supplied by the header/assembly proof) is
the hypothesis set of `wordPath_correct` below: control at
`secWordPath programLabels ++ rest`, empty stack, the six scalar cells
`BS/ES/MS/BO/EO/MO` holding the parsed sizes and offsets, the calldata equal
to the input, and the active window at or below the `TOP` cell (the path's
own `store TOP 0` then pins it at 250 words).
-/

namespace Challenge.Modexp.Submission.Proof.WordPath

open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState wordFrom byteFrom byteAt loadWord storeWord
  readBytes touchMemory)
open Challenge.Modexp.Submission (Expr store jumpIfNz jumpIfZ jumpUnlessLt cdbCell
  bitTest compileExpr BS ES MS BO EO MO Icell Jcell Wcell T0 T1 T2 RET TOP
  programAsm evalExpr exprOK)
open Challenge.Modexp.Submission.Proof.Header
open Challenge.Modexp.Submission.Proof.YulMem (wordVal wordVal_succ wordVal_lt
  byteAt_wordFrom_first wordFrom_eq wordFrom_toNat)
open Challenge.Modexp.Submission.Proofs.Algorithm (modPow_eq modPow_lt)
open Challenge.Modexp (baseSize exponentSize modulusSize spec ValidInput)
open EvmSemantics
open EvmSemantics.EVM.Precompile (bytesToNatPadded natToBytes modPow)
open Challenge.EvmProof.Bytes (bytesToNatPadded_zero_width bytesToNatPadded_succ
  bytesToNatPadded_add bytesToNatPadded_lt_pow)

/-! ## Generic label-resolution lemmas -/

/-- Resolve a word-path label: the continuation is the section tail plus the
big-path and halt sections. -/
private theorem resolve_label {lbl : Label} {pre tail : List Asm}
    (hh : lbl ∉ labelDefs (secHeader programLabels))
    (hp : lbl ∉ labelDefs pre)
    (hsplit : secWordPath programLabels = pre ++ [Asm.label lbl] ++ tail) :
    findLabel lbl programAsm =
      some (tail ++ (secBigPath programLabels ++ progTail)) := by
  rw [programAsm_eq, hsplit]
  simp only [List.append_assoc]
  rw [findLabel_pre hh, List.cons_append, List.nil_append]
  exact findLabel_here hp



/-! ## The word-path fragments -/

/-- The fixed continuation after the whole word-path section. -/
@[reducible] def wpK : List Asm := secBigPath programLabels ++ progTail

/-- Word path from `.label l.lweSer` to the end of the section. All fragment
definitions below are right-associated so that each leading statement faces
its continuation as `stmt ++ rest`. -/
def wpSer (_l : ProgLabels) : List Asm :=
  store RET (.bin .shl (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
    (.load T2)) ++
  (compileExpr (.load MS) ++ (compileExpr (.imm RET) ++ [.op .ret]))

/-- Word path from `.label l.lwZeroMod`. -/
def wpZeroMod (l : ProgLabels) : List Asm :=
  store T2 (.imm 0) ++ ([.label l.lweSer] ++ wpSer l)

/-- Word path from `.label l.lweNext`. -/
def wpNext (l : ProgLabels) : List Asm :=
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lweBytes] ++ ([.label l.lwZeroMod] ++ wpZeroMod l))

/-- Word path from `.label l.lweByteBits`. -/
def wpByteBits (l : ProgLabels) : List Asm :=
  jumpIfZ (.load Jcell) l.lweNext ++
  (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  (store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
  (jumpIfZ bitTest l.lweByteBits ++
  (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
  ([.jump l.lweByteBits] ++ ([.label l.lweNext] ++ wpNext l))))) )

/-- Word path from `.label l.lweBytes`. -/
def wpBytes (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load ES) l.lweSer ++
  (store Wcell (cdbCell EO) ++
  (store Jcell (.imm 8) ++ ([.label l.lweByteBits] ++ wpByteBits l)))

/-- Word path from `.label l.lweRest`. -/
def wpRest (l : ProgLabels) : List Asm :=
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.label l.lweBytes] ++ wpBytes l)

/-- Word path from `.label l.lweBits`. -/
def wpBits (l : ProgLabels) : List Asm :=
  jumpIfZ (.load Jcell) l.lweRest ++
  (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  (store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
  (jumpIfZ bitTest l.lweBits ++
  (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
  ([.jump l.lweBits] ++ ([.label l.lweRest] ++ wpRest l))))) )

/-- Word path from `.label l.lweBitsInit`. -/
def wpBitsInit (l : ProgLabels) : List Asm :=
  store T2 (.load T1) ++ ([.label l.lweBits] ++ wpBits l)

/-- Word path from `.label l.lweTop`. -/
def wpTopBit (l : ProgLabels) : List Asm :=
  jumpIfNz bitTest l.lweBitsInit ++
  (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  ([.jump l.lweTop] ++ ([.label l.lweBitsInit] ++ wpBitsInit l)))

/-- Word path from `.label l.lwInit`. -/
def wpLwInit (l : ProgLabels) : List Asm :=
  store Jcell (.imm 7) ++ ([.label l.lweTop] ++ wpTopBit l)

/-- Word path from `.label l.lweExpZero`. -/
def wpExpZero (l : ProgLabels) : List Asm :=
  store T2 (.bin .mod (.imm 1) (.load T0)) ++
  ([.jump l.lweSer] ++ ([.label l.lwInit] ++ wpLwInit l))

/-- Word path from `.label l.lweScan`. -/
def wpScan (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load ES) l.lweExpZero ++
  (store Wcell (cdbCell EO) ++
  (jumpIfNz (.load Wcell) l.lwInit ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lweScan] ++ ([.label l.lweExpZero] ++ wpExpZero l)))))

/-- Word path from `.label l.lwbDone`. -/
def wpLwbDone (l : ProgLabels) : List Asm :=
  store Icell (.imm 0) ++ ([.label l.lweScan] ++ wpScan l)

/-- Word path from `.label l.lwbLoop`. -/
def wpLwbLoop (l : ProgLabels) : List Asm :=
  jumpUnlessLt (.load Icell) (.load BS) l.lwbDone ++
  (store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
    (cdbCell BO) (.load T0)) ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lwbLoop] ++ ([.label l.lwbDone] ++ wpLwbDone l))))

/-- The word-path section up to (and excluding) `.label l.lwbLoop`. -/
def wpPrefix (l : ProgLabels) : List Asm :=
  store TOP (.imm 0) ++
  (store T0 (.bin .shr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
    (.cdload (.load MO))) ++
  (jumpIfZ (.load T0) l.lwZeroMod ++
  (store T1 (.imm 0) ++ store Icell (.imm 0))))

theorem secWordPath_eq : secWordPath programLabels = wpPrefix programLabels ++
  [.label programLabels.lwbLoop] ++ wpLwbLoop programLabels := by rfl

/-! ## Label resolutions against the concrete program -/

theorem findLwbLoop :
    findLabel programLabels.lwbLoop programAsm =
      some (wpLwbLoop programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label (pre := wpPrefix programLabels) (tail := wpLwbLoop programLabels)
    (by decide) (by decide) (by rfl)

theorem findLwbDone :
    findLabel programLabels.lwbDone programAsm =
      some (wpLwbDone programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop])
    (tail := wpLwbDone programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweScan :
    findLabel programLabels.lweScan programAsm =
      some (wpScan programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0))
    (tail := wpScan programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweExpZero :
    findLabel programLabels.lweExpZero programAsm =
      some (wpExpZero programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan])
    (tail := wpExpZero programLabels)
    (by decide) (by decide) (by rfl)

theorem findLwInit :
    findLabel programLabels.lwInit programAsm =
      some (wpLwInit programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer])
    (tail := wpLwInit programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweTop :
    findLabel programLabels.lweTop programAsm =
      some (wpTopBit programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7))
    (tail := wpTopBit programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweBitsInit :
    findLabel programLabels.lweBitsInit programAsm =
      some (wpBitsInit programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop])
    (tail := wpBitsInit programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweBits :
    findLabel programLabels.lweBits programAsm =
      some (wpBits programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop] ++
      [.label programLabels.lweBitsInit] ++ store T2 (.load T1))
    (tail := wpBits programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweRest :
    findLabel programLabels.lweRest programAsm =
      some (wpRest programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop] ++
      [.label programLabels.lweBitsInit] ++ store T2 (.load T1) ++
      [.label programLabels.lweBits] ++
      jumpIfZ (.load Jcell) programLabels.lweRest ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweBits])
    (tail := wpRest programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweBytes :
    findLabel programLabels.lweBytes programAsm =
      some (wpBytes programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop] ++
      [.label programLabels.lweBitsInit] ++ store T2 (.load T1) ++
      [.label programLabels.lweBits] ++
      jumpIfZ (.load Jcell) programLabels.lweRest ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweBits] ++
      [.label programLabels.lweRest] ++
      store Icell (.bin .add (.load Icell) (.imm 1)))
    (tail := wpBytes programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweByteBits :
    findLabel programLabels.lweByteBits programAsm =
      some (wpByteBits programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop] ++
      [.label programLabels.lweBitsInit] ++ store T2 (.load T1) ++
      [.label programLabels.lweBits] ++
      jumpIfZ (.load Jcell) programLabels.lweRest ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweBits] ++
      [.label programLabels.lweRest] ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++
      [.label programLabels.lweBytes] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweSer ++
      store Wcell (cdbCell EO) ++ store Jcell (.imm 8))
    (tail := wpByteBits programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweNext :
    findLabel programLabels.lweNext programAsm =
      some (wpNext programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop] ++
      [.label programLabels.lweBitsInit] ++ store T2 (.load T1) ++
      [.label programLabels.lweBits] ++
      jumpIfZ (.load Jcell) programLabels.lweRest ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweBits] ++
      [.label programLabels.lweRest] ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++
      [.label programLabels.lweBytes] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweSer ++
      store Wcell (cdbCell EO) ++ store Jcell (.imm 8) ++
      [.label programLabels.lweByteBits] ++
      jumpIfZ (.load Jcell) programLabels.lweNext ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweByteBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweByteBits])
    (tail := wpNext programLabels)
    (by decide) (by decide) (by rfl)

theorem findLwZeroMod :
    findLabel programLabels.lwZeroMod programAsm =
      some (wpZeroMod programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop] ++
      [.label programLabels.lweBitsInit] ++ store T2 (.load T1) ++
      [.label programLabels.lweBits] ++
      jumpIfZ (.load Jcell) programLabels.lweRest ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweBits] ++
      [.label programLabels.lweRest] ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++
      [.label programLabels.lweBytes] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweSer ++
      store Wcell (cdbCell EO) ++ store Jcell (.imm 8) ++
      [.label programLabels.lweByteBits] ++
      jumpIfZ (.load Jcell) programLabels.lweNext ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweByteBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweByteBits] ++
      [.label programLabels.lweNext] ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweBytes])
    (tail := wpZeroMod programLabels)
    (by decide) (by decide) (by rfl)

theorem findLweSer :
    findLabel programLabels.lweSer programAsm =
      some (wpSer programLabels ++ (secBigPath programLabels ++ progTail)) :=
  resolve_label
    (pre := wpPrefix programLabels ++ [.label programLabels.lwbLoop] ++
      jumpUnlessLt (.load Icell) (.load BS) programLabels.lwbDone ++
      store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
        (cdbCell BO) (.load T0)) ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lwbLoop] ++
      [.label programLabels.lwbDone] ++ store Icell (.imm 0) ++
      [.label programLabels.lweScan] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweExpZero ++
      store Wcell (cdbCell EO) ++
      jumpIfNz (.load Wcell) programLabels.lwInit ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweScan] ++
      [.label programLabels.lweExpZero] ++
      store T2 (.bin .mod (.imm 1) (.load T0)) ++ [.jump programLabels.lweSer] ++
      [.label programLabels.lwInit] ++ store Jcell (.imm 7) ++
      [.label programLabels.lweTop] ++
      jumpIfNz bitTest programLabels.lweBitsInit ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++ [.jump programLabels.lweTop] ++
      [.label programLabels.lweBitsInit] ++ store T2 (.load T1) ++
      [.label programLabels.lweBits] ++
      jumpIfZ (.load Jcell) programLabels.lweRest ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweBits] ++
      [.label programLabels.lweRest] ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++
      [.label programLabels.lweBytes] ++
      jumpUnlessLt (.load Icell) (.load ES) programLabels.lweSer ++
      store Wcell (cdbCell EO) ++ store Jcell (.imm 8) ++
      [.label programLabels.lweByteBits] ++
      jumpIfZ (.load Jcell) programLabels.lweNext ++
      store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
      store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
      jumpIfZ bitTest programLabels.lweByteBits ++
      store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
      [.jump programLabels.lweByteBits] ++
      [.label programLabels.lweNext] ++
      store Icell (.bin .add (.load Icell) (.imm 1)) ++ [.jump programLabels.lweBytes] ++
      [.label programLabels.lwZeroMod] ++ store T2 (.imm 0))
    (tail := wpSer programLabels)
    (by decide) (by decide) (by rfl)

/-- The fixed continuation after the word-path section, kept irreducible so
its large evaluation never happens inside a unification. -/
@[irreducible] def contK : List Asm :=
  secBigPath programLabels ++ progTail

theorem contK_def : secBigPath programLabels ++ progTail = contK := by
  unfold contK
  rfl

theorem findLwbLoopK :
    findLabel programLabels.lwbLoop programAsm = some (wpLwbLoop programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLwbLoop


theorem findLwbDoneK :
    findLabel programLabels.lwbDone programAsm = some (wpLwbDone programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLwbDone

theorem findLweScanK :
    findLabel programLabels.lweScan programAsm = some (wpScan programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweScan


theorem findLweExpZeroK :
    findLabel programLabels.lweExpZero programAsm =
      some (wpExpZero programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweExpZero

theorem findLwInitK :
    findLabel programLabels.lwInit programAsm = some (wpLwInit programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLwInit


theorem findLweBitsInitK :
    findLabel programLabels.lweBitsInit programAsm =
      some (wpBitsInit programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweBitsInit


theorem findLweRestK :
    findLabel programLabels.lweRest programAsm = some (wpRest programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweRest



theorem findLweNextK :
    findLabel programLabels.lweNext programAsm = some (wpNext programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweNext

theorem findLwZeroModK :
    findLabel programLabels.lwZeroMod programAsm =
      some (wpZeroMod programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLwZeroMod

theorem findLweSerK :
    findLabel programLabels.lweSer programAsm = some (wpSer programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweSer

/-! ## Word arithmetic helpers -/

/-- Shorthand for the 256-bit word carrying the natural `n`. -/
local notation:max "W " n:max => BitVec.ofNat 256 n

private theorem two_pow_256_eq : (2 : Nat) ^ 256 = 256 ^ 32 := by
  rw [show (2 : Nat) ^ 256 = (2 : Nat) ^ (8 * 32) from by norm_num, Nat.pow_mul]

theorem toNat_W {n : Nat} (h : n < 2 ^ 256) : (W n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem W_eq_zero {n : Nat} (h : n < 2 ^ 256) : W n = 0 ↔ n = 0 := by
  constructor
  · intro he
    have h2 : (W n).toNat = 0 := by rw [he]; rfl
    rwa [toNat_W h] at h2
  · intro he; subst he; rfl

theorem W_ne_zero {n : Nat} (hn : n ≠ 0) (h : n < 2 ^ 256) : W n ≠ 0 := by
  intro he
  exact hn ((W_eq_zero h).mp he)

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
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

theorem W_sub {a b : Nat} (hb : b ≤ a) (hpos : 0 < b) (ha : a < 2 ^ 256) :
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

theorem W_shr {v : Nat} (hv : v < 2 ^ 256) (k : Nat) :
    W v >>> k = W (v / 2 ^ k) := by
  have hlt : v / 2 ^ k < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]

theorem W_shl_toNat {v : Nat} (vlt : v < 2 ^ 256) (k : Nat) :
    (W v <<< k).toNat = (v * 2 ^ k) % 2 ^ 256 := by
  simp only [BitVec.toNat_shiftLeft, toNat_W vlt, Nat.shiftLeft_eq]

theorem W_and_one {v : Nat} (hv : v < 2 ^ 256) : W v &&& W 1 = W (v % 2) := by
  have h2 : v % 2 < 2 ^ 256 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt (by norm_num : (1 : Nat) < 2 ^ 256), toNat_W hv]
  simp

theorem W_mod {a m : Nat} (ha : a < 2 ^ 256) (hm0 : 0 < m) (hm : m < 2 ^ 256) :
    W a % W m = W (a % m) := by
  have hlt : a % m < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.mod_lt _ hm0)) hm
  apply BitVec.eq_of_toNat_eq
  have e : (W a % W m).toNat = (W a).toNat % (W m).toNat := by simp
  rw [e, toNat_W ha, toNat_W hm, toNat_W hlt]

theorem W_shl_toNat_mul {v k : Nat} (vlt : v < 2 ^ 256) (hmul : v * 2 ^ k < 2 ^ 256) :
    (W v <<< k).toNat = v * 2 ^ k := by
  rw [W_shl_toNat vlt k, Nat.mod_eq_of_lt hmul]

/-- A value below `256 ^ ms` for `ms ≤ 32` fits a word. -/
theorem lt_two_pow_256_of_lt_pow256 {r ms : Nat} (hms : ms ≤ 32) (hr : r < 256 ^ ms) :
    r < 2 ^ 256 := by
  rw [two_pow_256_eq]
  exact Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hms)

/-! ## Calldata bridge -/

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

theorem evalBin_byte_zero (x : U256) :
    evalBin .byte (0 : U256) x = (x >>> 248) &&& 255 := by
  have h0 : ((0 : U256)).toNat = 0 := by simp
  simp only [evalBin, h0]
  norm_num

/-- `byte(0, calldataload p)` is the calldata byte at `p`, as a word. -/
theorem evalExpr_cdb {e : Expr} {yst : EvmState} {p : Nat}
    (haddr : (evalExpr e yst).toNat = p) :
    evalExpr (Expr.cdb e) yst = W (byteFrom yst.env.calldata p).toNat := by
  have h1 : evalExpr (Expr.cdb e) yst
      = evalBin .byte (0 : U256) (wordFrom yst.env.calldata p) := by
    simp only [evalExpr, haddr]
  rw [h1, evalBin_byte_zero]
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
  have hand : (byteFrom yst.env.calldata p).toNat &&& 255
      = (byteFrom yst.env.calldata p).toNat := by
    have hmod := Nat.and_two_pow_sub_one_eq_mod (byteFrom yst.env.calldata p).toNat 8
    norm_num at hmod
    omega
  apply BitVec.eq_of_toNat_eq
  have e2 : ((wordFrom yst.env.calldata p >>> 248) &&& (255 : U256)).toNat
      = (wordFrom yst.env.calldata p >>> 248).toNat &&& 255 := by
    simp only [BitVec.toNat_and]
    rfl
  rw [e2, hshift, hand, toNat_W hlt]

/-! ## The word-path machine frame -/

/-- The word path's state frame once `store TOP 0` has pinned the active
window at 250 words: the calldata view and the six header scalar cells with
their parsed values (`bs es ms` the sizes, `bo eo mo` the offsets). Every
word-path statement preserves this frame. -/
def WPState (yst : EvmState) (calldata : ByteArray)
    (bs es ms bo eo mo : Nat) : Prop :=
  yst.activeWords.toNat = 250 ∧ yst.env.calldata = calldata.toList ∧
    loadWord yst.memory BS = W bs ∧ loadWord yst.memory ES = W es ∧
    loadWord yst.memory MS = W ms ∧ loadWord yst.memory BO = W bo ∧
    loadWord yst.memory EO = W eo ∧ loadWord yst.memory MO = W mo

theorem WPState.cd {yst calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo) :
    yst.env.calldata = calldata.toList := h.2.1

theorem WPState.BSw {yst calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo) :
    loadWord yst.memory BS = W bs := h.2.2.1

theorem WPState.ESw {yst calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo) :
    loadWord yst.memory ES = W es := h.2.2.2.1

theorem WPState.MSw {yst calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo) :
    loadWord yst.memory MS = W ms := h.2.2.2.2.1

theorem WPState.BOw {yst calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo) :
    loadWord yst.memory BO = W bo := h.2.2.2.2.2.1

theorem WPState.EOw {yst calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo) :
    loadWord yst.memory EO = W eo := h.2.2.2.2.2.2.1

theorem WPState.MOw {yst calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo) :
    loadWord yst.memory MO = W mo := h.2.2.2.2.2.2.2

theorem WPState.set_mem {yst yst' calldata bs es ms bo eo mo}
    (h : WPState yst calldata bs es ms bo eo mo)
    (haw : yst'.activeWords.toNat = 250) (hcd : yst'.env.calldata = calldata.toList)
    (hmem : ∀ q ∈ [BS, ES, MS, BO, EO, MO],
      loadWord yst'.memory q = loadWord yst.memory q) :
    WPState yst' calldata bs es ms bo eo mo := by
  refine ⟨haw, hcd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem BS (by decide)]; exact h.BSw
  · rw [hmem ES (by decide)]; exact h.ESw
  · rw [hmem MS (by decide)]; exact h.MSw
  · rw [hmem BO (by decide)]; exact h.BOw
  · rw [hmem EO (by decide)]; exact h.EOw
  · rw [hmem MO (by decide)]; exact h.MOw

/-- A word store to one cell leaves another, disjoint cell alone. -/
theorem loadCell_storeCell {mem : Nat → UInt8} {c q : Nat} {v : U256}
    (h : c + 32 ≤ q ∨ q + 32 ≤ c) :
    loadWord (storeWord mem c v) q = loadWord mem q :=
  loadWord_storeWord_disj h

/-- The entry and scratch cells used by the word path, pinned by 250 words. -/
theorem pinLoad {c : Nat} (h : c + 32 ≤ 8000) {yst : EvmState} {calldata : ByteArray}
    {bs es ms bo eo mo : Nat} (hf : WPState yst calldata bs es ms bo eo mo) :
    exprOK (Expr.load c) yst := by
  show c < 2 ^ 256 ∧ c + 32 ≤ 32 * yst.activeWords.toNat
  rw [hf.1]
  omega

theorem pinCdbCell {base : Nat} (hb : base + 32 ≤ 8000)
    {yst : EvmState} {calldata : ByteArray} {bs es ms bo eo mo : Nat}
    (hf : WPState yst calldata bs es ms bo eo mo) :
    exprOK (cdbCell base) yst := by
  show binOK .add = true ∧ exprOK (Expr.load base) yst ∧
    exprOK (Expr.load Icell) yst
  exact ⟨rfl, pinLoad hb hf, pinLoad (by decide) hf⟩

theorem pinBitTest {yst : EvmState} {calldata : ByteArray} {bs es ms bo eo mo : Nat}
    (hf : WPState yst calldata bs es ms bo eo mo) : exprOK bitTest yst := by
  show binOK .and = true ∧
    (binOK .shr = true ∧ exprOK (Expr.load Jcell) yst ∧
      exprOK (Expr.load Wcell) yst) ∧ exprOK (Expr.imm 1) yst
  exact ⟨rfl, ⟨rfl, pinLoad (by decide) hf, pinLoad (by decide) hf⟩, trivial⟩

/-- `store c e` writing the word value `W v`, in the pinned frame. -/
theorem storeW {c v : Nat} {e : Expr} {yst : EvmState} {k : List Asm}
    (he : exprOK e yst) (hcpin : c + 32 ≤ 8000) (haw : yst.activeWords.toNat = 250)
    (hval : evalExpr e yst = W v) :
    ASteps programAsm ⟨store c e ++ k, [], yst⟩
          ⟨k, [], { yst with memory := storeWord yst.memory c (W v) }⟩ := by
  have hc : c < 2 ^ 256 ∧ c + 32 ≤ 32 * yst.activeWords.toNat := by
    rw [haw]
    omega
  have h := store_steps (model := localModel) (prog := programAsm)
    (k := k) (σ := []) he hc
  rwa [hval] at h

theorem jumpTo {l : Label} {c' : List Asm}
    (hfind : findLabel l programAsm = some c') {k : List Asm} {yst : EvmState} :
    ASteps programAsm ⟨[.jump l] ++ k, [], yst⟩ ⟨c', [], yst⟩ :=
  jump_steps (model := localModel) hfind

theorem labelStep (l : Label) {k : List Asm} {yst : EvmState} :
    ASteps programAsm ⟨[.label l] ++ k, [], yst⟩ ⟨k, [], yst⟩ :=
  label_steps (model := localModel)

/-! ## Operand values -/

/-- The modulus word: `shr((32 - ms) * 8, calldataload mo)` is the padded
`ms`-byte read at `mo`. -/
theorem evalExpr_T0 {calldata : ByteArray} {bs es ms bo eo mo : Nat}
    {yst : EvmState}
    (hf : WPState yst calldata bs es ms bo eo mo)
    (hms0 : 0 < ms) (hms32 : ms ≤ 32)
    (hbo : bo = 96) (hbs : bs ≤ 1024) (hes : es ≤ 1024)
    (heo : eo = bo + bs) (hmo : mo = eo + es) :
    evalExpr (Expr.bin .shr
      (Expr.bin .mul (Expr.bin .sub (Expr.imm 32) (Expr.load MS))
        (Expr.imm 8))
      (Expr.cdload (Expr.load MO))) yst
      = W (bytesToNatPadded calldata mo ms) := by
  have heo256 : eo < 2 ^ 256 := by omega
  have hmo256 : mo < 2 ^ 256 := by omega
  have hsub : evalExpr (Expr.bin .sub (Expr.imm 32) (Expr.load MS)) yst
      = W (32 - ms) := by
    show W 32 - loadWord yst.memory MS = _
    rw [hf.MSw, W_sub hms32 hms0 (by omega)]
  have hmul : evalExpr (Expr.bin .mul
      (Expr.bin .sub (Expr.imm 32) (Expr.load MS)) (Expr.imm 8)) yst
      = W ((32 - ms) * 8) := by
    show evalExpr (Expr.bin .sub (Expr.imm 32) (Expr.load MS)) yst * W 8 = _
    rw [hsub, W_mul]
  have hcd : evalExpr (Expr.cdload (Expr.load MO)) yst
      = W (bytesToNatPadded calldata mo 32) := by
    show wordFrom yst.env.calldata (loadWord yst.memory MO).toNat = _
    rw [hf.MOw, toNat_W hmo256, hf.cd, wordFrom_eq_W]
  have hV256 : bytesToNatPadded calldata mo 32 < 2 ^ 256 := by
    have hv := bytesToNatPadded_lt_pow calldata mo 32
    rwa [show (256 : Nat) ^ 32 = 2 ^ 256 from two_pow_256_eq.symm] at hv
  show evalExpr (Expr.cdload (Expr.load MO)) yst >>>
    (evalExpr (Expr.bin .mul (Expr.bin .sub (Expr.imm 32) (Expr.load MS))
      (Expr.imm 8)) yst).toNat = _
  rw [hcd, hmul, toNat_W (by omega : (32 - ms) * 8 < 2 ^ 256), W_shr hV256]
  have hdiv : bytesToNatPadded calldata mo 32 / 2 ^ ((32 - ms) * 8)
      = bytesToNatPadded calldata mo ms := by
    have hsplit := bytesToNatPadded_add calldata mo ms (32 - ms)
    rw [show ms + (32 - ms) = 32 from by omega] at hsplit
    have htp : 2 ^ ((32 - ms) * 8) = 256 ^ (32 - ms) := by
      rw [Nat.mul_comm, Nat.pow_mul]
    have htail := bytesToNatPadded_lt_pow calldata (mo + ms) (32 - ms)
    have hK : (0 : Nat) < 256 ^ (32 - ms) := by norm_num
    rw [htp, hsplit,
      Nat.mul_comm (bytesToNatPadded calldata mo ms) (256 ^ (32 - ms)),
      Nat.add_comm (256 ^ (32 - ms) * bytesToNatPadded calldata mo ms)
        (bytesToNatPadded calldata (mo + ms) (32 - ms)),
      Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt htail, Nat.zero_add]
  rw [hdiv]

/-- The Horner step's value: from `T1 = W a` and the base byte at `bo + i`,
the stored T1 word is `W ((a * 256 + byte) % m)`. -/
theorem evalExpr_horner {calldata : ByteArray} {bs es ms bo eo mo a i m : Nat}
    {yst : EvmState}
    (hf : WPState yst calldata bs es ms bo eo mo)
    (hT1 : loadWord yst.memory T1 = W a)
    (hT0 : loadWord yst.memory T0 = W m)
    (hI : loadWord yst.memory Icell = W i)
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256) (ha : a < 2 ^ 256)
    (hbi : i ≤ bs) (hbs : bs ≤ 1024) (hbo : bo = 96) :
    evalExpr (Expr.ter .addmod
      (Expr.ter .mulmod (Expr.load T1) (Expr.imm 256) (Expr.load T0))
      (cdbCell BO) (Expr.load T0)) yst
      = W ((a * 256 + (byteFrom calldata.toList (bo + i)).toNat) % m) := by
  have hbyte : evalExpr (cdbCell BO) yst
      = W (byteFrom calldata.toList (bo + i)).toNat := by
    have haddr : (evalExpr (Expr.bin .add (Expr.load BO) (Expr.load Icell)) yst).toNat
        = bo + i := by
      show (loadWord yst.memory BO + loadWord yst.memory Icell).toNat = bo + i
      rw [hf.BOw, hI, W_add (by omega), toNat_W (by omega)]
    show evalExpr (Expr.cdb (Expr.bin .add (Expr.load BO) (Expr.load Icell))) yst = _
    rw [evalExpr_cdb haddr, hf.cd]
  have hmne : W m ≠ 0 := W_ne_zero (by omega) hm256
  have hbt : (byteFrom calldata.toList (bo + i)).toNat < 2 ^ 256 :=
    (byteFrom calldata.toList (bo + i)).toNat_lt.trans (by norm_num)
  have hmulmod : evalExpr (Expr.ter .mulmod (Expr.load T1) (Expr.imm 256)
      (Expr.load T0)) yst = W ((a * 256) % m) := by
    show (if loadWord yst.memory T0 = 0 then 0 else
      W ((loadWord yst.memory T1).toNat * (W 256).toNat
        % (loadWord yst.memory T0).toNat)) = _
    rw [hT1, hT0, if_neg hmne, toNat_W ha,
      toNat_W (by omega : (256 : Nat) < 2 ^ 256), toNat_W hm256]
  have h1 : (W ((a * 256) % m)).toNat = (a * 256) % m :=
    toNat_W (Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.mod_lt _ hm0)) hm256)
  have h2 : (W (byteFrom calldata.toList (bo + i)).toNat).toNat
      = (byteFrom calldata.toList (bo + i)).toNat := toNat_W hbt
  have hcong : ((a * 256) % m + (byteFrom calldata.toList (bo + i)).toNat) % m
      = (a * 256 + (byteFrom calldata.toList (bo + i)).toNat) % m :=
    Nat.mod_add_mod (a * 256) m (byteFrom calldata.toList (bo + i)).toNat
  show (if loadWord yst.memory T0 = 0 then 0 else
    W (((evalExpr (Expr.ter .mulmod (Expr.load T1) (Expr.imm 256)
      (Expr.load T0)) yst).toNat + (evalExpr (cdbCell BO) yst).toNat)
      % (loadWord yst.memory T0).toNat)) = _
  rw [hT0, if_neg hmne, hmulmod, hbyte, h1, h2, toNat_W hm256, hcong]

/-- `wpLwbLoop l ++ k` with the loop test peeled off (the form the round
lemmas consume). -/
def wpLwbLoopOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  jumpUnlessLt (.load Icell) (.load BS) l.lwbDone ++
  (store T1 (.ter .addmod (.ter .mulmod (.load T1) (.imm 256) (.load T0))
    (cdbCell BO) (.load T0)) ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lwbLoop] ++ ([.label l.lwbDone] ++ (wpLwbDone l ++ k)))))

theorem wpLwbLoop_open (l : ProgLabels) (k : List Asm) :
    wpLwbLoop l ++ k = wpLwbLoopOpen l k := by
  simp only [wpLwbLoop, List.append_assoc, wpLwbLoopOpen]

theorem findLwbLoopOpenK :
    findLabel programLabels.lwbLoop programAsm =
      some (wpLwbLoopOpen programLabels contK) := by
  unfold contK; rw [← wpLwbLoop_open]; exact findLwbLoop


/-- Reading an entry cell is unaffected by stores to two other cells. -/
theorem load_entry_store2 {mem : Nat → UInt8} {c1 c2 : Nat} {v1 v2 : U256}
    {q : Nat} (h2 : c2 + 32 ≤ q ∨ q + 32 ≤ c2)
    (h1 : c1 + 32 ≤ q ∨ q + 32 ≤ c1) :
    loadWord (storeWord (storeWord mem c1 v1) c2 v2) q = loadWord mem q := by
  rw [loadCell_storeCell h2, loadCell_storeCell h1]

/-- The frame cells (and `T0`) that loops must keep stable. -/
def frameCells : List Nat := [BS, ES, MS, BO, EO, MO, T0]

/-- One word store to a cell disjoint from the frame cells keeps the frame
and `T0`. -/
theorem WPState_store1 {calldata : ByteArray} {bs es ms bo eo mo m : Nat}
    {y : EvmState}
    {c : Nat} {v : U256}
    (h : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m)
    (hd : ∀ q ∈ frameCells, c + 32 ≤ q ∨ q + 32 ≤ c) :
    WPState {y with memory := storeWord y.memory c v} calldata bs es ms bo eo mo ∧
      loadWord (storeWord y.memory c v) T0 = W m := by
  refine ⟨⟨h.1, h.cd, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [loadCell_storeCell (hd BS (by decide))]; exact h.BSw
  · rw [loadCell_storeCell (hd ES (by decide))]; exact h.ESw
  · rw [loadCell_storeCell (hd MS (by decide))]; exact h.MSw
  · rw [loadCell_storeCell (hd BO (by decide))]; exact h.BOw
  · rw [loadCell_storeCell (hd EO (by decide))]; exact h.EOw
  · rw [loadCell_storeCell (hd MO (by decide))]; exact h.MOw
  · rw [loadCell_storeCell (hd T0 (by decide))]; exact hT0

/-- Two word stores to cells disjoint from the frame cells. -/
theorem WPState_store2 {calldata : ByteArray} {bs es ms bo eo mo m : Nat}
    {y : EvmState}
    {c1 c2 : Nat} {v1 v2 : U256}
    (h : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m)
    (hd : ∀ q ∈ frameCells, (c2 + 32 ≤ q ∨ q + 32 ≤ c2) ∧
      (c1 + 32 ≤ q ∨ q + 32 ≤ c1)) :
    WPState {y with memory := storeWord (storeWord y.memory c1 v1) c2 v2}
      calldata bs es ms bo eo mo ∧
      loadWord (storeWord (storeWord y.memory c1 v1) c2 v2) T0 = W m := by
  refine ⟨⟨h.1, h.cd, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [load_entry_store2 ((hd BS (by decide)).1) ((hd BS (by decide)).2)]
    exact h.BSw
  · rw [load_entry_store2 ((hd ES (by decide)).1) ((hd ES (by decide)).2)]
    exact h.ESw
  · rw [load_entry_store2 ((hd MS (by decide)).1) ((hd MS (by decide)).2)]
    exact h.MSw
  · rw [load_entry_store2 ((hd BO (by decide)).1) ((hd BO (by decide)).2)]
    exact h.BOw
  · rw [load_entry_store2 ((hd EO (by decide)).1) ((hd EO (by decide)).2)]
    exact h.EOw
  · rw [load_entry_store2 ((hd MO (by decide)).1) ((hd MO (by decide)).2)]
    exact h.MOw
  · rw [load_entry_store2 ((hd T0 (by decide)).1) ((hd T0 (by decide)).2)]
    exact hT0

set_option maxHeartbeats 10000000 in
/-- The base-reduction loop: from `.label lwbLoop` with `Icell = W 0` and
`T1 = W 0`, iterate the Horner step `bs` times to `.label lwbDone` with
`T1 = W (b % m)` and `Icell = W bs`. -/
theorem baseLoop_correct {calldata : ByteArray} {bs es ms bo eo mo m : Nat}
    {yst : EvmState}
    (hbs : bs ≤ 1024) (_hes : es ≤ 1024) (_hms0 : 0 < ms) (_hms32 : ms ≤ 32)
    (hbo : bo = 96) (heo : eo = bo + bs) (_hmo : mo = eo + es)
    (hf : WPState yst calldata bs es ms bo eo mo)
    (hT0 : loadWord yst.memory T0 = W m)
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256)
    (hT1 : loadWord yst.memory T1 = W (0 : Nat))
    (hI : loadWord yst.memory Icell = W (0 : Nat)) :
    ∃ yst' : EvmState,
      WPState yst' calldata bs es ms bo eo mo ∧
      loadWord yst'.memory T0 = W m ∧
      loadWord yst'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
      loadWord yst'.memory Icell = W bs ∧
      ASteps programAsm ⟨wpLwbLoop programLabels ++ contK, [], yst⟩
        ⟨wpLwbDone programLabels ++ contK, [], yst'⟩ := by
  have hbo256 : bo < 2 ^ 256 := by omega
  have hbs256 : bs < 2 ^ 256 := by omega
  have hround : ∀ {n : Nat} {y : EvmState}, 0 < n →
      (WPState y calldata bs es ms bo eo mo ∧
        loadWord y.memory T0 = W m ∧
        loadWord y.memory T1 = W (bytesToNatPadded calldata bo (bs - n) % m) ∧
        loadWord y.memory Icell = W (bs - n) ∧ n ≤ bs) →
      (∃ y', (WPState y' calldata bs es ms bo eo mo ∧
        loadWord y'.memory T0 = W m ∧
        loadWord y'.memory T1 = W (bytesToNatPadded calldata bo (bs - (n - 1)) % m) ∧
        loadWord y'.memory Icell = W (bs - (n - 1)) ∧ n - 1 ≤ bs) ∧
        ASteps programAsm ⟨wpLwbLoop programLabels ++ contK, [], y⟩
          ⟨wpLwbLoop programLabels ++ contK, [], y'⟩) ∨
      ((WPState y calldata bs es ms bo eo mo ∧
        loadWord y.memory T0 = W m ∧
        loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y.memory Icell = W bs) ∧
        ASteps programAsm ⟨wpLwbLoop programLabels ++ contK, [], y⟩
          ⟨wpLwbDone programLabels ++ contK, [], y⟩) := by
    intro n y hn ⟨hf', hT0', hT1', hI', hnle⟩
    have hi : bs - n < bs := by omega
    have hi256 : bs - n < 2 ^ 256 := by omega
    have hmidi256 : bytesToNatPadded calldata bo (bs - n) % m < 2 ^ 256 :=
      Nat.lt_trans (Nat.mod_lt _ hm0) hm256
    have hlt : (evalExpr (Expr.load Icell) y).ult (evalExpr (Expr.load BS) y) := by
      show (loadWord y.memory Icell).ult (loadWord y.memory BS) = true
      rw [hI', hf'.BSw]
      exact W_ult hi256 hbs256 hi
    set key : Nat := (bytesToNatPadded calldata bo (bs - n) % m * 256 +
          (byteFrom calldata.toList (bo + (bs - n))).toNat) % m with hkeydef
    have hval : evalExpr (.ter .addmod (.ter .mulmod (.load T1) (.imm 256)
        (.load T0)) (cdbCell BO) (.load T0)) y = W key := by
      rw [evalExpr_horner hf' hT1' hT0' hI' hm0 hm256 hmidi256 (by omega) hbs hbo,
        ← hkeydef]
    have hexpr : exprOK (.ter .addmod (.ter .mulmod (.load T1) (.imm 256)
        (.load T0)) (cdbCell BO) (.load T0)) y := by
      show terOK .addmod = true ∧
        (terOK .mulmod = true ∧ exprOK (Expr.load T1) y ∧
          exprOK (Expr.imm 256) y ∧ exprOK (Expr.load T0) y) ∧
        exprOK (cdbCell BO) y ∧ exprOK (Expr.load T0) y
      exact ⟨rfl, ⟨rfl, pinLoad (by decide) hf', trivial,
        pinLoad (by decide) hf'⟩, pinCdbCell (by decide) hf',
        pinLoad (by decide) hf'⟩
    have hIval : evalExpr (.bin .add (.load Icell) (.imm 1)) y
        = W (bs - n + 1) := by
      show loadWord y.memory Icell + W 1 = _
      rw [hI', W_add (by omega)]
    have hIexpr : exprOK (.bin .add (.load Icell) (.imm 1)) y := by
      show binOK .add = true ∧ exprOK (Expr.load Icell) y ∧ exprOK (Expr.imm 1) y
      exact ⟨rfl, pinLoad (by decide) hf', trivial⟩
    have hbytesucc : bytesToNatPadded calldata bo (bs - n + 1)
        = bytesToNatPadded calldata bo (bs - n) * 256 +
          (byteFrom calldata.toList (bo + (bs - n))).toNat :=
      bytesToNatPadded_succ calldata bo (bs - n)
    have hmod : key = bytesToNatPadded calldata bo (bs - n + 1) % m := by
      rw [hkeydef, hbytesucc]
      exact (((Nat.mod_modEq (bytesToNatPadded calldata bo (bs - n)) m).mul_right 256).add
        (Nat.ModEq.refl (byteFrom calldata.toList (bo + (bs - n))).toNat))
    have hframe1 := WPState_store1 (c := T1) (v := W key) hf' hT0' (by decide)
    have hframe := WPState_store2 (c1 := T1) (c2 := Icell) (v1 := W key)
      (v2 := W (bs - n + 1)) hf' hT0' (by decide)
    have hsteps : ASteps programAsm ⟨wpLwbLoop programLabels ++ contK, [], y⟩
        ⟨wpLwbLoop programLabels ++ contK, [],
          { y with memory := storeWord (storeWord y.memory T1 (W key)) Icell (W (bs - n + 1)) }⟩ := by
      rw [wpLwbLoop_open]
      exact ((jumpUnlessLt_fall (model := localModel) (prog := programAsm)
        (pinLoad (by decide) hf') (pinLoad (by decide) hf') hlt).trans
        (storeW (c := T1) (yst := y) hexpr (by decide) hf'.1 hval)).trans
        ((storeW (c := Icell) (yst := { y with memory := storeWord y.memory T1 (W key) })
          hIexpr (by decide) hframe1.1.1 hIval).trans
        (jumpTo findLwbLoopOpenK))
    left
    refine ⟨{ y with memory := storeWord (storeWord y.memory T1 (W key)) Icell (W (bs - n + 1)) },
      ⟨hframe.1, hframe.2, ?_, ?_, by omega⟩, hsteps⟩
    · show loadWord (storeWord (storeWord y.memory T1 (W key)) Icell (W (bs - n + 1))) T1
        = W (bytesToNatPadded calldata bo (bs - (n - 1)) % m)
      rw [loadCell_storeCell (c := Icell) (q := T1) (by decide), loadWord_storeWord,
        hmod, show bs - (n - 1) = bs - n + 1 from by omega]
    · show loadWord (storeWord (storeWord y.memory T1 (W key)) Icell (W (bs - n + 1))) Icell
        = W (bs - (n - 1))
      rw [loadWord_storeWord, show bs - (n - 1) = bs - n + 1 from by omega]
  have hexit : ∀ y : EvmState,
      (WPState y calldata bs es ms bo eo mo ∧
        loadWord y.memory T0 = W m ∧
        loadWord y.memory T1 = W (bytesToNatPadded calldata bo (bs - 0) % m) ∧
        loadWord y.memory Icell = W (bs - 0) ∧ 0 ≤ bs) →
      (WPState y calldata bs es ms bo eo mo ∧
        loadWord y.memory T0 = W m ∧
        loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y.memory Icell = W bs) ∧
        ASteps programAsm ⟨wpLwbLoop programLabels ++ contK, [], y⟩
          ⟨wpLwbDone programLabels ++ contK, [], y⟩ := by
    intro y ⟨hf', hT0', hT1', hI', _⟩
    refine ⟨⟨hf', hT0', hT1', hI'⟩, ?_⟩
    have hnlt : ¬(evalExpr (Expr.load Icell) y).ult (evalExpr (Expr.load BS) y) := by
      show ¬ ((loadWord y.memory Icell).ult (loadWord y.memory BS) = true)
      rw [hI', hf'.BSw]
      exact W_nult hbs256 hbs256 (Nat.le_refl bs)
    rw [wpLwbLoop_open]
    exact jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (pinLoad (by decide) hf') (pinLoad (by decide) hf') hnlt findLwbDoneK
  obtain ⟨yst', ⟨hf', hT0', hT1', hI'⟩, hsteps⟩ :=
    loop_counted (model := localModel) (prog := programAsm)
      (top := wpLwbLoop programLabels ++ contK) (σ := [])
      (c' := wpLwbDone programLabels ++ contK)
      (Inv := fun y n => WPState y calldata bs es ms bo eo mo ∧
        loadWord y.memory T0 = W m ∧
        loadWord y.memory T1 = W (bytesToNatPadded calldata bo (bs - n) % m) ∧
        loadWord y.memory Icell = W (bs - n) ∧ n ≤ bs)
      (P := fun y => WPState y calldata bs es ms bo eo mo ∧
        loadWord y.memory T0 = W m ∧
        loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y.memory Icell = W bs)
      hround hexit
      ⟨hf, hT0, by rw [show bs - bs = 0 from by omega, bytesToNatPadded_zero_width,
        Nat.zero_mod]; exact hT1,
        by rw [show bs - bs = 0 from by omega]; exact hI, Nat.le_refl bs⟩
  exact ⟨yst', hf', hT0', hT1', hI', hsteps⟩

theorem sq_mod (b E m x : Nat) (hx : x = b ^ E % m) :
    (x * x) % m = b ^ (2 * E) % m := by
  rw [hx, ← Nat.mul_mod, show 2 * E = E + E from by omega, Nat.pow_add]

theorem mulbase_mod (b E m x t : Nat) (hx : x = b ^ E % m) (ht : t = b % m) :
    (x * t) % m = b ^ (E + 1) % m := by
  rw [hx, ht, ← Nat.mul_mod, Nat.pow_succ]

/-- Doubling the exponent prefix: `2 · (X · 2^k + (wb >> k)) + bit(k-1)
= X · 2^(k+1) + (wb >> (k-1))`. -/
theorem bit_step (X wb n : Nat) (hn : 0 < n) (hn8 : n ≤ 8) :
    2 * (X * 2 ^ (8 - n) + wb / 2 ^ n) + wb / 2 ^ (n - 1) % 2
      = X * 2 ^ (8 - (n - 1)) + wb / 2 ^ (n - 1) := by
  have hpow : 2 ^ (8 - (n - 1)) = 2 ^ (8 - n) * 2 := by
    have h8 : 8 - (n - 1) = (8 - n) + 1 := by omega
    conv_lhs => rw [h8]
    rw [Nat.pow_succ]
  have hn1 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs =>
      rw [show n = (n - 1) + 1 from by omega]
      rw [Nat.pow_succ]
  have hdd : wb / 2 ^ n = (wb / 2 ^ (n - 1)) / 2 := by
    rw [hn1, Nat.div_div_eq_div_mul]
  have hdm := Nat.div_add_mod (wb / 2 ^ (n - 1)) 2
  rw [show X * 2 ^ (8 - (n - 1)) = 2 * (X * 2 ^ (8 - n)) from by rw [hpow]; ring]
  omega

/-! ## Remaining loop-head fragments (peeled forms) -/

def wpScanOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  jumpUnlessLt (.load Icell) (.load ES) l.lweExpZero ++
  (store Wcell (cdbCell EO) ++
  (jumpIfNz (.load Wcell) l.lwInit ++
  (store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lweScan] ++ ([.label l.lweExpZero] ++ (wpExpZero l ++ k))))))

theorem wpScan_open (l : ProgLabels) (k : List Asm) :
    wpScan l ++ k = wpScanOpen l k := by
  simp only [wpScan, List.append_assoc, wpScanOpen]

def wpTopBitOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  jumpIfNz bitTest l.lweBitsInit ++
  (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  ([.jump l.lweTop] ++ ([.label l.lweBitsInit] ++ (wpBitsInit l ++ k))))

theorem wpTopBit_open (l : ProgLabels) (k : List Asm) :
    wpTopBit l ++ k = wpTopBitOpen l k := by
  simp only [wpTopBit, List.append_assoc, wpTopBitOpen]

def wpBitsOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  jumpIfZ (.load Jcell) l.lweRest ++
  (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  (store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
  (jumpIfZ bitTest l.lweBits ++
  (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
  ([.jump l.lweBits] ++ ([.label l.lweRest] ++ (wpRest l ++ k)))))))

theorem wpBits_open (l : ProgLabels) (k : List Asm) :
    wpBits l ++ k = wpBitsOpen l k := by
  simp only [wpBits, List.append_assoc, wpBitsOpen]

def wpBytesOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  jumpUnlessLt (.load Icell) (.load ES) l.lweSer ++
  (store Wcell (cdbCell EO) ++
  (store Jcell (.imm 8) ++ ([.label l.lweByteBits] ++ (wpByteBits l ++ k))))

theorem wpBytes_open (l : ProgLabels) (k : List Asm) :
    wpBytes l ++ k = wpBytesOpen l k := by
  simp only [wpBytes, List.append_assoc, wpBytesOpen]

def wpByteBitsOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  jumpIfZ (.load Jcell) l.lweNext ++
  (store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
  (store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
  (jumpIfZ bitTest l.lweByteBits ++
  (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
  ([.jump l.lweByteBits] ++ ([.label l.lweNext] ++ (wpNext l ++ k)))))))

theorem wpByteBits_open (l : ProgLabels) (k : List Asm) :
    wpByteBits l ++ k = wpByteBitsOpen l k := by
  simp only [wpByteBits, List.append_assoc, wpByteBitsOpen]

/-! ## Opens for the jump-entered fragments -/

def wpLwbDoneOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store Icell (.imm 0) ++ ([.label l.lweScan] ++ (wpScan l ++ k))

theorem wpLwbDone_open (l : ProgLabels) (k : List Asm) :
    wpLwbDone l ++ k = wpLwbDoneOpen l k := by
  simp only [wpLwbDone, List.append_assoc, wpLwbDoneOpen]

def wpPrefixOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store TOP (.imm 0) ++
  (store T0 (.bin .shr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
    (.cdload (.load MO))) ++
  (jumpIfZ (.load T0) l.lwZeroMod ++
  (store T1 (.imm 0) ++ (store Icell (.imm 0) ++
  ([.label l.lwbLoop] ++ (wpLwbLoop l ++ k))))))

theorem secWordPath_open (k : List Asm) :
    secWordPath programLabels ++ k = wpPrefixOpen programLabels k := by
  simp only [secWordPath_eq, wpPrefix, List.append_assoc, wpPrefixOpen]

def wpZeroModOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store T2 (.imm 0) ++ ([.label l.lweSer] ++ (wpSer l ++ k))

theorem wpZeroMod_open (l : ProgLabels) (k : List Asm) :
    wpZeroMod l ++ k = wpZeroModOpen l k := by
  simp only [wpZeroMod, List.append_assoc, wpZeroModOpen]

def wpExpZeroOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store T2 (.bin .mod (.imm 1) (.load T0)) ++
  ([.jump l.lweSer] ++ ([.label l.lwInit] ++ (wpLwInit l ++ k)))

theorem wpExpZero_open (l : ProgLabels) (k : List Asm) :
    wpExpZero l ++ k = wpExpZeroOpen l k := by
  rw [wpExpZero, wpExpZeroOpen]
  simp only [List.append_assoc]

def wpLwInitOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store Jcell (.imm 7) ++ ([.label l.lweTop] ++ (wpTopBit l ++ k))

theorem wpLwInit_open (l : ProgLabels) (k : List Asm) :
    wpLwInit l ++ k = wpLwInitOpen l k := by
  simp only [wpLwInit, List.append_assoc, wpLwInitOpen]

def wpBitsInitOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store T2 (.load T1) ++ ([.label l.lweBits] ++ (wpBits l ++ k))

theorem wpBitsInit_open (l : ProgLabels) (k : List Asm) :
    wpBitsInit l ++ k = wpBitsInitOpen l k := by
  simp only [wpBitsInit, List.append_assoc, wpBitsInitOpen]

def wpRestOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.label l.lweBytes] ++ (wpBytes l ++ k))

theorem wpRest_open (l : ProgLabels) (k : List Asm) :
    wpRest l ++ k = wpRestOpen l k := by
  simp only [wpRest, List.append_assoc, wpRestOpen]

def wpNextOpen (l : ProgLabels) (k : List Asm) : List Asm :=
  store Icell (.bin .add (.load Icell) (.imm 1)) ++
  ([.jump l.lweBytes] ++ ([.label l.lwZeroMod] ++ (wpZeroMod l ++ k)))

theorem wpNext_open (l : ProgLabels) (k : List Asm) :
    wpNext l ++ k = wpNextOpen l k := by
  simp only [wpNext, List.append_assoc, wpNextOpen]

def wpSerOpen (_l : ProgLabels) (k : List Asm) : List Asm :=
  store RET (.bin .shl (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
    (.load T2)) ++
  (compileExpr (.load MS) ++ (compileExpr (.imm RET) ++ ([.op .ret] ++ k)))

theorem wpSer_open (l : ProgLabels) (k : List Asm) :
    wpSer l ++ k = wpSerOpen l k := by
  simp only [wpSer, List.append_assoc, wpSerOpen]

theorem findLweScanOpenK : findLabel programLabels.lweScan programAsm =
    some (wpScanOpen programLabels contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm,
    ← wpScan_open]
  exact findLweScan

theorem findLweTopOpenK : findLabel programLabels.lweTop programAsm =
    some (wpTopBitOpen programLabels contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm,
    ← wpTopBit_open]
  exact findLweTop

theorem findLweBitsK :
    findLabel programLabels.lweBits programAsm = some (wpBits programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweBits

theorem findLweBitsOpenK : findLabel programLabels.lweBits programAsm =
    some (wpBitsOpen programLabels contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm,
    ← wpBits_open]
  exact findLweBits

theorem findLweBytesOpenK : findLabel programLabels.lweBytes programAsm =
    some (wpBytesOpen programLabels contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm,
    ← wpBytes_open]
  exact findLweBytes

theorem findLweByteBitsOpenK : findLabel programLabels.lweByteBits programAsm =
    some (wpByteBitsOpen programLabels contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm,
    ← wpByteBits_open]
  exact findLweByteBits

theorem evalExpr_sq {m x : Nat} {yst : EvmState}
    (hT2 : loadWord yst.memory T2 = W x)
    (hT0 : loadWord yst.memory T0 = W m)
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256) (hx : x < 2 ^ 256) :
    evalExpr (.ter .mulmod (.load T2) (.load T2) (.load T0)) yst
      = W ((x * x) % m) := by
  show (if loadWord yst.memory T0 = 0 then 0 else
    W ((loadWord yst.memory T2).toNat * (loadWord yst.memory T2).toNat
      % (loadWord yst.memory T0).toNat)) = _
  rw [hT0, if_neg (W_ne_zero (by omega) hm256), hT2, toNat_W hx, toNat_W hm256]

theorem evalExpr_mulbase {m x t : Nat} {yst : EvmState}
    (hT2 : loadWord yst.memory T2 = W x) (hT1 : loadWord yst.memory T1 = W t)
    (hT0 : loadWord yst.memory T0 = W m)
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256) (hx : x < 2 ^ 256) (ht : t < 2 ^ 256) :
    evalExpr (.ter .mulmod (.load T2) (.load T1) (.load T0)) yst
      = W ((x * t) % m) := by
  show (if loadWord yst.memory T0 = 0 then 0 else
    W ((loadWord yst.memory T2).toNat * (loadWord yst.memory T1).toNat
      % (loadWord yst.memory T0).toNat)) = _
  rw [hT0, if_neg (W_ne_zero (by omega) hm256), hT2, hT1, toNat_W hx, toNat_W ht,
    toNat_W hm256]

theorem evalExpr_bitTest {w j : Nat} {yst : EvmState}
    (hW : loadWord yst.memory Wcell = W w) (hJ : loadWord yst.memory Jcell = W j)
    (hw256 : w < 2 ^ 256) (hj256 : j < 2 ^ 256) :
    evalExpr bitTest yst = W ((w / 2 ^ j) % 2) := by
  show (loadWord yst.memory Wcell >>> (loadWord yst.memory Jcell).toNat) &&& W 1 = _
  rw [hW, hJ, toNat_W hj256, W_shr hw256,
    W_and_one (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw256)]

theorem evalExpr_jdec {j : Nat} {yst : EvmState}
    (hJ : loadWord yst.memory Jcell = W j) (hj0 : 0 < j) (hj256 : j < 2 ^ 256) :
    evalExpr (.bin .sub (.load Jcell) (.imm 1)) yst = W (j - 1) := by
  show loadWord yst.memory Jcell - W 1 = _
  rw [hJ, W_sub (b := 1) (a := j) hj0 (by norm_num : (0 : Nat) < 1) hj256]

theorem evalExpr_mod1 {m : Nat} {yst : EvmState}
    (hT0 : loadWord yst.memory T0 = W m)
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256) :
    evalExpr (.bin .mod (.imm 1) (.load T0)) yst = W (1 % m) := by
  show (if loadWord yst.memory T0 = 0 then 0 else W 1 % loadWord yst.memory T0) = _
  rw [hT0, if_neg (W_ne_zero (by omega) hm256), W_mod (by norm_num) hm0 hm256]

theorem evalExpr_serShl {calldata : ByteArray} {bs es ms bo eo r : Nat}
    {yst : EvmState}
    (hf : WPState yst calldata bs es ms bo eo mo)
    (hT2 : loadWord yst.memory T2 = W r)
    (hms0 : 0 < ms) (hms32 : ms ≤ 32) (_hr256 : r < 2 ^ 256) :
    evalExpr (.bin .shl (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
      (.load T2)) yst = (W r <<< ((32 - ms) * 8)) := by
  have hsub : evalExpr (.bin .sub (.imm 32) (.load MS)) yst = W (32 - ms) := by
    show W 32 - loadWord yst.memory MS = _
    rw [hf.MSw, W_sub hms32 hms0 (by omega)]
  have hmul : evalExpr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8)) yst
      = W ((32 - ms) * 8) := by
    show evalExpr (.bin .sub (.imm 32) (.load MS)) yst * W 8 = _
    rw [hsub, W_mul]
  show loadWord yst.memory T2 <<< (evalExpr (.bin .mul
      (.bin .sub (.imm 32) (.load MS)) (.imm 8)) yst).toNat = _
  rw [hT2, hmul, toNat_W (by omega : (32 - ms) * 8 < 2 ^ 256)]

theorem storeW2 {c : Nat} {w : U256} {e : Expr} {yst : EvmState} {k : List Asm}
    (he : exprOK e yst) (hcpin : c + 32 ≤ 8000) (haw : yst.activeWords.toNat = 250)
    (hval : evalExpr e yst = w) :
    ASteps programAsm ⟨store c e ++ k, [], yst⟩
      ⟨k, [], { yst with memory := storeWord yst.memory c w }⟩ := by
  have hc : c < 2 ^ 256 ∧ c + 32 ≤ 32 * yst.activeWords.toNat := by
    rw [haw]
    omega
  have h := store_steps (model := localModel) (prog := programAsm)
    (k := k) (σ := []) he hc
  rwa [hval] at h

/-- Exponent-prefix doubling at a plain bit boundary. -/
theorem div_step (w n : Nat) (hn : 0 < n) :
    w / 2 ^ (n - 1) = 2 * (w / 2 ^ n) + w / 2 ^ (n - 1) % 2 := by
  have hdd : w / 2 ^ n = (w / 2 ^ (n - 1)) / 2 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ,
      show Nat.succ (n - 1) = n from by omega]
  have hdm := Nat.div_add_mod (w / 2 ^ (n - 1)) 2
  omega

/-! ## Small helpers -/

/-- The word-path entry predicate: what the header/assembly proof supplies.
`activeWords` may be anywhere at or below 250; the path's first statement
(`store TOP 0`) pins it at exactly 250. -/
structure WordEntry (yst : EvmState) (calldata : ByteArray)
    (bs es ms bo eo mo : Nat) : Prop where
  aw : yst.activeWords.toNat ≤ 250
  cd : yst.env.calldata = calldata.toList
  cBS : loadWord yst.memory BS = W bs
  cES : loadWord yst.memory ES = W es
  cMS : loadWord yst.memory MS = W ms
  cBO : loadWord yst.memory BO = W bo
  cEO : loadWord yst.memory EO = W eo
  cMO : loadWord yst.memory MO = W mo

theorem exprOK_imm (k : Nat) {yst : EvmState} : exprOK (Expr.imm k) yst := trivial

theorem lt256_of_lt {w : Nat} (h : w < 256) : w < 2 ^ 256 :=
  Nat.lt_of_lt_of_le h (by norm_num)

theorem exprOK_add1 {yst : EvmState} {calldata : ByteArray} {bs es ms bo eo mo : Nat}
    (hf : WPState yst calldata bs es ms bo eo mo) :
    exprOK (.bin .add (.load Icell) (.imm 1)) yst := by
  show binOK .add = true ∧ exprOK (Expr.load Icell) yst ∧ exprOK (Expr.imm 1) yst
  exact ⟨rfl, pinLoad (by decide) hf, trivial⟩

theorem evalExpr_add1 {i : Nat} {yst : EvmState}
    (hI : loadWord yst.memory Icell = W i) (hi : i + 1 < 2 ^ 256) :
    evalExpr (.bin .add (.load Icell) (.imm 1)) yst = W (i + 1) := by
  show loadWord yst.memory Icell + W 1 = _
  rw [hI, W_add hi]

theorem exprOK_T0 {calldata : ByteArray} {bs es ms bo eo mo : Nat} {yst : EvmState}
    (hf : WPState yst calldata bs es ms bo eo mo) :
    exprOK (.bin .shr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
      (.cdload (.load MO))) yst := by
  show binOK .shr = true ∧
    (binOK .mul = true ∧
      (binOK .sub = true ∧ exprOK (Expr.imm 32) yst ∧ exprOK (Expr.load MS) yst) ∧
      exprOK (Expr.imm 8) yst) ∧
    exprOK (Expr.cdload (Expr.load MO)) yst
  exact ⟨rfl, ⟨rfl, ⟨rfl, trivial, pinLoad (by decide) hf⟩, trivial⟩,
    pinLoad (by decide) hf⟩

theorem topStore_step {yst : EvmState} {k : List Asm} :
    ASteps programAsm ⟨store TOP (.imm 0) ++ k, [], yst⟩ ⟨k, [],
      { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 }⟩ := by
  have h := store_steps_exact (model := localModel) (prog := programAsm)
    (c := TOP) (e := Expr.imm 0) (k := k) (σ := []) (yst := yst) (by trivial)
  rwa [show TOP % 2 ^ 256 = TOP from by decide,
    show evalExpr (Expr.imm 0) yst = 0 from rfl] at h

theorem topStored_activeWords {yst : EvmState} (haw : yst.activeWords.toNat ≤ 250) :
    (touchMemory yst TOP 32).activeWords.toNat = 250 := by
  show YulSemantics.EVM.activeWordsAfter yst.activeWords.toNat TOP 32 % 2 ^ 256 = 250
  have hAW : YulSemantics.EVM.activeWordsAfter yst.activeWords.toNat TOP 32 = 250 := by
    show (if (32 : Nat) = 0 then yst.activeWords.toNat
      else Nat.max yst.activeWords.toNat ((TOP + 32 - 1) / 32 + 1)) = 250
    rw [if_neg (by norm_num), show (TOP + 32 - 1) / 32 + 1 = 250 from by decide]
    exact Nat.max_eq_right haw
  rw [hAW, Nat.mod_eq_of_lt (by norm_num : (250 : Nat) < 2 ^ 256)]

theorem topStored_WPState {calldata : ByteArray} {bs es ms bo eo mo : Nat} {yst : EvmState}
    (hent : WordEntry yst calldata bs es ms bo eo mo) :
    WPState { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 }
      calldata bs es ms bo eo mo := by
  refine ⟨topStored_activeWords hent.aw, hent.cd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show loadWord (storeWord yst.memory TOP 0) BS = W bs
    rw [loadCell_storeCell (c := TOP) (q := BS) (by decide)]
    exact hent.cBS
  · show loadWord (storeWord yst.memory TOP 0) ES = W es
    rw [loadCell_storeCell (c := TOP) (q := ES) (by decide)]
    exact hent.cES
  · show loadWord (storeWord yst.memory TOP 0) MS = W ms
    rw [loadCell_storeCell (c := TOP) (q := MS) (by decide)]
    exact hent.cMS
  · show loadWord (storeWord yst.memory TOP 0) BO = W bo
    rw [loadCell_storeCell (c := TOP) (q := BO) (by decide)]
    exact hent.cBO
  · show loadWord (storeWord yst.memory TOP 0) EO = W eo
    rw [loadCell_storeCell (c := TOP) (q := EO) (by decide)]
    exact hent.cEO
  · show loadWord (storeWord yst.memory TOP 0) MO = W mo
    rw [loadCell_storeCell (c := TOP) (q := MO) (by decide)]
    exact hent.cMO

/-- The prefix through the modulus load and the zero test: from the entry
state to the `jumpIfZ (.load T0)` with the frame established and
`T0 = W (bytesToNatPadded calldata mo ms)`. -/
theorem prefix_stores {calldata : ByteArray} {bs es ms bo eo mo : Nat} {yst : EvmState}
    (hbs : bs ≤ 1024) (hes : es ≤ 1024) (hms0 : 0 < ms) (hms32 : ms ≤ 32)
    (hbo : bo = 96) (heo : eo = bo + bs) (hmo : mo = eo + es)
    (hent : WordEntry yst calldata bs es ms bo eo mo) (k : List Asm) :
    ∃ y2 : EvmState,
      (WPState y2 calldata bs es ms bo eo mo ∧
        loadWord y2.memory T0 = W (bytesToNatPadded calldata mo ms)) ∧
      ASteps programAsm ⟨wpPrefixOpen programLabels k, [], yst⟩
        ⟨jumpIfZ (.load T0) programLabels.lwZeroMod ++
          (store T1 (.imm 0) ++ (store Icell (.imm 0) ++
          ([.label programLabels.lwbLoop] ++ (wpLwbLoop programLabels ++ k)))),
          [], y2⟩ := by
  have hs0 : ASteps programAsm ⟨wpPrefixOpen programLabels k, [], yst⟩
      ⟨store T0 (.bin .shr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
        (.cdload (.load MO))) ++ (jumpIfZ (.load T0) programLabels.lwZeroMod ++
        (store T1 (.imm 0) ++ (store Icell (.imm 0) ++
        ([.label programLabels.lwbLoop] ++ (wpLwbLoop programLabels ++ k))))), [],
        { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 }⟩ :=
    topStore_step
  have hf1 : WPState { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 }
      calldata bs es ms bo eo mo := topStored_WPState hent
  have hv0 : evalExpr (.bin .shr (.bin .mul (.bin .sub (.imm 32) (.load MS)) (.imm 8))
      (.cdload (.load MO))) { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 }
      = W (bytesToNatPadded calldata mo ms) :=
    evalExpr_T0 hf1 hms0 hms32 hbo hbs hes heo hmo
  have hs1 : ASteps programAsm ⟨store T0 (.bin .shr (.bin .mul
        (.bin .sub (.imm 32) (.load MS)) (.imm 8))
        (.cdload (.load MO))) ++ (jumpIfZ (.load T0) programLabels.lwZeroMod ++
        (store T1 (.imm 0) ++ (store Icell (.imm 0) ++
        ([.label programLabels.lwbLoop] ++ (wpLwbLoop programLabels ++ k))))), [],
        { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 }⟩
      ⟨jumpIfZ (.load T0) programLabels.lwZeroMod ++
          (store T1 (.imm 0) ++ (store Icell (.imm 0) ++
          ([.label programLabels.lwbLoop] ++ (wpLwbLoop programLabels ++ k)))), [],
        { { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 } with
          memory := storeWord (storeWord yst.memory TOP 0) T0
            (W (bytesToNatPadded calldata mo ms)) }⟩ :=
    storeW (c := T0) (yst := { touchMemory yst TOP 32 with
      memory := storeWord yst.memory TOP 0 }) (exprOK_T0 hf1) (by decide) hf1.1 hv0
  refine ⟨{ { touchMemory yst TOP 32 with memory := storeWord yst.memory TOP 0 } with
    memory := storeWord (storeWord yst.memory TOP 0) T0
      (W (bytesToNatPadded calldata mo ms)) }, ⟨⟨?_, ?_⟩, hs0.trans hs1⟩⟩
  · refine ⟨hf1.1, hf1.cd, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show loadWord (storeWord (storeWord yst.memory TOP 0) T0
          (W (bytesToNatPadded calldata mo ms))) BS = W bs
      rw [loadCell_storeCell (c := T0) (q := BS) (by decide),
        loadCell_storeCell (c := TOP) (q := BS) (by decide)]
      exact hent.cBS
    · show loadWord (storeWord (storeWord yst.memory TOP 0) T0
          (W (bytesToNatPadded calldata mo ms))) ES = W es
      rw [loadCell_storeCell (c := T0) (q := ES) (by decide),
        loadCell_storeCell (c := TOP) (q := ES) (by decide)]
      exact hent.cES
    · show loadWord (storeWord (storeWord yst.memory TOP 0) T0
          (W (bytesToNatPadded calldata mo ms))) MS = W ms
      rw [loadCell_storeCell (c := T0) (q := MS) (by decide),
        loadCell_storeCell (c := TOP) (q := MS) (by decide)]
      exact hent.cMS
    · show loadWord (storeWord (storeWord yst.memory TOP 0) T0
          (W (bytesToNatPadded calldata mo ms))) BO = W bo
      rw [loadCell_storeCell (c := T0) (q := BO) (by decide),
        loadCell_storeCell (c := TOP) (q := BO) (by decide)]
      exact hent.cBO
    · show loadWord (storeWord (storeWord yst.memory TOP 0) T0
          (W (bytesToNatPadded calldata mo ms))) EO = W eo
      rw [loadCell_storeCell (c := T0) (q := EO) (by decide),
        loadCell_storeCell (c := TOP) (q := EO) (by decide)]
      exact hent.cEO
    · show loadWord (storeWord (storeWord yst.memory TOP 0) T0
          (W (bytesToNatPadded calldata mo ms))) MO = W mo
      rw [loadCell_storeCell (c := T0) (q := MO) (by decide),
        loadCell_storeCell (c := TOP) (q := MO) (by decide)]
      exact hent.cMO
  · show loadWord (storeWord (storeWord yst.memory TOP 0) T0
        (W (bytesToNatPadded calldata mo ms))) T0 = W (bytesToNatPadded calldata mo ms)
    rw [loadWord_storeWord]

set_option maxHeartbeats 10000000 in
/-- Prefix, zero-modulus case: control jumps to `lwZeroMod`. -/
theorem prefix_zero {calldata : ByteArray} {bs es ms bo eo mo : Nat} {yst : EvmState}
    (hbs : bs ≤ 1024) (hes : es ≤ 1024) (hms0 : 0 < ms) (hms32 : ms ≤ 32)
    (hbo : bo = 96) (heo : eo = bo + bs) (hmo : mo = eo + es)
    (hent : WordEntry yst calldata bs es ms bo eo mo)
    (hm : bytesToNatPadded calldata mo ms = 0) :
    ∃ y2 : EvmState,
      (WPState y2 calldata bs es ms bo eo mo ∧
        loadWord y2.memory T0 = W (bytesToNatPadded calldata mo ms)) ∧
      ASteps programAsm ⟨wpPrefixOpen programLabels contK, [], yst⟩
        ⟨wpZeroMod programLabels ++ contK, [], y2⟩ := by
  obtain ⟨y2, ⟨hf2, hT0y2⟩, hsteps⟩ :=
    prefix_stores hbs hes hms0 hms32 hbo heo hmo hent contK
  have hz : evalExpr (Expr.load T0) y2 = 0 := by
    show loadWord y2.memory T0 = 0
    rw [hT0y2, hm]
    rfl
  exact ⟨y2, ⟨hf2, hT0y2⟩,
    hsteps.trans (jumpIfZ_taken (model := localModel) (prog := programAsm)
      (k := store T1 (.imm 0) ++ (store Icell (.imm 0) ++
        ([.label programLabels.lwbLoop] ++ (wpLwbLoop programLabels ++ contK))))
      (pinLoad (c := T0) (by decide) hf2) hz findLwZeroModK)⟩

set_option maxHeartbeats 10000000 in
/-- Prefix, nonzero-modulus case, first half: through the zero test and the
`T1 := 0` store. -/
theorem prefix_nonzero_1 {calldata : ByteArray} {bs es ms bo eo mo : Nat} {yst : EvmState}
    (hbs : bs ≤ 1024) (hes : es ≤ 1024) (hms0 : 0 < ms) (hms32 : ms ≤ 32)
    (hbo : bo = 96) (heo : eo = bo + bs) (hmo : mo = eo + es)
    (hent : WordEntry yst calldata bs es ms bo eo mo)
    (hm0 : 0 < bytesToNatPadded calldata mo ms)
    (hm256 : bytesToNatPadded calldata mo ms < 2 ^ 256)
    (k : List Asm) :
    ∃ y2 : EvmState,
      (WPState y2 calldata bs es ms bo eo mo ∧
        loadWord y2.memory T0 = W (bytesToNatPadded calldata mo ms) ∧
        loadWord y2.memory T1 = W 0) ∧
      ASteps programAsm ⟨wpPrefixOpen programLabels k, [], yst⟩
        ⟨store Icell (.imm 0) ++ ([.label programLabels.lwbLoop] ++
          (wpLwbLoop programLabels ++ k)), [], y2⟩ := by
  obtain ⟨y2, ⟨hf2, hT0y2⟩, hsteps⟩ :=
    prefix_stores hbs hes hms0 hms32 hbo heo hmo hent k
  have hne : evalExpr (Expr.load T0) y2 ≠ 0 := by
    show loadWord y2.memory T0 ≠ 0
    rw [hT0y2]
    exact W_ne_zero (Nat.ne_of_gt hm0) hm256
  refine ⟨{ y2 with memory := storeWord y2.memory T1 0 },
    ⟨⟨hf2, hT0y2, ?_⟩, hsteps.trans ((jumpIfZ_fall (model := localModel)
      (prog := programAsm) (pinLoad (c := T0) (by decide) hf2) hne).trans
      (storeW (c := T1) (yst := y2) (exprOK_imm 0) (by decide) hf2.1
        (rfl : evalExpr (Expr.imm 0) y2 = W 0)))⟩⟩
  · show loadWord (storeWord y2.memory T1 0) T1 = W 0
    rw [loadWord_storeWord]
    decide

set_option maxHeartbeats 10000000 in
/-- Prefix, nonzero-modulus case, second half: the `Icell := 0` store and the
loop label. -/
theorem prefix_nonzero {calldata : ByteArray} {bs es ms bo eo mo : Nat} {yst : EvmState}
    (hbs : bs ≤ 1024) (hes : es ≤ 1024) (hms0 : 0 < ms) (hms32 : ms ≤ 32)
    (hbo : bo = 96) (heo : eo = bo + bs) (hmo : mo = eo + es)
    (hent : WordEntry yst calldata bs es ms bo eo mo)
    (hm0 : 0 < bytesToNatPadded calldata mo ms)
    (hm256 : bytesToNatPadded calldata mo ms < 2 ^ 256)
    (k : List Asm) :
    ∃ y2 : EvmState,
      (WPState y2 calldata bs es ms bo eo mo ∧
        loadWord y2.memory T0 = W (bytesToNatPadded calldata mo ms) ∧
        loadWord y2.memory T1 = W 0 ∧ loadWord y2.memory Icell = W 0) ∧
      ASteps programAsm ⟨wpPrefixOpen programLabels k, [], yst⟩
        ⟨wpLwbLoop programLabels ++ k, [], y2⟩ := by
  obtain ⟨y2, ⟨hf2, hT0y2, hT1y2⟩, hsteps⟩ :=
    prefix_nonzero_1 hbs hes hms0 hms32 hbo heo hmo hent hm0 hm256 k
  refine ⟨{ y2 with memory := storeWord y2.memory Icell 0 },
    ⟨⟨hf2, hT0y2, hT1y2, ?_⟩,
      (hsteps.trans (storeW (c := Icell) (yst := y2) (exprOK_imm 0) (by decide)
        hf2.1 (rfl : evalExpr (Expr.imm 0) y2 = W 0))).trans
        (labelStep programLabels.lwbLoop)⟩⟩
  · show loadWord (storeWord y2.memory Icell 0) Icell = W 0
    rw [loadWord_storeWord]
    decide

/-- From `lwbDone` into the exponent scan: `Icell` reset to 0. -/
theorem lwbDone_to_scan {calldata : ByteArray} {bs es ms bo eo mo m : Nat}
    {y : EvmState}
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m)
    (hT1 : loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m)) :
    ∃ y' : EvmState,
      (WPState y' calldata bs es ms bo eo mo ∧
        loadWord y'.memory T0 = W m ∧
        loadWord y'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y'.memory Icell = W 0) ∧
      ASteps programAsm ⟨wpLwbDoneOpen programLabels contK, [], y⟩
        ⟨wpScanOpen programLabels contK, [], y'⟩ := by
  have hs1 : ASteps programAsm ⟨wpLwbDoneOpen programLabels contK, [], y⟩
      ⟨[.label programLabels.lweScan] ++ (wpScan programLabels ++ contK), [],
        { y with memory := storeWord y.memory Icell 0 }⟩ :=
    storeW (c := Icell) (yst := y) (exprOK_imm 0) (by decide) hfy.1
      (rfl : evalExpr (Expr.imm 0) y = W 0)
  have hframe := WPState_store1 (c := Icell) (v := 0) hfy hT0 (by decide)
  exact ⟨{ y with memory := storeWord y.memory Icell 0 },
    ⟨hframe.1, hframe.2, hT1, by
      show loadWord (storeWord y.memory Icell 0) Icell = W 0
      rw [loadWord_storeWord]
      decide⟩,
    hs1.trans (labelStep programLabels.lweScan)⟩

set_option maxHeartbeats 10000000 in
/-- The exponent scan: from `lweScan` with `Icell = W i` and a zero exponent
prefix at `eo` to the first nonzero byte (`lwInit`), or exhaustion
(`lweExpZero`, prefix value 0). -/
theorem scanLoop {calldata : ByteArray} {bs es ms bo eo mo m : Nat}
    (hbs : bs ≤ 1024) (hes : es ≤ 1024) (hbo : bo = 96) (heo : eo = bo + bs) :
    ∀ (n i : Nat), i + n = es →
      ∀ (y : EvmState),
      (WPState y calldata bs es ms bo eo mo ∧
        loadWord y.memory T0 = W m ∧
        loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y.memory Icell = W i ∧
        bytesToNatPadded calldata eo i = 0) →
      (∃ y' w j, (WPState y' calldata bs es ms bo eo mo ∧
          loadWord y'.memory T0 = W m ∧
          loadWord y'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
          loadWord y'.memory Icell = W j ∧
          loadWord y'.memory Wcell = W w ∧ w ≠ 0 ∧ w < 256 ∧
          j < es ∧ bytesToNatPadded calldata eo j = 0 ∧
          (byteFrom calldata.toList (eo + j)).toNat = w) ∧
        ASteps programAsm ⟨wpScanOpen programLabels contK, [], y⟩
          ⟨wpLwInit programLabels ++ contK, [], y'⟩) ∨
      (∃ y', (WPState y' calldata bs es ms bo eo mo ∧
          loadWord y'.memory T0 = W m ∧
          loadWord y'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
          loadWord y'.memory Icell = W es ∧
          bytesToNatPadded calldata eo es = 0) ∧
        ASteps programAsm ⟨wpScanOpen programLabels contK, [], y⟩
          ⟨wpExpZero programLabels ++ contK, [], y'⟩) := by
  intro n
  induction n with
  | zero =>
    intro i hi y inv
    obtain ⟨hfy, hT0y, hT1y, hIy, hpfx⟩ := inv
    have hie : i = es := by omega
    rw [hie] at hIy hpfx
    right
    refine ⟨y, ⟨hfy, hT0y, hT1y, hIy, hpfx⟩, ?_⟩
    have hnlt : ¬(evalExpr (Expr.load Icell) y).ult (evalExpr (Expr.load ES) y) := by
      show ¬ ((loadWord y.memory Icell).ult (loadWord y.memory ES) = true)
      rw [hIy, hfy.ESw]
      exact W_nult (by omega) (by omega) (Nat.le_refl es)
    exact jumpUnlessLt_taken (model := localModel) (prog := programAsm)
      (pinLoad (c := Icell) (by decide) hfy) (pinLoad (c := ES) (by decide) hfy)
      hnlt findLweExpZeroK
  | succ n ih =>
    intro i hi y inv
    obtain ⟨hfy, hT0y, hT1y, hIy, hpfx⟩ := inv
    have hies : i < es := by omega
    have hlt : (evalExpr (Expr.load Icell) y).ult (evalExpr (Expr.load ES) y) := by
      show (loadWord y.memory Icell).ult (loadWord y.memory ES) = true
      rw [hIy, hfy.ESw]
      exact W_ult (by omega) (by omega) hies
    set wb := (byteFrom calldata.toList (eo + i)).toNat with hwbdef
    have hb256 : wb < 256 := by
      have := (byteFrom calldata.toList (eo + i)).toNat_lt
      omega
    have hWval : evalExpr (cdbCell EO) y = W wb := by
      have haddr : (evalExpr (Expr.bin .add (Expr.load EO) (Expr.load Icell)) y).toNat
          = eo + i := by
        show (loadWord y.memory EO + loadWord y.memory Icell).toNat = eo + i
        rw [hfy.EOw, hIy, W_add (by omega), toNat_W (by omega)]
      show evalExpr (Expr.cdb (Expr.bin .add (Expr.load EO) (Expr.load Icell))) y = _
      rw [evalExpr_cdb haddr, hfy.cd]
    have hs1 : ASteps programAsm ⟨wpScanOpen programLabels contK, [], y⟩
        ⟨jumpIfNz (.load Wcell) programLabels.lwInit ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lweScan] ++ ([.label programLabels.lweExpZero] ++
          (wpExpZero programLabels ++ contK)))), [],
          { y with memory := storeWord y.memory Wcell (W wb) }⟩ :=
      (jumpUnlessLt_fall (model := localModel) (prog := programAsm)
        (pinLoad (c := Icell) (by decide) hfy) (pinLoad (c := ES) (by decide) hfy)
        hlt).trans
        (storeW (c := Wcell) (yst := y) (pinCdbCell (base := EO) (by decide) hfy)
          (by decide) hfy.1 hWval)
    have hframe1 := WPState_store1 (c := Wcell) (v := W wb) hfy hT0y (by decide)
    by_cases hwb : wb = 0
    · -- zero byte: increment and continue
      have hIval : evalExpr (.bin .add (.load Icell) (.imm 1)) y = W (i + 1) :=
        evalExpr_add1 hIy (by omega)
      have hz0 : evalExpr (Expr.load Wcell) { y with memory := storeWord y.memory Wcell (W wb) }
          = 0 := by
        show loadWord (storeWord y.memory Wcell (W wb)) Wcell = 0
        rw [loadWord_storeWord, hwb]
        rfl
      have hs2 : ASteps programAsm ⟨jumpIfNz (.load Wcell) programLabels.lwInit ++
          (store Icell (.bin .add (.load Icell) (.imm 1)) ++
          ([.jump programLabels.lweScan] ++ ([.label programLabels.lweExpZero] ++
          (wpExpZero programLabels ++ contK)))), [],
          { y with memory := storeWord y.memory Wcell (W wb) }⟩
          ⟨[.jump programLabels.lweScan] ++ ([.label programLabels.lweExpZero] ++
          (wpExpZero programLabels ++ contK)), [],
          { y with memory := storeWord (storeWord y.memory Wcell (W wb)) Icell (W (i + 1)) }⟩ :=
        (jumpIfNz_fall (model := localModel) (prog := programAsm)
          (k := store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.jump programLabels.lweScan] ++ ([.label programLabels.lweExpZero] ++
            (wpExpZero programLabels ++ contK))))
          (pinLoad (c := Wcell) (by decide) hframe1.1) hz0).trans
        (storeW (c := Icell)
          (yst := { y with memory := storeWord y.memory Wcell (W wb) })
          (exprOK_add1 hframe1.1) (by decide) hframe1.1.1 hIval)
      have hframe2 := WPState_store2 (c1 := Wcell) (c2 := Icell) (v1 := W wb)
        (v2 := W (i + 1)) hfy hT0y (by decide)
      have hs3 : ASteps programAsm ⟨[.jump programLabels.lweScan] ++
          ([.label programLabels.lweExpZero] ++
          (wpExpZero programLabels ++ contK)), [],
          { y with memory := storeWord (storeWord y.memory Wcell (W wb)) Icell (W (i + 1)) }⟩
          ⟨wpScanOpen programLabels contK, [],
            { y with memory := storeWord (storeWord y.memory Wcell (W wb)) Icell (W (i + 1)) }⟩ :=
        jumpTo findLweScanOpenK
      have hpfx' : bytesToNatPadded calldata eo (i + 1) = 0 := by
        rw [bytesToNatPadded_succ, hpfx]
        omega
      have hIcell' : loadWord (storeWord (storeWord y.memory Wcell (W wb)) Icell (W (i + 1))) Icell
          = W (i + 1) := by
        show loadWord (storeWord (storeWord y.memory Wcell (W wb)) Icell (W (i + 1))) Icell
          = W (i + 1)
        rw [loadWord_storeWord]
      have ihres := ih (i + 1) (by omega)
        { y with memory := storeWord (storeWord y.memory Wcell (W wb)) Icell (W (i + 1)) }
        ⟨hframe2.1, hframe2.2, hT1y, hIcell', hpfx'⟩
      rcases ihres with ⟨y'', w', j', hinv'', hsteps⟩ | ⟨y'', hinv'', hsteps⟩
      · exact Or.inl ⟨y'', w', j', hinv'',
          (hs1.trans (hs2.trans hs3)).trans hsteps⟩
      · exact Or.inr ⟨y'', hinv'',
          (hs1.trans (hs2.trans hs3)).trans hsteps⟩
    · -- nonzero byte: found
      left
      have hne : evalExpr (Expr.load Wcell) { y with memory := storeWord y.memory Wcell (W wb) }
          ≠ 0 := by
        show loadWord (storeWord y.memory Wcell (W wb)) Wcell ≠ 0
        rw [loadWord_storeWord]
        exact W_ne_zero hwb (by omega)
      refine ⟨{ y with memory := storeWord y.memory Wcell (W wb) }, wb, i,
        ⟨hframe1.1, hframe1.2, hT1y, hIy, ?_, hwb, by omega, hies, hpfx, hwbdef.symm⟩,
        ?_⟩
      · show loadWord (storeWord y.memory Wcell (W wb)) Wcell = W wb
        rw [loadWord_storeWord]
      · exact hs1.trans (jumpIfNz_taken (model := localModel) (prog := programAsm)
          (k := store Icell (.bin .add (.load Icell) (.imm 1)) ++
            ([.jump programLabels.lweScan] ++ ([.label programLabels.lweExpZero] ++
            (wpExpZero programLabels ++ contK))))
          (pinLoad (c := Wcell) (by decide) hframe1.1) hne findLwInitK)

/-- The zero-exponent branch: `T2 := 1 % m`, then serialize. -/
theorem expZero_path {calldata : ByteArray} {bs es ms bo eo mo m : Nat}
    {y : EvmState}
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m) (hm0 : 0 < m) (hm256 : m < 2 ^ 256) :
    ∃ y' : EvmState,
      (WPState y' calldata bs es ms bo eo mo ∧
        loadWord y'.memory T0 = W m ∧
        loadWord y'.memory T2 = W (1 % m)) ∧
      ASteps programAsm ⟨wpExpZeroOpen programLabels contK, [], y⟩
        ⟨wpSer programLabels ++ contK, [], y'⟩ := by
  have hval : evalExpr (.bin .mod (.imm 1) (.load T0)) y = W (1 % m) :=
    evalExpr_mod1 hT0 hm0 hm256
  have he1 : exprOK (.bin .mod (.imm 1) (.load T0)) y := by
    show binOK .mod = true ∧ exprOK (Expr.imm 1) y ∧ exprOK (Expr.load T0) y
    exact ⟨rfl, trivial, pinLoad (c := T0) (by decide) hfy⟩
  have hframe := WPState_store1 (c := T2) (v := W (1 % m)) hfy hT0 (by decide)
  refine ⟨{ y with memory := storeWord y.memory T2 (W (1 % m)) },
    ⟨⟨hframe.1, hframe.2, ?_⟩,
      (storeW (c := T2) (yst := y) he1 (by decide) hfy.1 hval).trans
        (jumpTo findLweSerK)⟩⟩
  · show loadWord (storeWord y.memory T2 (W (1 % m))) T2 = W (1 % m)
    rw [loadWord_storeWord]


set_option maxHeartbeats 10000000 in
/-- The bit loop proper: from `lweBits` with `Jcell = W n` and
`T2 = W (b ^ (w / 2^n) % m)` to `lweRest` with `T2 = W (b ^ w % m)`.
The intermediate states are named (`yA`, `yQ`, `yM`) so no nested structure
literal is ever elaborated twice. -/
theorem bitsLoop_correct {calldata : ByteArray} {bs es ms bo eo mo m w i0 n0 : Nat}
    {y : EvmState}
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256) (hw256 : w < 256)
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m)
    (hT1 : loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m))
    (hI : loadWord y.memory Icell = W i0)
    (hW : loadWord y.memory Wcell = W w)
    (hJ : loadWord y.memory Jcell = W n0) (hn0le : n0 ≤ 7)
    (hT2 : loadWord y.memory T2
      = W (bytesToNatPadded calldata bo bs ^ (w / 2 ^ n0) % m)) :
    ∃ y' : EvmState,
      (WPState y' calldata bs es ms bo eo mo ∧
        loadWord y'.memory T0 = W m ∧
        loadWord y'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y'.memory Icell = W i0 ∧
        loadWord y'.memory T2 = W (bytesToNatPadded calldata bo bs ^ w % m)) ∧
      ASteps programAsm ⟨wpBitsOpen programLabels contK, [], y⟩
        ⟨wpRest programLabels ++ contK, [], y'⟩ := by
  set bb : Nat := bytesToNatPadded calldata bo bs with hbbdef
  have hbn : bb % m < 2 ^ 256 := Nat.lt_trans (Nat.mod_lt _ hm0) hm256
  have hxn : ∀ n : Nat, bb ^ (w / 2 ^ n) % m < 2 ^ 256 :=
    fun _ => Nat.lt_trans (Nat.mod_lt _ hm0) hm256
  have hround : ∀ {n : Nat} {y3 : EvmState}, 0 < n →
      (WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bb % m) ∧
        loadWord y3.memory Icell = W i0 ∧
        loadWord y3.memory Wcell = W w ∧
        loadWord y3.memory Jcell = W n ∧ n ≤ 7 ∧
        loadWord y3.memory T2 = W (bb ^ (w / 2 ^ n) % m)) →
      (∃ y4, (WPState y4 calldata bs es ms bo eo mo ∧
        loadWord y4.memory T0 = W m ∧
        loadWord y4.memory T1 = W (bb % m) ∧
        loadWord y4.memory Icell = W i0 ∧
        loadWord y4.memory Wcell = W w ∧
        loadWord y4.memory Jcell = W (n - 1) ∧ n - 1 ≤ 7 ∧
        loadWord y4.memory T2 = W (bb ^ (w / 2 ^ (n - 1)) % m)) ∧
        ASteps programAsm ⟨wpBitsOpen programLabels contK, [], y3⟩
          ⟨wpBitsOpen programLabels contK, [], y4⟩) ∨
      ((WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bb % m) ∧
        loadWord y3.memory Icell = W i0 ∧
        loadWord y3.memory T2 = W (bb ^ w % m)) ∧
        ASteps programAsm ⟨wpBitsOpen programLabels contK, [], y3⟩
          ⟨wpRest programLabels ++ contK, [], y3⟩) := by
    intro n y3 hn ⟨hf3, hT0y, hT1y, hIy, hWy, hJy, hnle, hT2y⟩
    left
    set xq : Nat := bb ^ (w / 2 ^ n) % m with hxq
    -- state after the Jcell decrement
    set yA : EvmState := { y3 with memory := storeWord y3.memory Jcell (W (n - 1)) } with hyA
    have hsJ : ASteps programAsm ⟨wpBitsOpen programLabels contK, [], y3⟩
        ⟨store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
          (jumpIfZ bitTest programLabels.lweBits ++
          (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
          ([.jump programLabels.lweBits] ++
          ([.label programLabels.lweRest] ++ (wpRest programLabels ++ contK))))), [], yA⟩ :=
      (jumpIfZ_fall (model := localModel) (prog := programAsm)
        (pinLoad (c := Jcell) (by decide) hf3) (by
          show loadWord y3.memory Jcell ≠ 0
          rw [hJy]
          exact W_ne_zero (by omega) (lt256_of_lt (by omega)))).trans
      (storeW (c := Jcell) (yst := y3)
        (by
          show binOK .sub = true ∧ exprOK (Expr.load Jcell) y3 ∧ exprOK (Expr.imm 1) y3
          exact ⟨rfl, pinLoad (by decide) hf3, trivial⟩)
        (by decide) hf3.1 (evalExpr_jdec hJy hn (lt256_of_lt (by omega))))
    have hframeA : WPState yA calldata bs es ms bo eo mo ∧
        loadWord yA.memory T0 = W m :=
      WPState_store1 (c := Jcell) (v := W (n - 1)) hf3 hT0y (by decide)
    have hJA : loadWord yA.memory Jcell = W (n - 1) := by
      show loadWord (storeWord y3.memory Jcell (W (n - 1))) Jcell = W (n - 1)
      rw [loadWord_storeWord]
    have hTA : loadWord yA.memory T2 = W xq := by
      show loadWord (storeWord y3.memory Jcell (W (n - 1))) T2 = W xq
      rw [loadCell_storeCell (c := Jcell) (q := T2) (by decide)]
      exact hT2y
    -- state after the square
    set yQ : EvmState := { yA with memory := storeWord yA.memory T2 (W (xq * xq % m)) } with hyQ
    have hsq : evalExpr (.ter .mulmod (.load T2) (.load T2) (.load T0)) yA
        = W (xq * xq % m) :=
      evalExpr_sq (m := m) (x := xq) hTA hframeA.2 hm0 hm256 (hxn n)
    have hsQ : ASteps programAsm ⟨store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
          (jumpIfZ bitTest programLabels.lweBits ++
          (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
          ([.jump programLabels.lweBits] ++
          ([.label programLabels.lweRest] ++ (wpRest programLabels ++ contK))))), [], yA⟩
        ⟨jumpIfZ bitTest programLabels.lweBits ++
          (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
          ([.jump programLabels.lweBits] ++
          ([.label programLabels.lweRest] ++ (wpRest programLabels ++ contK)))), [], yQ⟩ :=
      storeW (c := T2) (yst := yA)
        (by
          show terOK .mulmod = true ∧ exprOK (Expr.load T2) _
              ∧ exprOK (Expr.load T2) _ ∧ exprOK (Expr.load T0) _
          exact ⟨rfl, pinLoad (by decide) hframeA.1, pinLoad (by decide) hframeA.1,
            pinLoad (by decide) hframeA.1⟩)
        (by decide) hframeA.1.1 hsq
    have hframeQ : WPState yQ calldata bs es ms bo eo mo ∧
        loadWord yQ.memory T0 = W m :=
      WPState_store1 (c := T2) (v := W (xq * xq % m)) hframeA.1 hframeA.2 (by decide)
    have hQload : loadWord yQ.memory T2 = W (xq * xq % m) := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 = _
      rw [loadWord_storeWord]
    have hWQ : loadWord yQ.memory Wcell = W w := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) Wcell = _
      rw [loadCell_storeCell (c := T2) (q := Wcell) (by decide),
        loadCell_storeCell (c := Jcell) (q := Wcell) (by decide)]
      exact hWy
    have hJQ : loadWord yQ.memory Jcell = W (n - 1) := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) Jcell = _
      rw [loadCell_storeCell (c := T2) (q := Jcell) (by decide)]
      exact hJA
    have hT1Q : loadWord yQ.memory T1 = W (bb % m) := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T1 = _
      rw [loadCell_storeCell (c := T2) (q := T1) (by decide),
        loadCell_storeCell (c := Jcell) (q := T1) (by decide)]
      exact hT1y
    have hbitQ : evalExpr bitTest yQ = W ((w / 2 ^ (n - 1)) % 2) :=
      evalExpr_bitTest hWQ hJQ (lt256_of_lt hw256) (lt256_of_lt (by omega))
    have hd := div_step w n hn
    have hsqm : xq * xq % m = bb ^ (2 * (w / 2 ^ n)) % m :=
      sq_mod (b := bb) (E := w / 2 ^ n) (m := m) (x := xq) rfl
    by_cases hbit : (w / 2 ^ (n - 1)) % 2 = 1
    · -- multiply by the base, then loop
      set yM : EvmState := { yQ with memory := storeWord yQ.memory T2 (W ((xq * xq % m * (bb % m)) % m)) } with hyM
      have hmul : evalExpr (.ter .mulmod (.load T2) (.load T1) (.load T0)) yQ
          = W ((xq * xq % m * (bb % m)) % m) :=
        evalExpr_mulbase (m := m) (x := xq * xq % m) (t := bb % m)
          hQload hT1Q hframeQ.2 hm0 hm256
          (Nat.lt_trans (Nat.mod_lt _ hm0) hm256) hbn
      have hsM : ASteps programAsm ⟨jumpIfZ bitTest programLabels.lweBits ++
            (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
            ([.jump programLabels.lweBits] ++
            ([.label programLabels.lweRest] ++ (wpRest programLabels ++ contK)))), [], yQ⟩
            ⟨[.jump programLabels.lweBits] ++
            ([.label programLabels.lweRest] ++ (wpRest programLabels ++ contK)), [], yM⟩ :=
        (jumpIfZ_fall (model := localModel) (prog := programAsm)
          (pinBitTest hframeQ.1) (by
            show evalExpr bitTest yQ ≠ 0
            rw [hbitQ, hbit]
            exact W_ne_zero one_ne_zero (by norm_num))).trans
        (storeW (c := T2) (yst := yQ)
          (by
            show terOK .mulmod = true ∧ exprOK (Expr.load T2) _
                ∧ exprOK (Expr.load T1) _ ∧ exprOK (Expr.load T0) _
            exact ⟨rfl, pinLoad (by decide) hframeQ.1, pinLoad (by decide) hframeQ.1,
              pinLoad (by decide) hframeQ.1⟩)
          (by decide) hframeQ.1.1 hmul)
      have hframeM : WPState yM calldata bs es ms bo eo mo ∧
          loadWord yM.memory T0 = W m :=
        WPState_store1 (c := T2) (v := W ((xq * xq % m * (bb % m)) % m))
          hframeQ.1 hframeQ.2 (by decide)
      have hMload : loadWord yM.memory T2 = W ((xq * xq % m * (bb % m)) % m) := by
        show loadWord (storeWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 (W ((xq * xq % m * (bb % m)) % m))) T2 = _
        rw [loadWord_storeWord]
      have hJM : loadWord yM.memory Jcell = W (n - 1) := by
        show loadWord (storeWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 (W ((xq * xq % m * (bb % m)) % m))) Jcell = _
        rw [loadCell_storeCell (c := T2) (q := Jcell) (by decide),
          loadCell_storeCell (c := T2) (q := Jcell) (by decide)]
        exact hJA
      have hWM : loadWord yM.memory Wcell = W w := by
        show loadWord (storeWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 (W ((xq * xq % m * (bb % m)) % m))) Wcell = _
        rw [loadCell_storeCell (c := T2) (q := Wcell) (by decide),
          loadCell_storeCell (c := T2) (q := Wcell) (by decide),
          loadCell_storeCell (c := Jcell) (q := Wcell) (by decide)]
        exact hWy
      refine ⟨yM, ⟨hframeM.1, hframeM.2, hT1y, hIy, hWM, hJM, by omega, ?_⟩, ?_⟩
      · show loadWord yM.memory T2 = W (bb ^ (w / 2 ^ (n - 1)) % m)
        rw [hMload]
        have hmulm : (xq * xq % m * (bb % m)) % m
            = bb ^ (2 * (w / 2 ^ n) + 1) % m :=
          mulbase_mod (b := bb) (E := 2 * (w / 2 ^ n)) (m := m)
            (x := xq * xq % m) (t := bb % m) hsqm rfl
        have hde : w / 2 ^ (n - 1) = 2 * (w / 2 ^ n) + 1 := by omega
        rw [hde]
        exact congrArg (BitVec.ofNat 256) hmulm
      · exact ((hsJ.trans hsQ).trans hsM).trans (jumpTo findLweBitsOpenK)
    · -- bit clear: skip the multiply, loop
      refine ⟨yQ, ⟨hframeQ.1, hframeQ.2, hT1y, hIy, hWy, hJQ, by omega, ?_⟩,
        (hsJ.trans hsQ).trans (jumpIfZ_taken (model := localModel) (prog := programAsm)
          (k := store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
            ([.jump programLabels.lweBits] ++
            ([.label programLabels.lweRest] ++ (wpRest programLabels ++ contK))))
          (pinBitTest hframeQ.1) (by
            show evalExpr bitTest yQ = 0
            rw [hbitQ]
            rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ (n - 1)) with h | h
            · rw [h]
              rfl
            · exact absurd h hbit) findLweBitsK)⟩
      · show loadWord yQ.memory T2 = W (bb ^ (w / 2 ^ (n - 1)) % m)
        have hde0 : w / 2 ^ (n - 1) = 2 * (w / 2 ^ n) := by omega
        rw [hQload, hsqm, hde0]
  have hexit : ∀ y3 : EvmState,
      (WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y3.memory Icell = W i0 ∧
        loadWord y3.memory Wcell = W w ∧
        loadWord y3.memory Jcell = W 0 ∧ 0 ≤ 7 ∧
        loadWord y3.memory T2 = W (bytesToNatPadded calldata bo bs ^ (w / 2 ^ 0) % m)) →
      (WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y3.memory Icell = W i0 ∧
        loadWord y3.memory T2 = W (bytesToNatPadded calldata bo bs ^ w % m)) ∧
        ASteps programAsm ⟨wpBitsOpen programLabels contK, [], y3⟩
          ⟨wpRest programLabels ++ contK, [], y3⟩ := by
    intro y3 ⟨hf3, hT0y, hT1y, hIy, hWy, hJy, _, hT2y⟩
    rw [Nat.pow_zero, Nat.div_one, ← hbbdef] at hT2y
    rw [← hbbdef] at hT1y
    refine ⟨⟨hf3, hT0y, hT1y, hIy, hT2y⟩, ?_⟩
    exact jumpIfZ_taken (model := localModel) (prog := programAsm)
      (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
        (store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
        (jumpIfZ bitTest programLabels.lweBits ++
        (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
        ([.jump programLabels.lweBits] ++
        ([.label programLabels.lweRest] ++ (wpRest programLabels ++ contK)))))))
      (pinLoad (c := Jcell) (by decide) hf3) (by
        show loadWord y3.memory Jcell = 0
        rw [hJy]
        rfl) findLweRestK
  have hrun := loop_counted (model := localModel) (prog := programAsm)
      (top := wpBitsOpen programLabels contK) (σ := [])
      (c' := wpRest programLabels ++ contK)
      (Inv := fun y3 n => WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bb % m) ∧
        loadWord y3.memory Icell = W i0 ∧
        loadWord y3.memory Wcell = W w ∧
        loadWord y3.memory Jcell = W n ∧ n ≤ 7 ∧
        loadWord y3.memory T2 = W (bb ^ (w / 2 ^ n) % m))
      (P := fun y3 => WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y3.memory Icell = W i0 ∧
        loadWord y3.memory T2 = W (bytesToNatPadded calldata bo bs ^ w % m))
      hround hexit ⟨hfy, hT0, hT1, hI, hW, hJ, hn0le, hT2⟩
  obtain ⟨yst', hP, hsteps⟩ := hrun
  obtain ⟨hf', hT0', hT1', hI', hT2'⟩ := hP
  refine ⟨yst', ⟨hf', hT0', hT1', hI', hT2'⟩, hsteps⟩

set_option maxHeartbeats 10000000 in
/-- The found-exponent path: from `lwInit` (first nonzero exponent byte `w`
at index `i0` in `Wcell`, reduced base in `T1`) through the top-bit scan and
the bit loop, to `lweRest` with `T2 = W (b ^ w % m)`. -/
theorem found_to_rest {calldata : ByteArray} {bs es ms bo eo mo m w i0 : Nat}
    {y : EvmState}
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m) (hm0 : 0 < m) (hm256 : m < 2 ^ 256)
    (hT1 : loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m))
    (hI : loadWord y.memory Icell = W i0)
    (hW : loadWord y.memory Wcell = W w) (hw0 : w ≠ 0) (hw256 : w < 256) :
    ∃ y' : EvmState,
      (WPState y' calldata bs es ms bo eo mo ∧
        loadWord y'.memory T0 = W m ∧
        loadWord y'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y'.memory Icell = W i0 ∧
        loadWord y'.memory T2 = W (bytesToNatPadded calldata bo bs ^ w % m)) ∧
      ASteps programAsm ⟨wpLwInitOpen programLabels contK, [], y⟩
        ⟨wpRest programLabels ++ contK, [], y'⟩ := by
  -- Jcell := 7, then the label
  have hs1 : ASteps programAsm ⟨wpLwInitOpen programLabels contK, [], y⟩
      ⟨[.label programLabels.lweTop] ++ (wpTopBit programLabels ++ contK), [],
        { y with memory := storeWord y.memory Jcell (W 7) }⟩ :=
    storeW (c := Jcell) (yst := y) (exprOK_imm 7) (by decide) hfy.1
      (rfl : evalExpr (Expr.imm 7) y = W 7)
  have hframeJ := WPState_store1 (c := Jcell) (v := W 7) hfy hT0 (by decide)
  -- the top-bit scan
  have htop : ∀ (jt : Nat) {y2 : EvmState},
      (WPState y2 calldata bs es ms bo eo mo ∧
        loadWord y2.memory T0 = W m ∧
        loadWord y2.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y2.memory Icell = W i0 ∧
        loadWord y2.memory Wcell = W w ∧
        loadWord y2.memory Jcell = W jt ∧ w ≠ 0 ∧ w < 2 ^ (jt + 1) ∧ jt ≤ 7) →
      ∃ y3 jt', (WPState y3 calldata bs es ms bo eo mo ∧
          loadWord y3.memory T0 = W m ∧
          loadWord y3.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
          loadWord y3.memory Icell = W i0 ∧
          loadWord y3.memory Wcell = W w ∧
          loadWord y3.memory Jcell = W jt' ∧
          (w / 2 ^ jt') % 2 = 1 ∧ w < 2 ^ (jt' + 1) ∧ jt' ≤ 7) ∧
        ASteps programAsm ⟨wpTopBitOpen programLabels contK, [], y2⟩
          ⟨wpBitsInit programLabels ++ contK, [], y3⟩ := by
    intro jt
    induction jt using Nat.strong_induction_on with
    | _ jt ih =>
      intro y2 ⟨hf2, hT0y, hT1y, hIy, hWy, hJy, hw0y, hwlt, hle⟩
      by_cases hbit : (w / 2 ^ jt) % 2 = 1
      · refine ⟨y2, jt, ⟨hf2, hT0y, hT1y, hIy, hWy, hJy, hbit, hwlt, hle⟩, ?_⟩
        exact jumpIfNz_taken (model := localModel) (prog := programAsm)
          (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
            ([.jump programLabels.lweTop] ++ ([.label programLabels.lweBitsInit] ++
            (wpBitsInit programLabels ++ contK))))
          (pinBitTest hf2) (by
            show evalExpr bitTest y2 ≠ 0
            have hdv := evalExpr_bitTest hWy hJy (lt256_of_lt hw256)
              (lt256_of_lt (by omega))
            rw [hdv, hbit]
            exact W_ne_zero one_ne_zero (by norm_num)) findLweBitsInitK
      · -- bit clear: decrement and recurse
        have hbit0 : (w / 2 ^ jt) % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ jt) with h | h
          · exact h
          · omega
        have hjt0 : 0 < jt := by
          by_cases hz : jt = 0
          · rw [hz] at hbit0 hwlt
            norm_num at hwlt
            omega
          · omega
        have hdpow : 2 ^ (jt + 1) = 2 ^ jt * 2 := Nat.pow_succ 2 jt
        rw [hdpow] at hwlt
        have hd0 : w / 2 ^ jt = 0 := by
          rcases Nat.eq_zero_or_pos (w / 2 ^ jt) with h | h
          · exact h
          · exfalso
            have hd2 := (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))).mpr
              (show w < 2 * 2 ^ jt by omega)
            have heq : w / 2 ^ jt = 1 := by omega
            rw [heq] at hbit0
            omega
        have hval : evalExpr (.bin .sub (.load Jcell) (.imm 1)) y2 = W (jt - 1) :=
          evalExpr_jdec hJy hjt0 (lt256_of_lt (by omega))
        have hs : ASteps programAsm ⟨wpTopBitOpen programLabels contK, [], y2⟩
            ⟨[.jump programLabels.lweTop] ++ ([.label programLabels.lweBitsInit] ++
              (wpBitsInit programLabels ++ contK)), [],
              { y2 with memory := storeWord y2.memory Jcell (W (jt - 1)) }⟩ :=
          (jumpIfNz_fall (model := localModel) (prog := programAsm)
            (pinBitTest hf2) (by
              show evalExpr bitTest y2 = 0
              have hdv := evalExpr_bitTest hWy hJy (lt256_of_lt hw256)
                (lt256_of_lt (by omega))
              rw [hdv, hbit0]
              rfl)).trans
          (storeW (c := Jcell) (yst := y2)
            (by
              show binOK .sub = true ∧ exprOK (Expr.load Jcell) y2 ∧
                exprOK (Expr.imm 1) y2
              exact ⟨rfl, pinLoad (by decide) hf2, trivial⟩)
            (by decide) hf2.1 hval)
        have hframe' := WPState_store1 (c := Jcell) (v := W (jt - 1)) hf2 hT0y
          (by decide)
        have hJload : loadWord (storeWord y2.memory Jcell (W (jt - 1))) Jcell
            = W (jt - 1) := by
          show loadWord (storeWord y2.memory Jcell (W (jt - 1))) Jcell = W (jt - 1)
          rw [loadWord_storeWord]
        have hwlt' : w < 2 ^ (jt - 1 + 1) := by
          rw [show jt - 1 + 1 = jt from by omega]
          rcases Nat.div_eq_zero_iff.mp hd0 with h1 | h2
          · exact absurd h1 (by omega)
          · exact h2
        obtain ⟨y3, _, hinv3, hsteps3⟩ := ih (jt - 1) (by omega)
          (y2 := { y2 with memory := storeWord y2.memory Jcell (W (jt - 1)) })
          ⟨hframe'.1, hframe'.2, hT1y, hIy, hWy, hJload, hw0y, hwlt', by omega⟩
        exact ⟨y3, _, hinv3, (hs.trans (jumpTo findLweTopOpenK)).trans hsteps3⟩
  obtain ⟨y2, jt', hinv2, hsteps2⟩ := htop (jt := 7)
    (y2 := { y with memory := storeWord y.memory Jcell (W 7) })
    ⟨hframeJ.1, hframeJ.2, hT1, hI, hW, (by
        show loadWord (storeWord y.memory Jcell (W 7)) Jcell = W 7
        rw [loadWord_storeWord]), hw0, (by
        rw [show (2:Nat) ^ (7 + 1) = 256 from by norm_num]; omega), by omega⟩
  -- wpBitsInit: T2 := T1
  have hsq : ASteps programAsm ⟨wpBitsInitOpen programLabels contK, [], y2⟩
      ⟨[.label programLabels.lweBits] ++ (wpBits programLabels ++ contK), [],
        { y2 with memory := storeWord y2.memory T2 (W (bytesToNatPadded calldata bo bs % m)) }⟩ :=
    storeW (c := T2) (yst := y2) (pinLoad (c := T1) (by decide) hinv2.1)
      (by decide) hinv2.1.1 (by
        show evalExpr (Expr.load T1) y2 = W (bytesToNatPadded calldata bo bs % m)
        rw [show evalExpr (Expr.load T1) y2 = loadWord y2.memory T1 from rfl]
        exact hinv2.2.2.1)
  have hframeT2 := WPState_store1 (c := T2)
    (v := W (bytesToNatPadded calldata bo bs % m)) hinv2.1 hinv2.2.1 (by decide)
  have hT2load : loadWord (storeWord y2.memory T2 (W (bytesToNatPadded calldata bo bs % m))) T2
      = W (bytesToNatPadded calldata bo bs % m) := by
    show loadWord (storeWord y2.memory T2 (W (bytesToNatPadded calldata bo bs % m))) T2 = _
    rw [loadWord_storeWord]
  -- at the top bit, w / 2 ^ jt' = 1
  obtain ⟨hfJ', hT0'', hT1'', hI'', hW'', hJ'', hbit'', hwlt'', hle'⟩ := hinv2
  have hwtop : w / 2 ^ jt' = 1 := by
    have hpos : (0:Nat) < 2 ^ jt' := Nat.pow_pos (by norm_num)
    rw [show 2 ^ (jt' + 1) = 2 ^ jt' * 2 from Nat.pow_succ 2 jt'] at hwlt''
    have hlt2 : w / 2 ^ jt' < 2 :=
      (Nat.div_lt_iff_lt_mul hpos).mpr (by omega : w < 2 * 2 ^ jt')
    rcases Nat.eq_zero_or_pos (w / 2 ^ jt') with h | h
    · rw [h, Nat.zero_mod] at hbit''
      omega
    · omega
  have hbl := bitsLoop_correct (calldata := calldata) (bs := bs) (es := es) (ms := ms)
      (bo := bo) (eo := eo) (mo := mo) (m := m) (w := w) (i0 := i0)
      hm0 hm256 hw256 hframeT2.1 hframeT2.2
      (by show loadWord (storeWord y2.memory T2 (W (bytesToNatPadded calldata bo bs % m))) T1 = W (bytesToNatPadded calldata bo bs % m)
          rw [loadCell_storeCell (c := T2) (q := T1) (by decide)]
          exact hT1'')
      (by show loadWord (storeWord y2.memory T2 (W (bytesToNatPadded calldata bo bs % m))) Icell = W i0
          rw [loadCell_storeCell (c := T2) (q := Icell) (by decide)]
          exact hI'')
      (by show loadWord (storeWord y2.memory T2 (W (bytesToNatPadded calldata bo bs % m))) Wcell = W w
          rw [loadCell_storeCell (c := T2) (q := Wcell) (by decide)]
          exact hW'')
      hJ'' hle' (by
        show loadWord (storeWord y2.memory T2 (W (bytesToNatPadded calldata bo bs % m))) T2
          = W (bytesToNatPadded calldata bo bs ^ (w / 2 ^ jt') % m)
        rw [loadWord_storeWord, hwtop, Nat.pow_one])
  obtain ⟨y4, ⟨hf4, hT04, hT14, hI4, hT24⟩, hsteps4⟩ := hbl
  refine ⟨y4, ⟨hf4, hT04, hT14, hI4, hT24⟩, ?_⟩
  show ASteps programAsm ⟨wpLwInitOpen programLabels contK, [], y⟩
      ⟨wpRest programLabels ++ contK, [], y4⟩
  exact ((hs1.trans (labelStep programLabels.lweTop)).trans
    (((hsteps2.trans hsq).trans (labelStep programLabels.lweBits)).trans hsteps4))

theorem findLweByteBitsK :
    findLabel programLabels.lweByteBits programAsm =
      some (wpByteBits programLabels ++ contK) := by
  rw [show contK = secBigPath programLabels ++ progTail from contK_def.symm]
  exact findLweByteBits

set_option maxHeartbeats 10000000 in
/-- The inner byte-bits loop: from `.label lweByteBits` with `Jcell = W n`
(`n ≤ 8`), byte `wb` in `Wcell`, and `T2 = W (b ^ (X * 2^(8-n) + wb / 2^n)
% m)`, to `lweNext` with `T2 = W (b ^ (X * 256 + wb) % m)`. -/
theorem byteBitsLoop {calldata : ByteArray} {bs es ms bo eo mo m wb : Nat}
    {y : EvmState} {X iv : Nat}
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256) (hwb256 : wb < 256)
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m)
    (hT1 : loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m))
    (hW : loadWord y.memory Wcell = W wb)
    (hJ : loadWord y.memory Jcell = W n0) (hn0le : n0 ≤ 8)
    (hI : loadWord y.memory Icell = W iv)
    (hT2 : loadWord y.memory T2
      = W (bytesToNatPadded calldata bo bs ^ (X * 2 ^ (8 - n0) + wb / 2 ^ n0) % m)) :
    ∃ y' : EvmState,
      (WPState y' calldata bs es ms bo eo mo ∧
        loadWord y'.memory T0 = W m ∧
        loadWord y'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y'.memory Icell = W iv ∧
        loadWord y'.memory T2
          = W (bytesToNatPadded calldata bo bs ^ (X * 2 ^ (8 - 0) + wb / 2 ^ 0) % m)) ∧
      ASteps programAsm ⟨wpByteBitsOpen programLabels contK, [], y⟩
        ⟨wpNextOpen programLabels contK, [], y'⟩ := by
  set bb : Nat := bytesToNatPadded calldata bo bs with hbbdef
  have hbn : bb % m < 2 ^ 256 := Nat.lt_trans (Nat.mod_lt _ hm0) hm256
  have hround : ∀ {n : Nat} {y3 : EvmState}, 0 < n →
      (WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bb % m) ∧
        loadWord y3.memory Wcell = W wb ∧
        loadWord y3.memory Jcell = W n ∧ n ≤ 8 ∧
        loadWord y3.memory Icell = W iv ∧
        loadWord y3.memory T2 = W (bb ^ (X * 2 ^ (8 - n) + wb / 2 ^ n) % m)) →
      (∃ y4, (WPState y4 calldata bs es ms bo eo mo ∧
        loadWord y4.memory T0 = W m ∧
        loadWord y4.memory T1 = W (bb % m) ∧
        loadWord y4.memory Wcell = W wb ∧
        loadWord y4.memory Jcell = W (n - 1) ∧ n - 1 ≤ 8 ∧
        loadWord y4.memory Icell = W iv ∧
        loadWord y4.memory T2 = W (bb ^ (X * 2 ^ (8 - (n - 1)) + wb / 2 ^ (n - 1)) % m)) ∧
        ASteps programAsm ⟨wpByteBitsOpen programLabels contK, [], y3⟩
          ⟨wpByteBitsOpen programLabels contK, [], y4⟩) ∨
      ((WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bb % m) ∧
        loadWord y3.memory Icell = W iv ∧
        loadWord y3.memory T2 = W (bb ^ (X * 2 ^ (8 - 0) + wb / 2 ^ 0) % m)) ∧
        ASteps programAsm ⟨wpByteBitsOpen programLabels contK, [], y3⟩
          ⟨wpNextOpen programLabels contK, [], y3⟩) := by
    intro n y3 hn ⟨hf3, hT0y, hT1y, hWy, hJy, hnle, hIy2, hT2y⟩
    left
    set xq : Nat := bb ^ (X * 2 ^ (8 - n) + wb / 2 ^ n) % m with hxq
    -- fall through the Jcell test, decrement
    set yA : EvmState := { y3 with memory := storeWord y3.memory Jcell (W (n - 1)) } with hyA
    have hsJ : ASteps programAsm ⟨wpByteBitsOpen programLabels contK, [], y3⟩
        ⟨store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
          (jumpIfZ bitTest programLabels.lweByteBits ++
          (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
          ([.jump programLabels.lweByteBits] ++
          ([.label programLabels.lweNext] ++ (wpNextOpen programLabels contK))))), [], yA⟩ :=
      (jumpIfZ_fall (model := localModel) (prog := programAsm)
        (pinLoad (c := Jcell) (by decide) hf3) (by
          show loadWord y3.memory Jcell ≠ 0
          rw [hJy]
          exact W_ne_zero (by omega) (lt256_of_lt (by omega)))).trans
      (storeW (c := Jcell) (yst := y3)
        (by
          show binOK .sub = true ∧ exprOK (Expr.load Jcell) y3 ∧ exprOK (Expr.imm 1) y3
          exact ⟨rfl, pinLoad (by decide) hf3, trivial⟩)
        (by decide) hf3.1 (evalExpr_jdec hJy hn (lt256_of_lt (by omega))))
    have hframeA : WPState yA calldata bs es ms bo eo mo ∧ loadWord yA.memory T0 = W m :=
      WPState_store1 (c := Jcell) (v := W (n - 1)) hf3 hT0y (by decide)
    have hJA : loadWord yA.memory Jcell = W (n - 1) := by
      show loadWord (storeWord y3.memory Jcell (W (n - 1))) Jcell = W (n - 1)
      rw [loadWord_storeWord]
    have hTA : loadWord yA.memory T2 = W xq := by
      show loadWord (storeWord y3.memory Jcell (W (n - 1))) T2 = W xq
      rw [loadCell_storeCell (c := Jcell) (q := T2) (by decide)]
      exact hT2y
    -- the square
    set yQ : EvmState := { yA with memory := storeWord yA.memory T2 (W (xq * xq % m)) } with hyQ
    have hsq : evalExpr (.ter .mulmod (.load T2) (.load T2) (.load T0)) yA
        = W (xq * xq % m) :=
      evalExpr_sq (m := m) (x := xq) hTA hframeA.2 hm0 hm256
        (Nat.lt_trans (Nat.mod_lt _ hm0) hm256)
    have hsQ : ASteps programAsm ⟨store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
          (jumpIfZ bitTest programLabels.lweByteBits ++
          (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
          ([.jump programLabels.lweByteBits] ++
          ([.label programLabels.lweNext] ++ (wpNextOpen programLabels contK))))), [], yA⟩
        ⟨jumpIfZ bitTest programLabels.lweByteBits ++
          (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
          ([.jump programLabels.lweByteBits] ++
          ([.label programLabels.lweNext] ++ (wpNextOpen programLabels contK)))), [], yQ⟩ :=
      storeW (c := T2) (yst := yA)
        (by
          show terOK .mulmod = true ∧ exprOK (Expr.load T2) _
              ∧ exprOK (Expr.load T2) _ ∧ exprOK (Expr.load T0) _
          exact ⟨rfl, pinLoad (by decide) hframeA.1, pinLoad (by decide) hframeA.1,
            pinLoad (by decide) hframeA.1⟩)
        (by decide) hframeA.1.1 hsq
    have hframeQ : WPState yQ calldata bs es ms bo eo mo ∧ loadWord yQ.memory T0 = W m :=
      WPState_store1 (c := T2) (v := W (xq * xq % m)) hframeA.1 hframeA.2 (by decide)
    have hQload : loadWord yQ.memory T2 = W (xq * xq % m) := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 = _
      rw [loadWord_storeWord]
    have hWQ : loadWord yQ.memory Wcell = W wb := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) Wcell = _
      rw [loadCell_storeCell (c := T2) (q := Wcell) (by decide),
        loadCell_storeCell (c := Jcell) (q := Wcell) (by decide)]
      exact hWy
    have hJQ : loadWord yQ.memory Jcell = W (n - 1) := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) Jcell = _
      rw [loadCell_storeCell (c := T2) (q := Jcell) (by decide)]
      exact hJA
    have hT1Q : loadWord yQ.memory T1 = W (bb % m) := by
      show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T1 = _
      rw [loadCell_storeCell (c := T2) (q := T1) (by decide),
        loadCell_storeCell (c := Jcell) (q := T1) (by decide)]
      exact hT1y
    have hbitQ : evalExpr bitTest yQ = W ((wb / 2 ^ (n - 1)) % 2) :=
      evalExpr_bitTest hWQ hJQ (lt256_of_lt hwb256) (lt256_of_lt (by omega))
    have hbt := bit_step X wb n hn hnle
    have hsqm : xq * xq % m = bb ^ (2 * (X * 2 ^ (8 - n) + wb / 2 ^ n)) % m :=
      sq_mod (b := bb) (E := X * 2 ^ (8 - n) + wb / 2 ^ n) (m := m) (x := xq) rfl
    by_cases hbit : (wb / 2 ^ (n - 1)) % 2 = 1
    · -- multiply by the base, then loop
      set yM : EvmState := { yQ with memory := storeWord yQ.memory T2 (W ((xq * xq % m * (bb % m)) % m)) } with hyM
      have hmul : evalExpr (.ter .mulmod (.load T2) (.load T1) (.load T0)) yQ
          = W ((xq * xq % m * (bb % m)) % m) :=
        evalExpr_mulbase (m := m) (x := xq * xq % m) (t := bb % m)
          hQload hT1Q hframeQ.2 hm0 hm256
          (Nat.lt_trans (Nat.mod_lt _ hm0) hm256) hbn
      have hsM : ASteps programAsm ⟨jumpIfZ bitTest programLabels.lweByteBits ++
            (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
            ([.jump programLabels.lweByteBits] ++
            ([.label programLabels.lweNext] ++ (wpNextOpen programLabels contK)))), [], yQ⟩
            ⟨[.jump programLabels.lweByteBits] ++
            ([.label programLabels.lweNext] ++ (wpNextOpen programLabels contK)), [], yM⟩ :=
        (jumpIfZ_fall (model := localModel) (prog := programAsm)
          (pinBitTest hframeQ.1) (by
            show evalExpr bitTest yQ ≠ 0
            rw [hbitQ, hbit]
            exact W_ne_zero one_ne_zero (by norm_num))).trans
        (storeW (c := T2) (yst := yQ)
          (by
            show terOK .mulmod = true ∧ exprOK (Expr.load T2) _
                ∧ exprOK (Expr.load T1) _ ∧ exprOK (Expr.load T0) _
            exact ⟨rfl, pinLoad (by decide) hframeQ.1, pinLoad (by decide) hframeQ.1,
              pinLoad (by decide) hframeQ.1⟩)
          (by decide) hframeQ.1.1 hmul)
      have hframeM : WPState yM calldata bs es ms bo eo mo ∧ loadWord yM.memory T0 = W m :=
        WPState_store1 (c := T2) (v := W ((xq * xq % m * (bb % m)) % m))
          hframeQ.1 hframeQ.2 (by decide)
      have hMload : loadWord yM.memory T2 = W ((xq * xq % m * (bb % m)) % m) := by
        show loadWord (storeWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 (W ((xq * xq % m * (bb % m)) % m))) T2 = _
        rw [loadWord_storeWord]
      have hWM : loadWord yM.memory Wcell = W wb := by
        show loadWord (storeWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 (W ((xq * xq % m * (bb % m)) % m))) Wcell = _
        rw [loadCell_storeCell (c := T2) (q := Wcell) (by decide),
          loadCell_storeCell (c := T2) (q := Wcell) (by decide),
          loadCell_storeCell (c := Jcell) (q := Wcell) (by decide)]
        exact hWy
      have hJM : loadWord yM.memory Jcell = W (n - 1) := by
        show loadWord (storeWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 (W ((xq * xq % m * (bb % m)) % m))) Jcell = _
        rw [loadCell_storeCell (c := T2) (q := Jcell) (by decide),
          loadCell_storeCell (c := T2) (q := Jcell) (by decide)]
        exact hJA
      have hIM : loadWord yM.memory Icell = W iv := by
        show loadWord (storeWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) T2 (W ((xq * xq % m * (bb % m)) % m))) Icell = _
        rw [loadCell_storeCell (c := T2) (q := Icell) (by decide),
          loadCell_storeCell (c := T2) (q := Icell) (by decide),
          loadCell_storeCell (c := Jcell) (q := Icell) (by decide)]
        exact hIy2
      refine ⟨yM, ⟨hframeM.1, hframeM.2, hT1y, hWM, hJM, by omega, hIM, ?_⟩, ?_⟩
      · show loadWord yM.memory T2
          = W (bb ^ (X * 2 ^ (8 - (n - 1)) + wb / 2 ^ (n - 1)) % m)
        rw [hMload]
        have hmulm : (xq * xq % m * (bb % m)) % m
            = bb ^ (2 * (X * 2 ^ (8 - n) + wb / 2 ^ n) + 1) % m :=
          mulbase_mod (b := bb) (E := 2 * (X * 2 ^ (8 - n) + wb / 2 ^ n)) (m := m)
            (x := xq * xq % m) (t := bb % m) hsqm rfl
        rw [hmulm, show 2 * (X * 2 ^ (8 - n) + wb / 2 ^ n) + 1
            = X * 2 ^ (8 - (n - 1)) + wb / 2 ^ (n - 1) from by rw [← hbt]; omega]
      · exact ((hsJ.trans hsQ).trans hsM).trans (jumpTo findLweByteBitsOpenK)
    · -- bit clear: skip the multiply, loop
      have hIQ : loadWord yQ.memory Icell = W iv := by
        show loadWord (storeWord (storeWord y3.memory Jcell (W (n - 1))) T2 (W (xq * xq % m))) Icell = _
        rw [loadCell_storeCell (c := T2) (q := Icell) (by decide),
          loadCell_storeCell (c := Jcell) (q := Icell) (by decide)]
        exact hIy2
      refine ⟨yQ, ⟨hframeQ.1, hframeQ.2, hT1y, hWy, hJQ, by omega, hIQ, ?_⟩, ?_⟩
      · show loadWord yQ.memory T2
          = W (bb ^ (X * 2 ^ (8 - (n - 1)) + wb / 2 ^ (n - 1)) % m)
        rw [hQload, hsqm, show 2 * (X * 2 ^ (8 - n) + wb / 2 ^ n)
            = X * 2 ^ (8 - (n - 1)) + wb / 2 ^ (n - 1) from by rw [← hbt]; omega]
      · exact (hsJ.trans hsQ).trans (jumpIfZ_taken (model := localModel) (prog := programAsm)
          (k := store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
            ([.jump programLabels.lweByteBits] ++
            ([.label programLabels.lweNext] ++ (wpNextOpen programLabels contK))))
          (pinBitTest hframeQ.1) (by
            show evalExpr bitTest yQ = 0
            rw [hbitQ]
            rcases Nat.mod_two_eq_zero_or_one (wb / 2 ^ (n - 1)) with h | h
            · rw [h]
              rfl
            · exact absurd h hbit) findLweByteBitsK)
  have hexit : ∀ y3 : EvmState,
      (WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y3.memory Wcell = W wb ∧
        loadWord y3.memory Jcell = W 0 ∧ 0 ≤ 8 ∧
        loadWord y3.memory Icell = W iv ∧
        loadWord y3.memory T2 = W (bytesToNatPadded calldata bo bs ^ (X * 2 ^ (8 - 0) + wb / 2 ^ 0) % m)) →
      (WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y3.memory Icell = W iv ∧
        loadWord y3.memory T2
          = W (bytesToNatPadded calldata bo bs ^ (X * 2 ^ (8 - 0) + wb / 2 ^ 0) % m)) ∧
        ASteps programAsm ⟨wpByteBitsOpen programLabels contK, [], y3⟩
          ⟨wpNextOpen programLabels contK, [], y3⟩ := by
    intro y3 ⟨hf3, hT0y, hT1y, _, hJy, _, hIy2, hT2y⟩
    exact ⟨⟨hf3, hT0y, hT1y, hIy2, hT2y⟩,
      jumpIfZ_taken (model := localModel) (prog := programAsm)
        (k := store Jcell (.bin .sub (.load Jcell) (.imm 1)) ++
          (store T2 (.ter .mulmod (.load T2) (.load T2) (.load T0)) ++
          (jumpIfZ bitTest programLabels.lweByteBits ++
          (store T2 (.ter .mulmod (.load T2) (.load T1) (.load T0)) ++
          ([.jump programLabels.lweByteBits] ++
          ([.label programLabels.lweNext] ++ (wpNextOpen programLabels contK)))))))
        (pinLoad (c := Jcell) (by decide) hf3) (by
          show loadWord y3.memory Jcell = 0
          rw [hJy]
          rfl) findLweNextK⟩
  rw [hbbdef] at hT1 hT2 ⊢
  obtain ⟨yst', hP, hsteps⟩ :=
    loop_counted (model := localModel) (prog := programAsm)
      (top := wpByteBitsOpen programLabels contK) (σ := [])
      (c' := wpNextOpen programLabels contK)
      (Inv := fun y3 n => WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bb % m) ∧
        loadWord y3.memory Wcell = W wb ∧
        loadWord y3.memory Jcell = W n ∧ n ≤ 8 ∧
        loadWord y3.memory Icell = W iv ∧
        loadWord y3.memory T2 = W (bb ^ (X * 2 ^ (8 - n) + wb / 2 ^ n) % m))
      (P := fun y3 => WPState y3 calldata bs es ms bo eo mo ∧
        loadWord y3.memory T0 = W m ∧
        loadWord y3.memory T1 = W (bb % m) ∧
        loadWord y3.memory Icell = W iv ∧
        loadWord y3.memory T2 = W (bb ^ (X * 2 ^ (8 - 0) + wb / 2 ^ 0) % m))
      hround hexit ⟨hfy, hT0, hT1, hW, hJ, hn0le, hI, hT2⟩
  obtain ⟨hf', hT0', hT1', hIcell', hT2'⟩ := hP
  rw [hbbdef] at hT1' hT2'
  exact ⟨yst', ⟨hf', hT0', hT1', hIcell', hT2'⟩, hsteps⟩


@[irreducible] def bytesInv (calldata : ByteArray)
    (bs es ms bo eo mo bb m : Nat) (y : EvmState) (n : Nat) : Prop :=
  WPState y calldata bs es ms bo eo mo ∧
    loadWord y.memory T0 = W m ∧
    loadWord y.memory T1 = W (bb % m) ∧
    loadWord y.memory Icell = W (es - n) ∧ n ≤ es ∧
    loadWord y.memory T2 = W (bb ^ bytesToNatPadded calldata eo (es - n) % m)

theorem bytesInv_mk {calldata : ByteArray}
    {bs es ms bo eo mo bb m : Nat} {y : EvmState} {n : Nat}
    (h1 : WPState y calldata bs es ms bo eo mo)
    (h2 : loadWord y.memory T0 = W m)
    (h3 : loadWord y.memory T1 = W (bb % m))
    (h4 : loadWord y.memory Icell = W (es - n))
    (h5 : n ≤ es)
    (h6 : loadWord y.memory T2 = W (bb ^ bytesToNatPadded calldata eo (es - n) % m)) :
    bytesInv calldata bs es ms bo eo mo bb m y n := by
  unfold bytesInv
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem bytesInv_elims {calldata : ByteArray}
    {bs es ms bo eo mo bb m : Nat} {y : EvmState} {n : Nat}
    (h : bytesInv calldata bs es ms bo eo mo bb m y n) :
    WPState y calldata bs es ms bo eo mo ∧
      loadWord y.memory T0 = W m ∧
      loadWord y.memory T1 = W (bb % m) ∧
      loadWord y.memory Icell = W (es - n) ∧ n ≤ es ∧
      loadWord y.memory T2 = W (bb ^ bytesToNatPadded calldata eo (es - n) % m) := by
  unfold bytesInv at h
  exact h

@[irreducible] def bytesPost (calldata : ByteArray)
    (bs es ms bo eo mo bb m : Nat) (y : EvmState) : Prop :=
  WPState y calldata bs es ms bo eo mo ∧
    loadWord y.memory T0 = W m ∧
    loadWord y.memory T1 = W (bb % m) ∧
    loadWord y.memory Icell = W es ∧
    loadWord y.memory T2 = W (bb ^ bytesToNatPadded calldata eo es % m)

theorem bytesPost_mk {calldata : ByteArray}
    {bs es ms bo eo mo bb m : Nat} {y : EvmState}
    (h1 : WPState y calldata bs es ms bo eo mo)
    (h2 : loadWord y.memory T0 = W m)
    (h3 : loadWord y.memory T1 = W (bb % m))
    (h4 : loadWord y.memory Icell = W es)
    (h6 : loadWord y.memory T2 = W (bb ^ bytesToNatPadded calldata eo es % m)) :
    bytesPost calldata bs es ms bo eo mo bb m y := by
  unfold bytesPost
  exact ⟨h1, h2, h3, h4, h6⟩

theorem bytesPost_elims {calldata : ByteArray}
    {bs es ms bo eo mo bb m : Nat} {y : EvmState}
    (h : bytesPost calldata bs es ms bo eo mo bb m y) :
    WPState y calldata bs es ms bo eo mo ∧
      loadWord y.memory T0 = W m ∧
      loadWord y.memory T1 = W (bb % m) ∧
      loadWord y.memory Icell = W es ∧
      loadWord y.memory T2 = W (bb ^ bytesToNatPadded calldata eo es % m) := by
  unfold bytesPost at h
  exact h

set_option maxHeartbeats 10000000 in
/-- The remaining-bytes loop: from `.label lweRest` (which increments
`Icell` past the seed byte) with `T2 = W (b ^ w % m)` at the seed's index,
iterate the byte-bits loop over the remaining exponent bytes, to `lweSer`
with `T2 = W (b ^ e % m)`. -/
theorem bytesPath {calldata : ByteArray} {bs es ms bo eo mo m i0 w : Nat}
    {y : EvmState}
    (hbs : bs ≤ 1024) (hes : es ≤ 1024) (hbo : bo = 96) (heo : eo = bo + bs)
    (hm0 : 0 < m) (hm256 : m < 2 ^ 256)
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m)
    (hT1 : loadWord y.memory T1 = W (bytesToNatPadded calldata bo bs % m))
    (hI : loadWord y.memory Icell = W i0)
    (hi0es : i0 < es)
    (hpfx : bytesToNatPadded calldata eo i0 = 0)
    (hbw : (byteFrom calldata.toList (eo + i0)).toNat = w)
    (hT2 : loadWord y.memory T2
      = W (bytesToNatPadded calldata bo bs ^ w % m)) :
    ∃ y' : EvmState,
      (WPState y' calldata bs es ms bo eo mo ∧
        loadWord y'.memory T0 = W m ∧
        loadWord y'.memory T1 = W (bytesToNatPadded calldata bo bs % m) ∧
        loadWord y'.memory T2
          = W (bytesToNatPadded calldata bo bs
              ^ bytesToNatPadded calldata eo es % m)) ∧
      ASteps programAsm ⟨wpRestOpen programLabels contK, [], y⟩
        ⟨wpSer programLabels ++ contK, [], y'⟩ := by
  set bb : Nat := bytesToNatPadded calldata bo bs with hbbdef
  have hbn : bb % m < 2 ^ 256 := Nat.lt_trans (Nat.mod_lt _ hm0) hm256
  have hseed : bytesToNatPadded calldata eo (i0 + 1) = w := by
    rw [bytesToNatPadded_succ, hpfx, Nat.zero_mul, Nat.zero_add, hbw]
  -- Icell := i0 + 1, then the label
  have hs1 : ASteps programAsm ⟨wpRestOpen programLabels contK, [], y⟩
      ⟨wpBytesOpen programLabels contK, [],
        { y with memory := storeWord y.memory Icell (W (i0 + 1)) }⟩ :=
    (storeW (c := Icell) (yst := y) (exprOK_add1 hfy) (by decide) hfy.1
      (evalExpr_add1 hI (by omega : i0 + 1 < 2 ^ 256))).trans
        (labelStep programLabels.lweBytes)
  have hframeI : WPState { y with memory := storeWord y.memory Icell (W (i0 + 1)) }
      calldata bs es ms bo eo mo ∧
      loadWord (storeWord y.memory Icell (W (i0 + 1))) T0 = W m :=
    WPState_store1 (c := Icell) (v := W (i0 + 1)) hfy hT0 (by decide)
  have hT1I : loadWord (storeWord y.memory Icell (W (i0 + 1))) T1 = W (bb % m) := by
    show loadWord (storeWord y.memory Icell (W (i0 + 1))) T1 = _
    rw [loadCell_storeCell (c := Icell) (q := T1) (by decide)]
    exact hT1
  have hT2I : loadWord (storeWord y.memory Icell (W (i0 + 1))) T2
      = W (bb ^ bytesToNatPadded calldata eo (i0 + 1) % m) := by
    show loadWord (storeWord y.memory Icell (W (i0 + 1))) T2 = _
    rw [loadCell_storeCell (c := Icell) (q := T2) (by decide), hseed]
    exact hT2
  -- the outer counted loop
  have hround : ∀ {n : Nat} {y3 : EvmState}, 0 < n →
      bytesInv calldata bs es ms bo eo mo bb m y3 n →
      (∃ y4, bytesInv calldata bs es ms bo eo mo bb m y4 (n - 1) ∧
        ASteps programAsm ⟨wpBytesOpen programLabels contK, [], y3⟩
          ⟨wpBytesOpen programLabels contK, [], y4⟩) ∨
      (bytesPost calldata bs es ms bo eo mo bb m y3 ∧
        ASteps programAsm ⟨wpBytesOpen programLabels contK, [], y3⟩
          ⟨wpSer programLabels ++ contK, [], y3⟩) := by
    intro n y3 hn hI3
    obtain ⟨hf3, hT0y, hT1y, hIy, hnle, hT2y⟩ := bytesInv_elims hI3
    left
    have hilt : es - n < es := by omega
    set i := es - n with hi
    set wb := (byteFrom calldata.toList (eo + i)).toNat with hwbd
    have hwb256 : wb < 256 := by
      have := (byteFrom calldata.toList (eo + i)).toNat_lt
      omega
    have hWval : evalExpr (cdbCell EO) y3 = W wb := by
      have haddr : (evalExpr (Expr.bin .add (Expr.load EO) (Expr.load Icell)) y3).toNat
          = eo + i := by
        show (loadWord y3.memory EO + loadWord y3.memory Icell).toNat = eo + i
        rw [hf3.EOw, hIy, W_add (by omega : eo + (es - n) < 2 ^ 256),
          toNat_W (by omega : eo + (es - n) < 2 ^ 256), ← hi]
      show evalExpr (Expr.cdb (Expr.bin .add (Expr.load EO) (Expr.load Icell))) y3 = _
      rw [evalExpr_cdb haddr, hf3.cd]
    -- fall the test, load the byte, Jcell := 8, then the label
    set yA : EvmState := { y3 with memory := storeWord (storeWord y3.memory Wcell (W wb)) Jcell (W 8) } with hyA
    have hsA : ASteps programAsm ⟨wpBytesOpen programLabels contK, [], y3⟩
        ⟨wpByteBitsOpen programLabels contK, [], yA⟩ :=
      ((jumpUnlessLt_fall (model := localModel) (prog := programAsm)
        (pinLoad (c := Icell) (by decide) hf3) (pinLoad (c := ES) (by decide) hf3)
        (by
          show (loadWord y3.memory Icell).ult (loadWord y3.memory ES) = true
          rw [hIy, hf3.ESw]
          exact W_ult (by omega : es - n < 2 ^ 256) (by omega : es < 2 ^ 256)
            hilt)).trans
      (storeW (c := Wcell) (yst := y3) (pinCdbCell (base := EO) (by decide) hf3)
        (by decide) hf3.1 hWval)).trans
      ((storeW (c := Jcell) (yst := { y3 with memory := storeWord y3.memory Wcell (W wb) })
        (exprOK_imm 8) (by decide)
        (WPState_store1 (c := Wcell) (v := W wb) hf3 hT0y (by decide)).1.1
        (rfl : evalExpr (Expr.imm 8) _ = W 8)).trans
      (labelStep programLabels.lweByteBits))
    have hframeA : WPState yA calldata bs es ms bo eo mo ∧ loadWord yA.memory T0 = W m :=
      WPState_store2 (c1 := Wcell) (c2 := Jcell) (v1 := W wb) (v2 := W 8) hf3 hT0y
        (by decide)
    have hT1A : loadWord yA.memory T1 = W (bb % m) := by
      show loadWord (storeWord (storeWord y3.memory Wcell (W wb)) Jcell (W 8)) T1 = _
      rw [loadCell_storeCell (c := Jcell) (q := T1) (by decide),
        loadCell_storeCell (c := Wcell) (q := T1) (by decide)]
      exact hT1y
    have hWA : loadWord yA.memory Wcell = W wb := by
      show loadWord (storeWord (storeWord y3.memory Wcell (W wb)) Jcell (W 8)) Wcell = _
      rw [loadCell_storeCell (c := Jcell) (q := Wcell) (by decide), loadWord_storeWord]
    have hJA : loadWord yA.memory Jcell = W 8 := by
      show loadWord (storeWord (storeWord y3.memory Wcell (W wb)) Jcell (W 8)) Jcell = _
      rw [loadWord_storeWord]
    have hT2A : loadWord yA.memory T2
        = W (bb ^ (bytesToNatPadded calldata eo i * 2 ^ (8 - 8) + wb / 2 ^ 8) % m) := by
      show loadWord (storeWord (storeWord y3.memory Wcell (W wb)) Jcell (W 8)) T2 = _
      rw [loadCell_storeCell (c := Jcell) (q := T2) (by decide),
        loadCell_storeCell (c := Wcell) (q := T2) (by decide),
        show 8 - 8 = 0 from rfl, Nat.pow_zero, Nat.mul_one,
        Nat.div_eq_of_lt (by
          rw [show (2:Nat) ^ 8 = 256 from by norm_num]
          exact hwb256),
        Nat.add_zero]
      exact hT2y
    -- the inner loop over the byte's bits
    obtain ⟨yB, ⟨hfB, hT0B, hT1B, hIB, hT2B⟩, hstepsB⟩ :=
      byteBitsLoop (calldata := calldata) (bs := bs) (es := es) (ms := ms)
        (bo := bo) (eo := eo) (mo := mo) (m := m) (wb := wb)
        (X := bytesToNatPadded calldata eo i) (iv := i)
        hm0 hm256 hwb256 hframeA.1 hframeA.2 hT1A hWA hJA (by decide : 8 ≤ 8) hIy hT2A
    -- Icell := i + 1, jump back to lweBytes
    set yC : EvmState := { yB with memory := storeWord yB.memory Icell (W (i + 1)) } with hyC
    have hsC : ASteps programAsm ⟨wpNextOpen programLabels contK, [], yB⟩
        ⟨wpBytesOpen programLabels contK, [], yC⟩ :=
      (storeW (c := Icell) (yst := yB) (exprOK_add1 hfB) (by decide) hfB.1
        (evalExpr_add1 hIB
          (Nat.lt_of_le_of_lt (show es - n + 1 ≤ 1024 by omega)
            (by norm_num : (1024:Nat) < 2 ^ 256)))).trans
      (jumpTo findLweBytesOpenK)
    have hframeC : WPState yC calldata bs es ms bo eo mo ∧ loadWord yC.memory T0 = W m :=
      WPState_store1 (c := Icell) (v := W (i + 1)) hfB hT0B (by decide)
    have hT1C : loadWord yC.memory T1 = W (bb % m) := by
      show loadWord (storeWord yB.memory Icell (W (i + 1))) T1 = _
      rw [loadCell_storeCell (c := Icell) (q := T1) (by decide)]
      exact hT1B
    have hT2C : loadWord yC.memory T2
        = W (bb ^ bytesToNatPadded calldata eo (i + 1) % m) := by
      show loadWord (storeWord yB.memory Icell (W (i + 1))) T2 = _
      rw [loadCell_storeCell (c := Icell) (q := T2) (by decide)]
      have hsucc : bytesToNatPadded calldata eo (i + 1)
          = bytesToNatPadded calldata eo i * 256 + wb :=
        bytesToNatPadded_succ calldata eo i
      rw [show (2:Nat) ^ (8 - 0) = 256 from by norm_num,
        show wb / (2:Nat) ^ 0 = wb from by rw [Nat.pow_zero, Nat.div_one]] at hT2B
      rw [hsucc]
      exact hT2B
    have hIES : i + 1 = es - (n - 1) := by omega
    refine ⟨yC, bytesInv_mk hframeC.1 hframeC.2 hT1C ?_ (by omega) ?_,
      (hsA.trans hstepsB).trans hsC⟩
    · show loadWord (storeWord yB.memory Icell (W (i + 1))) Icell = W (es - (n - 1))
      rw [loadWord_storeWord, ← hIES]
    · show loadWord yC.memory T2 = W (bb ^ bytesToNatPadded calldata eo (es - (n - 1)) % m)
      rw [← hIES]
      exact hT2C
  have hexit : ∀ y3 : EvmState,
      bytesInv calldata bs es ms bo eo mo bb m y3 0 →
      bytesPost calldata bs es ms bo eo mo bb m y3 ∧
        ASteps programAsm ⟨wpBytesOpen programLabels contK, [], y3⟩
          ⟨wpSer programLabels ++ contK, [], y3⟩ := by
    intro y3 hI3
    obtain ⟨hf3, hT0y, hT1y, hIy, _, hT2y⟩ := bytesInv_elims hI3
    refine ⟨bytesPost_mk hf3 hT0y hT1y ?_ hT2y, ?_⟩
    · exact hIy
    · have hnlt : ¬(evalExpr (Expr.load Icell) y3).ult (evalExpr (Expr.load ES) y3) := by
        show ¬ ((loadWord y3.memory Icell).ult (loadWord y3.memory ES) = true)
        rw [hIy, hf3.ESw]
        exact W_nult (by omega : es - 0 < 2 ^ 256) (by omega : es < 2 ^ 256)
          (Nat.le_of_eq (by rw [show es - 0 = es from rfl]))
      exact jumpUnlessLt_taken (model := localModel) (prog := programAsm)
        (pinLoad (c := Icell) (by decide) hf3) (pinLoad (c := ES) (by decide) hf3)
        hnlt findLweSerK
  rw [hbbdef] at hT1 hT2 ⊢
  have hI4 : loadWord (storeWord y.memory Icell (W (i0 + 1))) Icell
      = W (es - (es - (i0 + 1))) := by
    rw [loadWord_storeWord, show es - (es - (i0 + 1)) = i0 + 1 from by omega]
  have hT2I4 : loadWord (storeWord y.memory Icell (W (i0 + 1))) T2
      = W (bb ^ bytesToNatPadded calldata eo (es - (es - (i0 + 1))) % m) := by
    rw [show es - (es - (i0 + 1)) = i0 + 1 from by omega]
    exact hT2I
  have hnle0 : es - (i0 + 1) ≤ es := by omega
  obtain ⟨yst', hP, hsteps⟩ :=
    loop_counted (model := localModel) (prog := programAsm)
      (top := wpBytesOpen programLabels contK) (σ := [])
      (c' := wpSer programLabels ++ contK)
      (Inv := bytesInv calldata bs es ms bo eo mo bb m)
      (P := bytesPost calldata bs es ms bo eo mo bb m)
      hround hexit (n := es - (i0 + 1))
      (yst := { y with memory := storeWord y.memory Icell (W (i0 + 1)) })
      (bytesInv_mk hframeI.1 hframeI.2 hT1I hI4 hnle0 hT2I4)
  obtain ⟨hf', hT0', hT1', _, hT2'⟩ := bytesPost_elims hP
  rw [hbbdef] at hT1' hT2'
  refine ⟨yst', ⟨?_, ?_, ?_, ?_⟩, hs1.trans hsteps⟩
  · exact hf'
  · exact hT0'
  · exact hT1'
  · exact hT2' 

/-! ## Serialization -/

theorem le_two_pow_256 : (256 : Nat) ^ 32 ≤ 2 ^ 256 :=
  le_of_eq two_pow_256_eq.symm

/-- The value of the stored return word: no truncation, since the accumulator
is below `256 ^ ms`. -/
theorem serWord_toNat {r ms : Nat} (hms : ms ≤ 32) (hr : r < 256 ^ ms) :
    (W r <<< ((32 - ms) * 8)).toNat = r * 256 ^ (32 - ms) := by
  have hp8 : (2 : Nat) ^ ((32 - ms) * 8) = 256 ^ (32 - ms) := by
    rw [Nat.mul_comm, Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from by norm_num]
  have hmul : r * 2 ^ ((32 - ms) * 8) < 2 ^ 256 := by
    rw [hp8]
    calc r * 256 ^ (32 - ms) < 256 ^ ms * 256 ^ (32 - ms) := by
          have hpos : (0:Nat) < 256 ^ (32 - ms) := Nat.pow_pos (by norm_num)
          nlinarith [hpos]
      _ = 256 ^ (ms + (32 - ms)) := by rw [Nat.pow_add]
      _ = 256 ^ 32 := by congr 1; omega
      _ ≤ 2 ^ 256 := le_two_pow_256
  rw [W_shl_toNat_mul (lt_two_pow_256_of_lt_pow256 hms hr) hmul, hp8]

/-- The stored word's big-endian bytes are `natToBytes`'s. -/
theorem byteAt_serWord {r ms i : Nat} (hms : ms ≤ 32) (hr : r < 256 ^ ms)
    (hi : i < ms) :
    byteAt (W r <<< ((32 - ms) * 8)) (31 - i)
      = UInt8.ofNat (r / 256 ^ (ms - 1 - i) % 256) := by
  have hv := serWord_toNat hms hr
  show UInt8.ofNat ((W r <<< ((32 - ms) * 8) >>> (8 * (31 - i))).toNat) = _
  rw [BitVec.toNat_ushiftRight, hv, Nat.shiftRight_eq_div_pow]
  have hsplit : 8 * (31 - i) = (32 - ms) * 8 + (ms - 1 - i) * 8 := by omega
  have hp1 : (2: Nat) ^ ((32 - ms) * 8 + (ms - 1 - i) * 8)
      = 256 ^ (32 - ms) * 2 ^ ((ms - 1 - i) * 8) := by
    rw [Nat.mul_comm (32 - ms) 8, Nat.pow_add]
    norm_num [Nat.pow_mul]
  have hp2 : (2: Nat) ^ ((ms - 1 - i) * 8) = 256 ^ (ms - 1 - i) := by
    rw [Nat.mul_comm, Nat.pow_mul]
  rw [show 8 * (31 - i) = (32 - ms) * 8 + (ms - 1 - i) * 8 from by omega, hp1,
    Nat.mul_comm r (256 ^ (32 - ms)),
    Nat.mul_div_mul_left _ _ (Nat.pow_pos (by norm_num)), hp2]
  apply UInt8.toNat_inj.mp
  show (UInt8.ofNat (r / 256 ^ (ms - 1 - i))).toNat
      = (UInt8.ofNat (r / 256 ^ (ms - 1 - i) % 256)).toNat
  have h1 : (UInt8.ofNat (r / 256 ^ (ms - 1 - i))).toNat
      = r / 256 ^ (ms - 1 - i) % 256 := rfl
  have h2 : (UInt8.ofNat (r / 256 ^ (ms - 1 - i) % 256)).toNat
      = r / 256 ^ (ms - 1 - i) % 256 % 256 := rfl
  rw [h1, h2, Nat.mod_mod]

/-- The return window of the stored accumulator is the padded encoding. -/
theorem readBytes_serWord (mem : Nat → UInt8) (r ms : Nat)
    (hms : ms ≤ 32) (hr : r < 256 ^ ms) :
    readBytes (storeWord mem RET (W r <<< ((32 - ms) * 8))) RET ms
      = (natToBytes r ms).toList := by
  rw [readBytes_storeWord_self (v := W r <<< ((32 - ms) * 8)) hms]
  have hdata : (natToBytes r ms).data.size = ms := by
    show (EvmSemantics.Data.Bytes.natToBytesPadded r ms).size = ms
    exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size r ms
  have hlen : ((natToBytes r ms).toList).length = ms := by
    rw [ByteArray.toList_eq_data, Array.length_toList]; exact hdata
  refine List.ext_getElem
    (l₁ := (List.range ms).map (fun i => byteAt (W r <<< ((32 - ms) * 8)) (31 - i)))
    (l₂ := (natToBytes r ms).toList) ?_ ?_
  · rw [List.length_map, List.length_range, hlen]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    have hi : i < ms := by simpa [List.length_map, List.length_range] using h1
    rw [byteAt_serWord hms hr hi]
    have hget : (natToBytes r ms)[i]?.getD 0
        = UInt8.ofNat (r / 256 ^ (ms - 1 - i) % 256) :=
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD r ms i hi
    show UInt8.ofNat (r / 256 ^ (ms - 1 - i) % 256) = ((natToBytes r ms).toList)[i]'h2
    have hbridge : ((natToBytes r ms).toList)[i]'h2
        = (natToBytes r ms)[i]?.getD 0 := by
      have hopt : ((natToBytes r ms).toList)[i]? = (natToBytes r ms)[i]? := by
        rw [ByteArray.toList_eq_data, Array.getElem?_toList]
        rfl
      have h3 : i < (natToBytes r ms).size := by
        show i < (natToBytes r ms).data.size
        rw [ByteArray.toList_eq_data, Array.length_toList] at h2
        exact h2
      rw [getElem?_pos (natToBytes r ms) i h3] at hopt
      rw [List.getElem?_eq_getElem h2] at hopt
      rw [Option.some.injEq] at hopt
      rw [hopt, getElem?_pos (natToBytes r ms) i h3, Option.getD_some]
    rw [hbridge, hget]

/-- The serialization and halt: from `.label lweSer` with `T2 = W r` and
`r < 256 ^ ms`, store the shifted return word and `RET` it. -/
theorem serHalt {calldata : ByteArray} {bs es ms bo eo mo r : Nat}
    {y : EvmState}
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hms0 : 0 < ms) (hms32 : ms ≤ 32)
    (hT2 : loadWord y.memory T2 = W r) (hr : r < 256 ^ ms) :
    ∃ (b : AConf) (yst' : EvmState),
      ASteps programAsm ⟨wpSerOpen programLabels contK, [], y⟩ b ∧
      AHalt programAsm b yst' ∧
      yst'.halted = some (.ret, (natToBytes r ms).toList) := by
  have hv : evalExpr (.bin .shl (.bin .mul (.bin .sub (.imm 32) (.load MS))
      (.imm 8)) (.load T2)) y = (W r <<< ((32 - ms) * 8)) :=
    evalExpr_serShl hfy hT2 hms0 hms32
      (lt_two_pow_256_of_lt_pow256 hms32 hr)
  have hs1 : ASteps programAsm ⟨wpSerOpen programLabels contK, [], y⟩
      ⟨compileExpr (Expr.load MS) ++ (compileExpr (Expr.imm RET) ++
        ([.op .ret] ++ contK)), [],
        { y with memory := storeWord y.memory RET (W r <<< ((32 - ms) * 8)) }⟩ :=
    storeW2 (c := RET) (yst := y)
      (by
        show binOK .shl = true ∧
          (binOK .mul = true ∧
            (binOK .sub = true ∧ exprOK (Expr.imm 32) y ∧ exprOK (Expr.load MS) y) ∧
            exprOK (Expr.imm 8) y) ∧
          exprOK (Expr.load T2) y
        exact ⟨rfl, ⟨rfl, ⟨rfl, trivial, pinLoad (by decide) hfy⟩, trivial⟩,
          pinLoad (by decide) hfy⟩)
      (by decide) hfy.1 hv
  -- push the two RET arguments
  set yS : EvmState :=
    { y with memory := storeWord y.memory RET (W r <<< ((32 - ms) * 8)) }
  have hms : evalExpr (Expr.load MS) yS = W ms := by
    show loadWord yS.memory MS = W ms
    have hdisj : RET + 32 ≤ MS ∨ MS + 32 ≤ RET :=
      Or.inl (by unfold RET; decide)
    show loadWord (storeWord y.memory RET (W r <<< ((32 - ms) * 8))) MS = W ms
    rw [loadCell_storeCell hdisj]
    exact hfy.MSw
  have hokMS : exprOK (Expr.load MS) yS := by
    show MS < 2 ^ 256 ∧ MS + 32 ≤ 32 * yS.activeWords.toNat
    have haw : yS.activeWords.toNat = 250 := hfy.1
    rw [haw]
    constructor
    · unfold MS; norm_num
    · unfold MS; omega
  have hs2 : ASteps programAsm
      ⟨compileExpr (Expr.load MS) ++ (compileExpr (Expr.imm RET) ++
        ([.op .ret] ++ contK)), [], yS⟩
      ⟨.op .ret :: contK, words [W RET, W ms] ++ [], yS⟩ := by
    rw [show compileExpr (Expr.load MS) ++ (compileExpr (Expr.imm RET) ++
          ([.op .ret] ++ contK))
        = (compileExpr (Expr.load MS) ++ compileExpr (Expr.imm RET) ++ [.op .ret]) ++ contK
        from by rw [List.append_assoc, List.append_assoc]]
    show ASteps programAsm _ ⟨.op .ret :: contK, words [W RET, W ms] ++ [], yS⟩
    rw [← hms]
    show ASteps programAsm _
      ⟨.op .ret :: contK, words [W RET, evalExpr (Expr.load MS) yS] ++ [], yS⟩
    exact ret_args_steps (model := localModel) (prog := programAsm)
      (k := contK) (σ := []) hokMS (exprOK_imm RET)
  -- the halt configuration
  set bH : AConf := ⟨.op .ret :: contK, words [W RET, W ms] ++ [], yS⟩
  set yH : EvmState :=
    { touchMemory yS (W RET).toNat (W ms).toNat with
      halted := some (YulSemantics.EVM.HaltKind.ret,
        readBytes yS.memory (W RET).toNat (W ms).toNat) }
  refine ⟨bH, yH, ASteps.trans hs1 hs2,
    ahalt_ret (model := localModel) (prog := programAsm) (p := W RET) (s := W ms),
    ?_⟩
  have hRET : (W RET).toNat = RET := toNat_W (by unfold RET; norm_num)
  have hmsv : (W ms).toNat = ms := toNat_W
    (Nat.lt_of_le_of_lt hms32 (by norm_num : (32: Nat) < 2 ^ 256))
  have htouch : touchMemory yS RET ms = yS :=
    touchMemoryRange_noop hms0 (by
      show RET + ms ≤ 32 * yS.activeWords.toNat
      have haw : yS.activeWords.toNat = 250 := hfy.1
      rw [haw]; unfold RET; omega)
  show yH.halted = some (.ret, (natToBytes r ms).toList)
  have hred : yH.halted
      = some (YulSemantics.EVM.HaltKind.ret,
        readBytes yS.memory (W RET).toNat (W ms).toNat) := rfl
  rw [hred, hRET, hmsv]
  congr 1
  congr 1
  have hmem : yS.memory = storeWord y.memory RET (W r <<< ((32 - ms) * 8)) := rfl
  rw [hmem]
  exact readBytes_serWord y.memory r ms hms32 hr

/-- The zero-modulus path: `T2 := 0` at `lwZeroMod`, then serialize and halt
with the all-zero (single-byte-per-width) return value. -/
theorem wpZeroModPath {calldata : ByteArray} {bs es ms bo eo mo m : Nat}
    {y : EvmState}
    (hfy : WPState y calldata bs es ms bo eo mo)
    (hT0 : loadWord y.memory T0 = W m)
    (hms0 : 0 < ms) (hms32 : ms ≤ 32) :
    ∃ (b : AConf) (yst' : EvmState),
      ASteps programAsm ⟨wpZeroModOpen programLabels contK, [], y⟩ b ∧
      AHalt programAsm b yst' ∧
      yst'.halted = some (.ret, (natToBytes 0 ms).toList) := by
  have hs1 : ASteps programAsm ⟨wpZeroModOpen programLabels contK, [], y⟩
      ⟨[.label programLabels.lweSer] ++ (wpSer programLabels ++ contK), [],
        { y with memory := storeWord y.memory T2 (W 0) }⟩ :=
    storeW (c := T2) (yst := y) (exprOK_imm 0) (by decide) hfy.1
      (rfl : evalExpr (Expr.imm 0) y = W 0)
  have hframe := WPState_store1 (c := T2) (v := W 0) hfy hT0 (by decide)
  have hT2z : loadWord (storeWord y.memory T2 (W 0)) T2 = W 0 := by
    rw [loadWord_storeWord]
  obtain ⟨b, yst', hS, hH, hD⟩ := serHalt hframe.1 hms0 hms32 hT2z
    (Nat.pow_pos (by norm_num : (0 : Nat) < 256))
  exact ⟨b, yst', hs1.trans ((labelStep programLabels.lweSer).trans hS), hH, hD⟩

/-- A `width`-byte padded read is below `256 ^ width`. -/
theorem bytesToNatPadded_lt_pow (bytes : ByteArray) (p : Nat) :
    ∀ ms : Nat, bytesToNatPadded bytes p ms < 256 ^ ms := by
  intro ms
  induction ms with
  | zero => rw [bytesToNatPadded_zero_width]; norm_num
  | succ n ih =>
    rw [bytesToNatPadded_succ]
    have hb : (byteFrom bytes.toList (p + n)).toNat < 256 :=
      (byteFrom bytes.toList (p + n)).toNat_lt
    have h1 : bytesToNatPadded bytes p n * 256 < 256 ^ n * 256 :=
      Nat.mul_lt_mul_of_pos_right ih (by norm_num)
    calc bytesToNatPadded bytes p n * 256 + (byteFrom bytes.toList (p + n)).toNat
        < 256 ^ n * 256 := by omega
      _ = 256 ^ (n + 1) := by rw [Nat.pow_succ]

set_option maxHeartbeats 10000000 in
/-- The word-path main theorem: from the entry state (header cells set) the
program halts returning exactly `spec calldata`. -/
theorem wordPath_correct {calldata : ByteArray} {bs es ms bo eo mo : Nat}
    {yst : EvmState}
    (hbs : bs ≤ 1024) (hes : es ≤ 1024) (hms0 : 0 < ms) (hms32 : ms ≤ 32)
    (hbo : bo = 96) (heo : eo = bo + bs) (hmo : mo = eo + es)
    (hbsz : baseSize calldata = bs) (hesz : exponentSize calldata = es)
    (hmsz : modulusSize calldata = ms)
    (hm256 : bytesToNatPadded calldata mo ms < 2 ^ 256)
    (hent : WordEntry yst calldata bs es ms bo eo mo) :
    ∃ (b : AConf) (yst' : EvmState),
      ASteps programAsm
        ⟨secWordPath programLabels ++ (secBigPath programLabels ++ progTail),
          [], yst⟩ b ∧
      AHalt programAsm b yst' ∧
      yst'.halted = some (.ret, (spec calldata).toList) := by
  -- the spec value, in path terms (header sizes tie the cell values)
  have hspec : spec calldata = natToBytes
      (modPow (bytesToNatPadded calldata 96 bs)
        (bytesToNatPadded calldata (96 + bs) es)
        (bytesToNatPadded calldata (96 + bs + es) ms)) ms := by
    unfold spec
    rw [if_neg (by rw [hmsz]; omega)]
    rw [hbsz, hesz, hmsz]
  have hmo' : mo = 96 + bs + es := by omega
  -- the entry code is the prefix fragment over `contK`
  have hentry : secWordPath programLabels ++ (secBigPath programLabels ++ progTail)
      = wpPrefixOpen programLabels contK := by
    rw [secWordPath_open, contK_def]
  rw [hentry]
  by_cases hmzero : bytesToNatPadded calldata mo ms = 0
  · -- zero modulus: jump to `lwZeroMod`, serialize zero
    obtain ⟨y2, ⟨hf2, hT02⟩, hA⟩ := prefix_zero hbs hes hms0 hms32 hbo heo hmo hent hmzero
    rw [wpZeroMod_open] at hA
    obtain ⟨b, yst', hS, hH, hD⟩ := wpZeroModPath hf2 hT02 hms0 hms32
    refine ⟨b, yst', hA.trans hS, hH, ?_⟩
    have hm0M : bytesToNatPadded calldata (96 + bs + es) ms = 0 := by
      rw [← hmo']; exact hmzero
    rw [hspec, modPow_eq, if_pos hm0M, hD]
  · -- nonzero modulus: the full big path
    have hpos : 0 < bytesToNatPadded calldata mo ms := Nat.pos_of_ne_zero hmzero
    have hm0ne : ¬ (bytesToNatPadded calldata (96 + bs + es) ms = 0) := by
      intro hh; rw [← hmo'] at hh; exact hmzero hh
    obtain ⟨y2, ⟨hf2, hT02, hT12, hI2⟩, hA⟩ :=
      prefix_nonzero hbs hes hms0 hms32 hbo heo hmo hent hpos hm256 contK
    obtain ⟨y3, hf3, hT03, hT13, hI3, hB⟩ :=
      baseLoop_correct hbs hes hms0 hms32 hbo heo hmo hf2 hT02 hpos hm256 hT12 hI2
    rw [wpLwbDone_open] at hB
    obtain ⟨y4, ⟨hf4, hT04, hT14, hI4c⟩, hC⟩ := lwbDone_to_scan hf3 hT03 hT13
    have hpfx0 : bytesToNatPadded calldata eo 0 = 0 :=
      bytesToNatPadded_zero_width calldata eo
    rcases scanLoop hbs hes hbo heo es 0 (by omega) y4
        ⟨hf4, hT04, hT14, hI4c, hpfx0⟩ with ⟨y5, w, j, hinv5, hD⟩ | ⟨y5, hinv5, hD⟩
    · -- a nonzero byte was found: run the exponent loop, serialize
      obtain ⟨hf5, hT05, hT15, hI5, hW5, hw05, hw2565, hj5, hpfx5, hbw5⟩ := hinv5
      rw [wpLwInit_open] at hD
      obtain ⟨y6, ⟨hf6, hT06, hT16, hI6, hT26⟩, hE⟩ :=
        found_to_rest hf5 hT05 hpos hm256 hT15 hI5 hW5 hw05 hw2565
      rw [wpRest_open] at hE
      obtain ⟨y7, ⟨hf7, hT07, hT17, hT27⟩, hF⟩ :=
        bytesPath hbs hes hbo heo hpos hm256 hf6 hT06 hT16 hI6 hj5 hpfx5 hbw5 hT26
      have hr : bytesToNatPadded calldata bo bs ^ bytesToNatPadded calldata eo es
          % bytesToNatPadded calldata mo ms < 256 ^ ms :=
        Nat.lt_trans (Nat.mod_lt _ hpos) (bytesToNatPadded_lt_pow calldata mo ms)
      obtain ⟨b, yst'', hS, hH, hD2⟩ := serHalt hf7 hms0 hms32 hT27 hr
      rw [heo, hbo, hmo'] at hD2
      refine ⟨b, yst'', (((hA.trans hB).trans hC).trans hD).trans (hE.trans (hF.trans hS)),
        hH, ?_⟩
      rw [hspec, modPow_eq, if_neg hm0ne, hD2]
    · -- the exponent was exhausted: `T2 := 1 % m`, serialize
      obtain ⟨hf5, hT05, hT15, hI5, hpfxE⟩ := hinv5
      rw [heo, hbo] at hpfxE
      rw [wpExpZero_open] at hD
      obtain ⟨y6, ⟨hf6, hT06, hT26⟩, hE⟩ := expZero_path hf5 hT05 hpos hm256
      have hr : (1 : Nat) % bytesToNatPadded calldata mo ms < 256 ^ ms := by
        have h256 : (1 : Nat) < 256 ^ ms := by
          cases ms with
          | zero => exact absurd hms0 (by omega)
          | succ k =>
            have hp : (0 : Nat) < 256 ^ k := Nat.pow_pos (by norm_num)
            rw [Nat.pow_succ]
            omega
        exact Nat.lt_of_le_of_lt (Nat.mod_le 1 _) h256
      obtain ⟨b, yst'', hS, hH, hD2⟩ := serHalt hf6 hms0 hms32 hT26 hr
      rw [hmo'] at hD2
      refine ⟨b, yst'', (((hA.trans hB).trans hC).trans hD).trans (hE.trans hS),
        hH, ?_⟩
      rw [hspec, modPow_eq, if_neg hm0ne, hpfxE, Nat.pow_zero, hD2]

end Challenge.Modexp.Submission.Proof.WordPath

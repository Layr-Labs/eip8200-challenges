import Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorTrace
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryReadonly
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryFrames
import Challenge.Modexp.Submission.Proofs.Fast.CarryResult

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorModel
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CiosCachedMidMemory
open CiosAccumulatorMemory CiosCarryMemory

/-- The deferred-store row has the same complete memory as the proven carry row. -/
theorem rowWithTN_carry (mem : ByteArray) (pa pb n i : Nat) (hn : n ≤ 32) :
    rowWithTN mem pa pb n i = CarryRowModel.rowCarry mem pa pb n i := by
  rw [rowWithTN_eq mem pa pb n i hn]
  rfl

theorem rowsWithTN_carry (mem : ByteArray) (pa pb n i : Nat) (hn : n ≤ 32) :
    rowsWithTN mem pa pb n i = CarryRowModel.rowsCarry mem pa pb n i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [rowsWithTN, CarryRowModel.rowsCarry, ih, rowWithTN_carry _ _ _ _ _ hn]

def middleProgram : List Instr :=
  CiosAccumulatorTrace.middleStore ++ CiosCarryReadonly.cachedProduct

/-- The middle sum and overflow replace two dead row slots. The correction
product uses unchanged memory and preserves both new register values. -/
theorem run_middle (s : State) (mem : ByteArray) (c bi slot : UInt256)
    (pa pb n i : Nat) (tl inv m0 aEnd a96 a64 a32 dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) (hminv : inverseInvariant mem n) :
    runInstructions middleProgram
      (CiosCarryFrames.midState (carrySlot := slot) s mem c bi pa pb n i inv m0
        (tl :: a96 :: a64 :: a32 :: aEnd :: dst :: ret :: rest)) =
    some (CiosCarryFrames.l2At (carrySlot := MachineState.readWord mem 8224+c)
      4565 s mem (CarryRowModel.overflow mem c) (rowMu mem n) (rowC0 mem n)
      pa pb n i 0 inv m0 (tl :: a96 :: a64 :: a32 :: aEnd :: dst :: ret :: rest)) := by
  have hs := CiosAccumulatorTrace.run_middleStore {s with memory := mem} c bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa) (UInt256.ofNat (pb-32))
    (CiosCarryFrames.l1Target n) slot
    (allOnes :: CiosCarryFrames.l2Target n :: inv :: m0 :: tl :: a96 :: a64 :: a32 ::
      aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact
  have hp := CiosCarryReadonly.run_cachedProduct_model
    (carrySlot := MachineState.readWord mem 8224+c) {s with memory := mem}
    (midCarry mem c) (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat pa)
    (UInt256.ofNat (pb-32)) (CiosCarryFrames.l1Target n) (CiosCarryFrames.l2Target n)
    tl inv m0 aEnd a96 a64 a32 dst ret n rest hcap hn32 hact hc hminv
  have trace := runInstructions_append_some _ _ _ _ _ hs hp
  simpa only [middleProgram, CiosCarryReadonly.cacheStack, framed,
    CiosCarryFrames.midState, CiosCarryFrames.l2At, l2Step, midCarry, CarryRowModel.overflow,
    List.append_assoc, List.cons_append, List.nil_append] using trace

#print axioms rowsWithTN_carry
#print axioms run_middle
end Challenge.Modexp.Submission.Proofs.Fast.CiosAccumulatorModel

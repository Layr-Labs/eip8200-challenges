import Challenge.Modexp.Reference.Proofs.Bytecode.Main
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# MODEXP output dispatcher

The zero-width EIP-198 result is a complete terminating bytecode path.  It is
kept separate because it touches no operand bytes or memory and therefore has
the challenge's minimum gas cost.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

private def loc (index : Nat) (hindex : index < 961 := by omega) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  Challenge.EvmProof.Stepper.Located.ofIndex Artifact.allWellFormed
    ⟨index, by
      change index < Artifact.referenceInstructions.length
      rw [Artifact.referenceInstructions_count]
      exact hindex⟩

def zeroSizePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [loc 921, loc 922, loc 923, loc 924, loc 925, loc 926, loc 927]

def zeroSizeFinalState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1236
    stack := [UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)]
    halt := .Returned
    hReturn := ByteArray.empty }

set_option linter.unusedSimpArgs false in
theorem run_zeroSize (input : ByteArray) (hzero : modulusSize input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroSizePath
      (Main.headerState input) = some (zeroSizeFinalState input) := by
  simp (config := { maxSteps := 200000 })
    [zeroSizePath, loc, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Main.headerState, zeroSizeFinalState, hzero, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_zeroSize (input : ByteArray) (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (Main.headerState input)
      (zeroSizeFinalState input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka zeroSizePath
  · rfl
  · rfl
  · exact run_zeroSize input hzero
  · rfl
  · exact deployAddress_not_precompile

theorem gasSteps_zeroSize_cost (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (gasSteps_zeroSize input hzero).cost = 21 := by
  rfl

/-- Complete trace and exact minimum gas for zero-width results. -/
def gasSteps_zeroSize_total (input : ByteArray) (hvalid : ValidInput input)
    (hzero : modulusSize input = 0) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (zeroSizeFinalState input) :=
  (Main.gasSteps_header input hvalid).trans (gasSteps_zeroSize input hzero)

theorem gasSteps_zeroSize_total_cost (input : ByteArray)
    (hvalid : ValidInput input) (hzero : modulusSize input = 0) :
    (gasSteps_zeroSize_total input hvalid hzero).cost = 183 := by
  rw [Challenge.EvmProof.GasSteps.trans_cost,
    Main.gasSteps_header_cost, gasSteps_zeroSize_cost]

@[simp] theorem zeroSizeFinalState_isDone (input : ByteArray) :
    (zeroSizeFinalState input).isDone = true := by
  rfl

theorem zeroSizeFinalState_result (input : ByteArray)
    (hzero : modulusSize input = 0) :
    (zeroSizeFinalState input).toResult = .returned (spec input) := by
  simp [zeroSizeFinalState, spec, hzero]

end Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch

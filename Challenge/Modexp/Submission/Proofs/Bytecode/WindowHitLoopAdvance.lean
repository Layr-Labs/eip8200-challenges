import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvanceJump

set_option warningAsError true
set_option maxRecDepth 40000

/-!
# Fixed-width loop advance

This composes the separately checked arithmetic head and jump tail, then
specializes their generic framed-state contract to the concrete loop states.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvance

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitPaths
open WindowHitStates

theorem run_loopAdvance (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) (hpointer : pointer < 160) :
    Challenge.EvmProof.Stepper.runLocatedBlock loopAdvancePath
      (wordState input pointer 4 3547 accumulator) =
        some (loopState input (pointer + 4)
          (WindowMath.chunkWordStep (modulusWord input) (baseWord input)
            accumulator (MachineState.readWord input pointer))) := by
  let chunk := WindowMath.chunkWordStep (modulusWord input) (baseWord input)
    accumulator (MachineState.readWord input pointer)
  let template := wordState input pointer 4 3547 accumulator
  have hhead := WindowHitLoopAdvanceHead.run template
    (MachineState.readWord input pointer) (UInt256.ofNat pointer) chunk
    (modulusWord input) (routeStack input) pointer rfl hpointer
    (by simp [routeStack]) rfl
  have hjump := WindowHitLoopAdvanceJump.run template
    (UInt256.ofNat (pointer + 4)) chunk (modulusWord input) (routeStack input)
    (by simp [routeStack]) rfl rfl
  have hall := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (loopAdvancePath.take 3) (loopAdvancePath.drop 3)
    (WindowHitLoopAdvanceHead.framed template 3547
      (MachineState.readWord input pointer :: UInt256.ofNat pointer :: chunk ::
        modulusWord input :: routeStack input))
    (WindowHitLoopAdvanceHead.framed template 3551
      (UInt256.ofNat (pointer + 4) :: chunk :: modulusWord input ::
        routeStack input))
    (WindowHitLoopAdvanceHead.framed template 3197
      (UInt256.ofNat (pointer + 4) :: chunk :: modulusWord input ::
        routeStack input))
    hhead rfl hjump
  simpa only [List.take_append_drop, WindowHitLoopAdvanceHead.framed,
    template, chunk, wordState, loopState,
    WindowHitStates.byteAccumulator_four, List.cons_append, List.nil_append] using hall

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running := by rfl)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_loopAdvance (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) (hpointer : pointer < 160) :
    LoopAdvanceStep input pointer accumulator :=
  sound loopAdvancePath (run_loopAdvance input pointer accumulator hpointer)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvance

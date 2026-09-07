import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopTailFinish
set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open Word

def bitFinishTailPath := bitFinishTailHeadPath ++ bitFinishTailFinishPath

theorem run_bitFinishTail (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (expLoopState input (outer + 1) acc base) := by
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    bitFinishTailHeadPath bitFinishTailFinishPath
    (bitFinishDispatchState input outer byte offset acc base)
    (bitFinishTailMidState input outer acc base)
    (expLoopState input (outer + 1) acc base)
    (run_bitFinishTailHead input outer byte offset acc base) rfl
    (run_bitFinishTailFinish input outer acc base hvalid houter)

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

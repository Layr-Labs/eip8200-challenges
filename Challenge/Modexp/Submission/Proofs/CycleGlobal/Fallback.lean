import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUMain
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUBlocks
set_option warningAsError true
namespace CycleSubmission.Global.Fallback
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

theorem correct (s : State) (env : Environment Artifact.artifact .Osaka s)
    (hpc : s.pc = UInt256.ofNat 219) (hstk : s.stack.length < 900)
    (haw : s.activeWords.toNat ≤ 289) (hcs : s.callStack = [])
    (hvalid : Challenge.Modexp.ValidInput s.executionEnv.calldata)
    (hpos : 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata) :
    ∃ final : State, Nonempty (GasSteps s final) ∧ final.isDone = true ∧
      final.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) :=
  BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
    BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks s env hpc hstk haw hcs hvalid hpos

end CycleSubmission.Global.Fallback

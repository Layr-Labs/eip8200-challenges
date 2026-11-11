import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectR5Entry
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TailRoutes
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace CycleSubmission.Global.TailFour
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission CycleSubmission.Global
open Monpro CiosCached StagedOperand
noncomputable def head4 (s : State) (mem : ByteArray) (bsize esize k mi : Nat)
    
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 4 bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hmachine : ((MachineState.readWord mem 96).toNat * mi + 1) % 2^256 = 0) :
    GasSteps (SlimFrames.special s mem 4 bsize esize 128 k)
      (DirectR5Reuse.result s mem (UInt256.ofNat (k-1)) bsize esize 128) := by
  simpa [SlimFrames.special] using
    (DirectR5Entry.enter4 s mem (UInt256.ofNat (k-1)) bsize esize 128 hact env)

#print axioms head4
end CycleSubmission.Global.TailFour

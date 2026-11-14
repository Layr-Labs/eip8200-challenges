import Challenge.Modexp.Submission.Proofs.Cycle.EntryMeaning
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.EntryBinding
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.EntryMeaning CycleSubmission.Execution
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding WindowTwentyOneSlice
open HistoricalSearch.CRTControl
def entryBlock : Block Artifact.artifact .Osaka 3328 entryProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2589 110 3328 entryProgram
    (by change 2589+110 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def entered (s : State) (f : Caller) : State :=
  result s f

noncomputable def gasSteps (s : State) (f : Caller)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : f.tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 3328, stack := saved f} (entered s f) := by
  have h := entryBlock.steps
    (s := {s with pc := UInt256.ofNat 3328, stack := saved f})
    (env.transfer rfl rfl) rfl (run s f (by omega) hact)
  exact h

end CycleSubmission.EntryBinding

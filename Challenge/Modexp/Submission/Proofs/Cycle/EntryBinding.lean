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
def entryBlock : Block Artifact.artifact .Osaka 5964 entryProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 4922 109 5964 entryProgram
    (by change 4922+109 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 4922+109 ≤ 9189)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def headBlock : Block Artifact.artifact .Osaka 6152 jumpDestProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 5031 1 6152 jumpDestProgram
    (by change 5031+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 5031+1 ≤ 9189)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def entered (s : State) (f : Caller) : State :=
  {result s f with pc := UInt256.ofNat 6153}

noncomputable def gasSteps (s : State) (f : Caller)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : f.tail.length ≤ 944) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 5964, stack := saved f} (entered s f) := by
  have h := entryBlock.steps
    (s := {s with pc := UInt256.ofNat 5964, stack := saved f})
    (env.transfer rfl rfl) rfl (run s f (by omega) hact)
  have cap : (result s f).stack.length < 1024 := by
    simp only [result, CycleSubmission.SquareMeaning.frame0, saved,
      List.length_append, List.length_cons, List.length_nil]
    omega
  have h2 := headBlock.steps (s := result s f) (env.transfer rfl rfl) rfl
    (jumpDest_run (result s f) cap)
  exact h.trans h2

end CycleSubmission.EntryBinding

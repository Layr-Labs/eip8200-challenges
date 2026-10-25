import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

/-- Keep a private working count below the fourteen-word arithmetic frame.
The original count is retained for JUMPI; the working count is decremented in place. -/
def counterHeadProgram : List Instr :=
  [.op .JUMPDEST, .push 1 1, .op (.Dup ⟨15, by decide⟩),
   .op .SUB, .op (.Swap ⟨14, by decide⟩), .push 17 5694]

def counterHeadModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7651
    stack := UInt256.ofNat 5694 :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: (c - UInt256.ofNat 1) :: rest}

theorem counterHead_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions counterHeadProgram {s with
      pc := UInt256.ofNat 7627
      stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: c :: rest} =
      some (counterHeadModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, counterHeadProgram, counterHeadModel, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]
end CycleSubmission.Execution

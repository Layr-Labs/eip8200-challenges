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
The original count is retained for JUMPI; the working count is decremented in place.
There is no overflow test in front of it: the square loop's operands stay below `R - 2N`. -/
def counterHeadProgram : List Instr :=
  [.push 19 1, .op (.Dup ⟨15, by decide⟩),
   .op .SUB, .op (.Swap ⟨14, by decide⟩), .push 2 5694]

def counterHeadModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c : UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7645
    stack := UInt256.ofNat 5694 :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: (c - UInt256.ofNat 1) :: rest}

theorem counterHead_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions counterHeadProgram {s with
      pc := UInt256.ofNat 7619
      stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: c :: rest} =
      some (counterHeadModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 c rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, counterHeadProgram, counterHeadModel, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

/-- The loop exit at 7646 runs six `JUMPDEST`s; the byte filler that keeps every later pc in
place is the widened counter push (`PUSH19 1`) at 7619. -/
def counterExitProgram : List Instr :=
  [.op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

theorem counterExit_run (s : State) (rest : List UInt256) (hcap : rest.length ≤ 1000) :
    runInstructions counterExitProgram {s with pc := UInt256.ofNat 7646, stack := rest} =
      some {s with pc := UInt256.ofNat 7652, stack := rest} := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 2) : rest.length + j < 1024 := by omega
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  simp [hz, h0, h1, counterExitProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]
end CycleSubmission.Execution

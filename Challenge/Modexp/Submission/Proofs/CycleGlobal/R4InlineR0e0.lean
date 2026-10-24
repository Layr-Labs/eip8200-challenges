import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.R4Runs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
namespace CycleSubmission.Global.Fast.R4InlineTransport
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast R4Math R4Runs R4Blocks

def r0e_0OldP0 : List Instr := [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4382, .push 2 4621, .op .JUMP]
theorem r0e_0OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hjump0 : Decode.isValidJumpDest s.executionEnv.code (4621 : UInt256).toNat = true) :
    runInstructions r0e_0OldP0 { s with pc := UInt256.ofNat 4372, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := (4621 : UInt256), stack := (4382 : UInt256) :: (0 : UInt256) :: x1 :: x2 :: x3 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r0e_0OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hjump0] <;> rfl

def r0e_0Old : List Instr := r0e_0OldP0
theorem r0e_0Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hjump0 : Decode.isValidJumpDest s.executionEnv.code (4621 : UInt256).toNat = true) :
    runInstructions r0e_0Old { s with pc := UInt256.ofNat 4372, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := (4621 : UInt256), stack := (4382 : UInt256) :: (0 : UInt256) :: z1 :: z2 :: z3 :: z4 :: z0 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := r0e_0OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap hjump0
  have h := g0
  simpa only [r0e_0Old, List.append_assoc] using h

def r0e_0NewP0 : List Instr := [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0]
theorem r0e_0NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0e_0NewP0 { s with pc := UInt256.ofNat 4129, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4132, stack := (0 : UInt256) :: x1 :: x2 :: x3 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 13) : rest.length + j < 1024 := by omega
  simp [r0e_0NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc] <;> rfl

def r0e_0New : List Instr := r0e_0NewP0
theorem r0e_0New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0e_0New { s with pc := UInt256.ofNat 4129, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := UInt256.ofNat 4132, stack := (0 : UInt256) :: z1 :: z2 :: z3 :: z4 :: z0 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := r0e_0NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap
  have h := g0
  simpa only [r0e_0New, List.append_assoc] using h

def r0e_0Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest => v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest
  | xs => xs

theorem run_r0e_0 (s : State) (c t3 t2 t1 t0 d k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009) :
    runInstructions r0e_0New
      { s with pc := UInt256.ofNat 4129, stack := c :: t3 :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4132, stack := (⟨0⟩ : UInt256) :: t3 :: t2 :: t1 :: t0 :: c :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have hn := r0e_0New_run s (c) (t3) (t2) (t1) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [Challenge.EvmProof.Word.word_add_comm, show (0 : UInt256) = ⟨0⟩ by decide] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

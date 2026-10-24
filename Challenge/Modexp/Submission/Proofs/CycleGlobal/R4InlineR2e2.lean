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

def r2e_2OldP0 : List Instr := [.op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op (.Swap ⟨0, by decide⟩)]
theorem r2e_2OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r2e_2OldP0 { s with pc := UInt256.ofNat 4562, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4568, stack := x1 :: (UInt256.lt (x6 + x0) x6) :: x2 :: x3 :: x4 :: x5 :: (x6 + x0) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r2e_2OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2e_2OldP1 : List Instr := [.op .POP, .push 2 4577, .push 2 4621, .op .JUMP]
theorem r2e_2OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hjump0 : Decode.isValidJumpDest s.executionEnv.code (4621 : UInt256).toNat = true) :
    runInstructions r2e_2OldP1 { s with pc := UInt256.ofNat 4568, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := (4621 : UInt256), stack := (4577 : UInt256) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r2e_2OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hjump0]

def r2e_2Old : List Instr := r2e_2OldP0 ++ r2e_2OldP1
theorem r2e_2Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hjump0 : Decode.isValidJumpDest s.executionEnv.code (4621 : UInt256).toNat = true) :
    runInstructions r2e_2Old { s with pc := UInt256.ofNat 4562, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := (4621 : UInt256), stack := (4577 : UInt256) :: (UInt256.lt (z6 + z0) z6) :: z2 :: z3 :: z4 :: z5 :: (z6 + z0) :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r2e_2OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g1 := r2e_2OldP1_run s (z1) ((UInt256.lt (z6 + z0) z6)) (z2) (z3) (z4) (z5) ((z6 + z0)) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap hjump0
  have h := (runInstructions_append_some _ _ _ _ _ g0 g1)
  simpa only [r2e_2Old, List.append_assoc] using h

def r2e_2NewP0 : List Instr := [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT]
theorem r2e_2NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r2e_2NewP0 { s with pc := UInt256.ofNat 4492, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4497, stack := (UInt256.lt (x5 + x0) x5) :: x1 :: x2 :: x3 :: x4 :: (x5 + x0) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r2e_2NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2e_2New : List Instr := r2e_2NewP0
theorem r2e_2New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r2e_2New { s with pc := UInt256.ofNat 4492, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := UInt256.ofNat 4497, stack := (UInt256.lt (z5 + z0) z5) :: z1 :: z2 :: z3 :: z4 :: (z5 + z0) :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := r2e_2NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap
  have h := g0
  simpa only [r2e_2New, List.append_assoc] using h

def r2e_2Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest => v1 :: v4 :: v5 :: v2 :: v3 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest
  | xs => xs

theorem run_r2e_2 (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009) :
    runInstructions r2e_2New
      { s with pc := UInt256.ofNat 4492, stack := c :: p1 :: p0 :: p3 :: p2 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4497, stack := (UInt256.lt (p4 + c) p4) :: p1 :: p0 :: p3 :: p2 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have hn := r2e_2New_run s (c) (p1) (p0) (p3) (p2) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [Challenge.EvmProof.Word.word_add_comm, show (0 : UInt256) = ⟨0⟩ by decide] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

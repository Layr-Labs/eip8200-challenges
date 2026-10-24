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

def redt_0OldP0 : List Instr := [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP, .op (.Swap ⟨5, by decide⟩)]
theorem redt_0OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_0OldP0 { s with pc := UInt256.ofNat 4710, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4716, stack := x8 :: x3 :: (x8 + x0) :: x5 :: x6 :: x7 :: x2 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [redt_0OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def redt_0OldP1 : List Instr := [.op (.Dup ⟨2, by decide⟩), .op .LT, .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]
theorem redt_0OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) (hjump0 : Decode.isValidJumpDest s.executionEnv.code x6.toNat = true) :
    runInstructions redt_0OldP1 { s with pc := UInt256.ofNat 4716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := x6, stack := x2 :: x3 :: x4 :: x5 :: ((UInt256.lt x2 x0) + x1) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [redt_0OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hjump0]

def redt_0Old : List Instr := redt_0OldP0 ++ redt_0OldP1
theorem redt_0Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) (hjump0 : Decode.isValidJumpDest s.executionEnv.code z2.toNat = true) :
    runInstructions redt_0Old { s with pc := UInt256.ofNat 4710, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } =
    some { s with pc := z2, stack := (z8 + z0) :: z5 :: z6 :: z7 :: ((UInt256.lt (z8 + z0) z8) + z3) :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } := by
  have g0 := redt_0OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g1 := redt_0OldP1_run s (z8) (z3) ((z8 + z0)) (z5) (z6) (z7) (z2) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap hjump0
  have h := (runInstructions_append_some _ _ _ _ _ g0 g1)
  simpa only [redt_0Old, List.append_assoc] using h

def redt_0NewP0 : List Instr := [.op (.Dup ⟨7, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op .POP, .op (.Swap ⟨5, by decide⟩)]
theorem redt_0NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_0NewP0 { s with pc := UInt256.ofNat 4217, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4222, stack := x7 :: x2 :: x3 :: x4 :: x5 :: (x7 + x0) :: x1 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [redt_0NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def redt_0NewP1 : List Instr := [.op (.Dup ⟨5, by decide⟩), .op .LT, .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .POP]
theorem redt_0NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_0NewP1 { s with pc := UInt256.ofNat 4222, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4227, stack := x2 :: x3 :: x4 :: x5 :: ((UInt256.lt x5 x0) + x1) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [redt_0NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def redt_0New : List Instr := redt_0NewP0 ++ redt_0NewP1
theorem redt_0New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_0New { s with pc := UInt256.ofNat 4217, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } =
    some { s with pc := UInt256.ofNat 4227, stack := z3 :: z4 :: z5 :: (z7 + z0) :: ((UInt256.lt (z7 + z0) z7) + z2) :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } := by
  have g0 := redt_0NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g1 := redt_0NewP1_run s (z7) (z2) (z3) (z4) (z5) ((z7 + z0)) (z1) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 g1)
  simpa only [redt_0New, List.append_assoc] using h

def redt_0Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: rest => v1 :: v2 :: v3 :: v0 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: rest
  | xs => xs

theorem run_redt_0 (s : State) (c m ret v p3 q2 q1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007) :
    runInstructions redt_0New
      { s with pc := UInt256.ofNat 4217, stack := c :: m :: v :: q2 :: q1 :: q0 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4227, stack := q2 :: q1 :: q0 :: (p4 + c) :: (v + (UInt256.lt (p4 + c) p4)) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have hn := redt_0New_run s (c) (m) (v) (q2) (q1) (q0) (p3) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [Challenge.EvmProof.Word.word_add_comm, show (0 : UInt256) = ⟨0⟩ by decide] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

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

def reds3_3OldP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨15, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem reds3_3OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3OldP0 { s with pc := UInt256.ofNat 4684, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4690, stack := x1 :: x13 :: x9 :: (x13 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds3_3OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3OldP1 : List Instr := [.op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]
theorem reds3_3OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3OldP1 { s with pc := UInt256.ofNat 4690, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } =
    some { s with pc := UInt256.ofNat 4696, stack := x3 :: ((UInt256.gt x3 (UInt256.mulMod x0 x1 x2)) - (UInt256.mulMod x0 x1 x2)) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds3_3OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3OldP2 : List Instr := [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩)]
theorem reds3_3OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3OldP2 { s with pc := UInt256.ofNat 4696, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4702, stack := ((x3 + x0) + x7) :: ((x3 + x0) + x7) :: (x3 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds3_3OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3OldP3 : List Instr := [.op (.Swap ⟨9, by decide⟩), .op (.Swap ⟨8, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB]
theorem reds3_3OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3OldP3 { s with pc := UInt256.ofNat 4702, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest } =
    some { s with pc := UInt256.ofNat 4708, stack := ((UInt256.gt x5 x2) - x3) :: x4 :: (UInt256.gt x9 x1) :: x6 :: x7 :: x8 :: x10 :: x0 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds3_3OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3OldP4 : List Instr := [.op .SUB, .op .ADD]
theorem reds3_3OldP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3OldP4 { s with pc := UInt256.ofNat 4708, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } =
    some { s with pc := UInt256.ofNat 4710, stack := ((x0 - x1) + x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [reds3_3OldP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3Old : List Instr := reds3_3OldP0 ++ reds3_3OldP1 ++ reds3_3OldP2 ++ reds3_3OldP3 ++ reds3_3OldP4
theorem reds3_3Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3Old { s with pc := UInt256.ofNat 4684, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } =
    some { s with pc := UInt256.ofNat 4710, stack := ((((UInt256.gt z0 (z0 + (z13 * z1))) - ((UInt256.gt (z13 * z1) (UInt256.mulMod z1 z13 z9)) - (UInt256.mulMod z1 z13 z9))) - (z13 * z1)) + (UInt256.gt z4 ((z0 + (z13 * z1)) + z4))) :: z1 :: z2 :: z3 :: z5 :: ((z0 + (z13 * z1)) + z4) :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } := by
  have g0 := reds3_3OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g1 := reds3_3OldP1_run s (z1) (z13) (z9) ((z13 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g2 := reds3_3OldP2_run s ((z13 * z1)) (((UInt256.gt (z13 * z1) (UInt256.mulMod z1 z13 z9)) - (UInt256.mulMod z1 z13 z9))) ((z13 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g3 := reds3_3OldP3_run s (((z0 + (z13 * z1)) + z4)) (((z0 + (z13 * z1)) + z4)) ((z0 + (z13 * z1))) (((UInt256.gt (z13 * z1) (UInt256.mulMod z1 z13 z9)) - (UInt256.mulMod z1 z13 z9))) ((z13 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g4 := reds3_3OldP4_run s (((UInt256.gt z0 (z0 + (z13 * z1))) - ((UInt256.gt (z13 * z1) (UInt256.mulMod z1 z13 z9)) - (UInt256.mulMod z1 z13 z9)))) ((z13 * z1)) ((UInt256.gt z4 ((z0 + (z13 * z1)) + z4))) (z1) (z2) (z3) (z5) (((z0 + (z13 * z1)) + z4)) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [reds3_3Old, List.append_assoc] using h

def reds3_3NewP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem reds3_3NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3NewP0 { s with pc := UInt256.ofNat 4692, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4698, stack := x1 :: x12 :: x8 :: (x12 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds3_3NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3NewP1 : List Instr := [.op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]
theorem reds3_3NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3NewP1 { s with pc := UInt256.ofNat 4698, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4704, stack := x3 :: ((UInt256.gt x3 (UInt256.mulMod x0 x1 x2)) - (UInt256.mulMod x0 x1 x2)) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds3_3NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3NewP2 : List Instr := [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩)]
theorem reds3_3NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3NewP2 { s with pc := UInt256.ofNat 4704, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } =
    some { s with pc := UInt256.ofNat 4710, stack := ((x3 + x0) + x7) :: ((x3 + x0) + x7) :: (x3 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds3_3NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3NewP3 : List Instr := [.op (.Swap ⟨8, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]
theorem reds3_3NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3NewP3 { s with pc := UInt256.ofNat 4710, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } =
    some { s with pc := UInt256.ofNat 4716, stack := (((UInt256.gt x5 x2) - x3) - x4) :: (UInt256.gt x9 x1) :: x6 :: x7 :: x8 :: x0 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds3_3NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3NewP4 : List Instr := [.op .ADD]
theorem reds3_3NewP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3NewP4 { s with pc := UInt256.ofNat 4716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4717, stack := (x0 + x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [reds3_3NewP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds3_3New : List Instr := reds3_3NewP0 ++ reds3_3NewP1 ++ reds3_3NewP2 ++ reds3_3NewP3 ++ reds3_3NewP4
theorem reds3_3New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3New { s with pc := UInt256.ofNat 4692, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } =
    some { s with pc := UInt256.ofNat 4717, stack := ((((UInt256.gt z0 (z0 + (z12 * z1))) - ((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z8)) - (UInt256.mulMod z1 z12 z8))) - (z12 * z1)) + (UInt256.gt z4 ((z0 + (z12 * z1)) + z4))) :: z1 :: z2 :: z3 :: ((z0 + (z12 * z1)) + z4) :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } := by
  have g0 := reds3_3NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g1 := reds3_3NewP1_run s (z1) (z12) (z8) ((z12 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g2 := reds3_3NewP2_run s ((z12 * z1)) (((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z8)) - (UInt256.mulMod z1 z12 z8))) ((z12 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g3 := reds3_3NewP3_run s (((z0 + (z12 * z1)) + z4)) (((z0 + (z12 * z1)) + z4)) ((z0 + (z12 * z1))) (((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z8)) - (UInt256.mulMod z1 z12 z8))) ((z12 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g4 := reds3_3NewP4_run s ((((UInt256.gt z0 (z0 + (z12 * z1))) - ((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z8)) - (UInt256.mulMod z1 z12 z8))) - (z12 * z1))) ((UInt256.gt z4 ((z0 + (z12 * z1)) + z4))) (z1) (z2) (z3) (((z0 + (z12 * z1)) + z4)) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [reds3_3New, List.append_assoc] using h

def reds3_3Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: rest => v0 :: v1 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: rest
  | xs => xs

theorem run_reds3_3 (s : State) (c m ret v p3 p2 q1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003) :
    runInstructions reds3_3New
      { s with pc := UInt256.ofNat 4692, stack := c :: m :: v :: p2 :: p3 :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4717, stack := (sCarry n3 m c p3 k) :: m :: v :: p2 :: (mSum n3 m c p3) :: q1 :: q0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := reds3_3Old_run s (c) (m) (ret) (v) (p3) (p2) (q1) (q0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  have hc := R4Runs.run_reds3 s c m ret v p3 p2 q1 q0 p4 k n0 n1 n2 n3 np rest hcap
  change runInstructions reds3_3Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg reds3_3Perm he
  simp only [reds3_3Perm] at hp
  have hn := reds3_3New_run s (c) (m) (v) (p2) (p3) (q1) (q0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

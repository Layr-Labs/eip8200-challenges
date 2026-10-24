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

def reds2_1OldP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨10, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem reds2_1OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1OldP0 { s with pc := UInt256.ofNat 4658, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4664, stack := x1 :: x12 :: x9 :: (x12 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds2_1OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1OldP1 : List Instr := [.op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]
theorem reds2_1OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1OldP1 { s with pc := UInt256.ofNat 4664, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } =
    some { s with pc := UInt256.ofNat 4670, stack := x3 :: ((UInt256.gt x3 (UInt256.mulMod x0 x1 x2)) - (UInt256.mulMod x0 x1 x2)) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds2_1OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1OldP2 : List Instr := [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩)]
theorem reds2_1OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1OldP2 { s with pc := UInt256.ofNat 4670, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4676, stack := ((x3 + x0) + x8) :: ((x3 + x0) + x8) :: (x3 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds2_1OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1OldP3 : List Instr := [.op (.Swap ⟨10, by decide⟩), .op (.Swap ⟨9, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB]
theorem reds2_1OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1OldP3 { s with pc := UInt256.ofNat 4676, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest } =
    some { s with pc := UInt256.ofNat 4682, stack := ((UInt256.gt x5 x2) - x3) :: x4 :: (UInt256.gt x10 x1) :: x6 :: x7 :: x8 :: x9 :: x11 :: x0 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds2_1OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1OldP4 : List Instr := [.op .SUB, .op .ADD]
theorem reds2_1OldP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1OldP4 { s with pc := UInt256.ofNat 4682, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } =
    some { s with pc := UInt256.ofNat 4684, stack := ((x0 - x1) + x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [reds2_1OldP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1Old : List Instr := reds2_1OldP0 ++ reds2_1OldP1 ++ reds2_1OldP2 ++ reds2_1OldP3 ++ reds2_1OldP4
theorem reds2_1Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1Old { s with pc := UInt256.ofNat 4658, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } =
    some { s with pc := UInt256.ofNat 4684, stack := ((((UInt256.gt z0 (z0 + (z12 * z1))) - ((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z9)) - (UInt256.mulMod z1 z12 z9))) - (z12 * z1)) + (UInt256.gt z5 ((z0 + (z12 * z1)) + z5))) :: z1 :: z2 :: z3 :: z4 :: z6 :: ((z0 + (z12 * z1)) + z5) :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } := by
  have g0 := reds2_1OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g1 := reds2_1OldP1_run s (z1) (z12) (z9) ((z12 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g2 := reds2_1OldP2_run s ((z12 * z1)) (((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z9)) - (UInt256.mulMod z1 z12 z9))) ((z12 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g3 := reds2_1OldP3_run s (((z0 + (z12 * z1)) + z5)) (((z0 + (z12 * z1)) + z5)) ((z0 + (z12 * z1))) (((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z9)) - (UInt256.mulMod z1 z12 z9))) ((z12 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g4 := reds2_1OldP4_run s (((UInt256.gt z0 (z0 + (z12 * z1))) - ((UInt256.gt (z12 * z1) (UInt256.mulMod z1 z12 z9)) - (UInt256.mulMod z1 z12 z9)))) ((z12 * z1)) ((UInt256.gt z5 ((z0 + (z12 * z1)) + z5))) (z1) (z2) (z3) (z4) (z6) (((z0 + (z12 * z1)) + z5)) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [reds2_1Old, List.append_assoc] using h

def reds2_1NewP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem reds2_1NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1NewP0 { s with pc := UInt256.ofNat 4364, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4370, stack := x1 :: x11 :: x8 :: (x11 * x1) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds2_1NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1NewP1 : List Instr := [.op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]
theorem reds2_1NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1NewP1 { s with pc := UInt256.ofNat 4370, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4376, stack := x3 :: ((UInt256.gt x3 (UInt256.mulMod x0 x1 x2)) - (UInt256.mulMod x0 x1 x2)) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [reds2_1NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1NewP2 : List Instr := [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩)]
theorem reds2_1NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1NewP2 { s with pc := UInt256.ofNat 4376, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } =
    some { s with pc := UInt256.ofNat 4382, stack := ((x3 + x0) + x6) :: ((x3 + x0) + x6) :: (x3 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds2_1NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1NewP3 : List Instr := [.op (.Swap ⟨7, by decide⟩), .op .GT, .op (.Swap ⟨3, by decide⟩), .op .GT, .op .SUB, .op .SUB]
theorem reds2_1NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1NewP3 { s with pc := UInt256.ofNat 4382, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } =
    some { s with pc := UInt256.ofNat 4388, stack := (((UInt256.gt x5 x2) - x3) - x4) :: (UInt256.gt x8 x1) :: x6 :: x7 :: x0 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [reds2_1NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1NewP4 : List Instr := [.op .ADD]
theorem reds2_1NewP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1NewP4 { s with pc := UInt256.ofNat 4388, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4389, stack := (x0 + x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [reds2_1NewP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def reds2_1New : List Instr := reds2_1NewP0 ++ reds2_1NewP1 ++ reds2_1NewP2 ++ reds2_1NewP3 ++ reds2_1NewP4
theorem reds2_1New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1New { s with pc := UInt256.ofNat 4364, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } =
    some { s with pc := UInt256.ofNat 4389, stack := ((((UInt256.gt z0 (z0 + (z11 * z1))) - ((UInt256.gt (z11 * z1) (UInt256.mulMod z1 z11 z8)) - (UInt256.mulMod z1 z11 z8))) - (z11 * z1)) + (UInt256.gt z3 ((z0 + (z11 * z1)) + z3))) :: z1 :: z2 :: ((z0 + (z11 * z1)) + z3) :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } := by
  have g0 := reds2_1NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g1 := reds2_1NewP1_run s (z1) (z11) (z8) ((z11 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g2 := reds2_1NewP2_run s ((z11 * z1)) (((UInt256.gt (z11 * z1) (UInt256.mulMod z1 z11 z8)) - (UInt256.mulMod z1 z11 z8))) ((z11 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g3 := reds2_1NewP3_run s (((z0 + (z11 * z1)) + z3)) (((z0 + (z11 * z1)) + z3)) ((z0 + (z11 * z1))) (((UInt256.gt (z11 * z1) (UInt256.mulMod z1 z11 z8)) - (UInt256.mulMod z1 z11 z8))) ((z11 * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g4 := reds2_1NewP4_run s ((((UInt256.gt z0 (z0 + (z11 * z1))) - ((UInt256.gt (z11 * z1) (UInt256.mulMod z1 z11 z8)) - (UInt256.mulMod z1 z11 z8))) - (z11 * z1))) ((UInt256.gt z3 ((z0 + (z11 * z1)) + z3))) (z1) (z2) (((z0 + (z11 * z1)) + z3)) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [reds2_1New, List.append_assoc] using h

def reds2_1Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: rest => v0 :: v1 :: v3 :: v6 :: v7 :: v5 :: v4 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: rest
  | xs => xs

theorem run_reds2_1 (s : State) (c m ret v p3 p2 p1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1003) :
    runInstructions reds2_1New
      { s with pc := UInt256.ofNat 4364, stack := c :: m :: v :: p2 :: q0 :: p1 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4389, stack := (sCarry n2 m c p2 k) :: m :: v :: (mSum n2 m c p2) :: q0 :: p1 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := reds2_1Old_run s (c) (m) (ret) (v) (p3) (p2) (p1) (q0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  have hc := R4Runs.run_reds2 s c m ret v p3 p2 p1 q0 p4 k n0 n1 n2 n3 np rest hcap
  change runInstructions reds2_1Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg reds2_1Perm he
  simp only [reds2_1Perm] at hp
  have hn := reds2_1New_run s (c) (m) (v) (p2) (q0) (p1) (p3) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

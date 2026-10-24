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

def r1c2_1OldP0 : List Instr := [.push 2 2144, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r1c2_1OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c2_1OldP0 { s with pc := UInt256.ofNat 4421, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4429, stack := ((MachineState.readWord s.memory 2144) * x1) :: x7 :: (MachineState.readWord s.memory 2144) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [r1c2_1OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def r1c2_1OldP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r1c2_1OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1OldP1 { s with pc := UInt256.ofNat 4429, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4435, stack := (UInt256.gt x0 (UInt256.mulMod x4 x2 x1)) :: (UInt256.mulMod x4 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r1c2_1OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1OldP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨1, by decide⟩)]
theorem r1c2_1OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1OldP2 { s with pc := UInt256.ofNat 4435, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4441, stack := (x3 + x2) :: x6 :: (x3 + x2) :: (x0 - x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c2_1OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1OldP3 : List Instr := [.op .ADD, .op (.Swap ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT]
theorem r1c2_1OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1OldP3 { s with pc := UInt256.ofNat 4441, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4447, stack := (UInt256.gt x5 x2) :: x3 :: x4 :: (UInt256.lt (x0 + x1) x8) :: x6 :: x7 :: (x0 + x1) :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c2_1OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1OldP4 : List Instr := [.op .SUB, .op .SUB, .op .ADD]
theorem r1c2_1OldP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1OldP4 { s with pc := UInt256.ofNat 4447, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4450, stack := (((x0 - x1) - x2) + x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [r1c2_1OldP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1Old : List Instr := r1c2_1OldP0 ++ r1c2_1OldP1 ++ r1c2_1OldP2 ++ r1c2_1OldP3 ++ r1c2_1OldP4
theorem r1c2_1Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c2_1Old { s with pc := UInt256.ofNat 4421, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4450, stack := ((((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2144) * z1))) - ((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) - ((MachineState.readWord s.memory 2144) * z1)) + (UInt256.lt ((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z3) z3)) :: z1 :: z2 :: ((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z3) :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r1c2_1OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap hact
  have g1 := r1c2_1OldP1_run s (((MachineState.readWord s.memory 2144) * z1)) (z7) ((MachineState.readWord s.memory 2144)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r1c2_1OldP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) ((UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) (((MachineState.readWord s.memory 2144) * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r1c2_1OldP3_run s ((z0 + ((MachineState.readWord s.memory 2144) * z1))) (z3) ((z0 + ((MachineState.readWord s.memory 2144) * z1))) (((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) (((MachineState.readWord s.memory 2144) * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r1c2_1OldP4_run s ((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2144) * z1)))) (((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) (((MachineState.readWord s.memory 2144) * z1)) ((UInt256.lt ((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z3) z3)) (z1) (z2) (((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z3)) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r1c2_1Old, List.append_assoc] using h

def r1c2_1NewP0 : List Instr := [.push 2 2144, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r1c2_1NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c2_1NewP0 { s with pc := UInt256.ofNat 4265, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4273, stack := ((MachineState.readWord s.memory 2144) * x1) :: x7 :: (MachineState.readWord s.memory 2144) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [r1c2_1NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def r1c2_1NewP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r1c2_1NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1NewP1 { s with pc := UInt256.ofNat 4273, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4279, stack := (UInt256.gt x0 (UInt256.mulMod x4 x2 x1)) :: (UInt256.mulMod x4 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c2_1NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1NewP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩)]
theorem r1c2_1NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1NewP2 { s with pc := UInt256.ofNat 4279, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4285, stack := (x3 + x2) :: x5 :: (x3 + x2) :: (x0 - x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c2_1NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1NewP3 : List Instr := [.op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT]
theorem r1c2_1NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1NewP3 { s with pc := UInt256.ofNat 4285, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4291, stack := (UInt256.gt x5 x2) :: x3 :: x4 :: (UInt256.lt (x0 + x1) x7) :: x6 :: (x0 + x1) :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c2_1NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1NewP4 : List Instr := [.op .SUB, .op .SUB, .op .ADD]
theorem r1c2_1NewP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c2_1NewP4 { s with pc := UInt256.ofNat 4291, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4294, stack := (((x0 - x1) - x2) + x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r1c2_1NewP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c2_1New : List Instr := r1c2_1NewP0 ++ r1c2_1NewP1 ++ r1c2_1NewP2 ++ r1c2_1NewP3 ++ r1c2_1NewP4
theorem r1c2_1New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c2_1New { s with pc := UInt256.ofNat 4265, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4294, stack := ((((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2144) * z1))) - ((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) - ((MachineState.readWord s.memory 2144) * z1)) + (UInt256.lt ((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z2) z2)) :: z1 :: ((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z2) :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r1c2_1NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap hact
  have g1 := r1c2_1NewP1_run s (((MachineState.readWord s.memory 2144) * z1)) (z7) ((MachineState.readWord s.memory 2144)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r1c2_1NewP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) ((UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) (((MachineState.readWord s.memory 2144) * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r1c2_1NewP3_run s ((z0 + ((MachineState.readWord s.memory 2144) * z1))) (z2) ((z0 + ((MachineState.readWord s.memory 2144) * z1))) (((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) (((MachineState.readWord s.memory 2144) * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r1c2_1NewP4_run s ((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2144) * z1)))) (((UInt256.gt ((MachineState.readWord s.memory 2144) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2144) z7))) (((MachineState.readWord s.memory 2144) * z1)) ((UInt256.lt ((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z2) z2)) (z1) (((z0 + ((MachineState.readWord s.memory 2144) * z1)) + z2)) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r1c2_1New, List.append_assoc] using h

def r1c2_1Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest => v0 :: v1 :: v3 :: v4 :: v5 :: v2 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest
  | xs => xs

theorem run_r1c2_1 (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c2_1New
      { s with pc := UInt256.ofNat 4265, stack := c :: d :: p2 :: p1 :: p0 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4294, stack := (mCarry a2 d c p2 k) :: d :: (mSum a2 d c p2) :: p1 :: p0 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r1c2_1Old_run s (c) (d) (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r1c2 s c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a2 rest hcap ha2 hact
  change runInstructions r1c2_1Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r1c2_1Perm he
  simp only [r1c2_1Perm] at hp
  have hn := r1c2_1New_run s (c) (d) (p2) (p1) (p0) (p3) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

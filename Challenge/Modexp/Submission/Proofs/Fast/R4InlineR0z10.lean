import Challenge.Modexp.Submission.Proofs.Fast.R4Runs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
namespace Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast R4Math R4Runs R4Blocks

def r0z1_0OldP0 : List Instr := [.push 2 2176, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r0z1_0OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z1_0OldP0 { s with pc := UInt256.ofNat 4303, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: rest } =
    some { s with pc := UInt256.ofNat 4311, stack := ((MachineState.readWord s.memory 2176) * x2) :: x3 :: (MachineState.readWord s.memory 2176) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  simp [r0z1_0OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hl2176, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact]

def r0z1_0OldP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r0z1_0OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r0z1_0OldP1 { s with pc := UInt256.ofNat 4311, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4317, stack := (UInt256.gt x0 (UInt256.mulMod x5 x2 x1)) :: (UInt256.mulMod x5 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [r0z1_0OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r0z1_0OldP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩)]
theorem r0z1_0OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r0z1_0OldP2 { s with pc := UInt256.ofNat 4317, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4323, stack := x3 :: (x3 + x2) :: (x0 - x1) :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [r0z1_0OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r0z1_0OldP3 : List Instr := [.op .GT, .op .SUB, .op .SUB]
theorem r0z1_0OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r0z1_0OldP3 { s with pc := UInt256.ofNat 4323, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4326, stack := (((UInt256.gt x0 x1) - x2) - x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [r0z1_0OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r0z1_0Old : List Instr := r0z1_0OldP0 ++ r0z1_0OldP1 ++ r0z1_0OldP2 ++ r0z1_0OldP3
theorem r0z1_0Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z1_0Old { s with pc := UInt256.ofNat 4303, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: rest } =
    some { s with pc := UInt256.ofNat 4326, stack := (((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2176) * z2))) - ((UInt256.gt ((MachineState.readWord s.memory 2176) * z2) (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3)) - (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3))) - ((MachineState.readWord s.memory 2176) * z2)) :: (z0 + ((MachineState.readWord s.memory 2176) * z2)) :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: rest } := by
  have g0 := r0z1_0OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap hact
  have g1 := r0z1_0OldP1_run s (((MachineState.readWord s.memory 2176) * z2)) (z3) ((MachineState.readWord s.memory 2176)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap
  have g2 := r0z1_0OldP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2176) * z2) (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3))) ((UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3)) (((MachineState.readWord s.memory 2176) * z2)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap
  have g3 := r0z1_0OldP3_run s (z0) ((z0 + ((MachineState.readWord s.memory 2176) * z2))) (((UInt256.gt ((MachineState.readWord s.memory 2176) * z2) (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3)) - (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3))) (((MachineState.readWord s.memory 2176) * z2)) ((z0 + ((MachineState.readWord s.memory 2176) * z2))) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3)))
  simpa only [r0z1_0Old, List.append_assoc] using h

def r0z1_0NewP0 : List Instr := [.push 2 2176, .op .MLOAD, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r0z1_0NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z1_0NewP0 { s with pc := UInt256.ofNat 9021, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: rest } =
    some { s with pc := UInt256.ofNat 9029, stack := ((MachineState.readWord s.memory 2176) * x2) :: x3 :: (MachineState.readWord s.memory 2176) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  simp [r0z1_0NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hl2176, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact]

def r0z1_0NewP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r0z1_0NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r0z1_0NewP1 { s with pc := UInt256.ofNat 9029, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 9035, stack := (UInt256.gt x0 (UInt256.mulMod x5 x2 x1)) :: (UInt256.mulMod x5 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [r0z1_0NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r0z1_0NewP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩)]
theorem r0z1_0NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r0z1_0NewP2 { s with pc := UInt256.ofNat 9035, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 9041, stack := x3 :: (x3 + x2) :: (x0 - x1) :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [r0z1_0NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r0z1_0NewP3 : List Instr := [.op .GT, .op .SUB, .op .SUB]
theorem r0z1_0NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r0z1_0NewP3 { s with pc := UInt256.ofNat 9041, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 9044, stack := (((UInt256.gt x0 x1) - x2) - x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [r0z1_0NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r0z1_0New : List Instr := r0z1_0NewP0 ++ r0z1_0NewP1 ++ r0z1_0NewP2 ++ r0z1_0NewP3
theorem r0z1_0New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z1_0New { s with pc := UInt256.ofNat 9021, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: rest } =
    some { s with pc := UInt256.ofNat 9044, stack := (((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2176) * z2))) - ((UInt256.gt ((MachineState.readWord s.memory 2176) * z2) (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3)) - (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3))) - ((MachineState.readWord s.memory 2176) * z2)) :: (z0 + ((MachineState.readWord s.memory 2176) * z2)) :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: rest } := by
  have g0 := r0z1_0NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap hact
  have g1 := r0z1_0NewP1_run s (((MachineState.readWord s.memory 2176) * z2)) (z3) ((MachineState.readWord s.memory 2176)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap
  have g2 := r0z1_0NewP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2176) * z2) (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3))) ((UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3)) (((MachineState.readWord s.memory 2176) * z2)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap
  have g3 := r0z1_0NewP3_run s (z0) ((z0 + ((MachineState.readWord s.memory 2176) * z2))) (((UInt256.gt ((MachineState.readWord s.memory 2176) * z2) (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3)) - (UInt256.mulMod z2 (MachineState.readWord s.memory 2176) z3))) (((MachineState.readWord s.memory 2176) * z2)) ((z0 + ((MachineState.readWord s.memory 2176) * z2))) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3)))
  simpa only [r0z1_0New, List.append_assoc] using h

def r0z1_0Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: rest => v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: rest
  | xs => xs

theorem run_r0z1_0 (s : State) (c t0 d k n0 n1 n2 n3 np a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z1_0New
      { s with pc := UInt256.ofNat 9021, stack := c :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 9044, stack := (zCarry a1 d c k) :: (zSum a1 d c) :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r0z1_0Old_run s (c) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r0z1 s c t0 d k n0 n1 n2 n3 np a1 rest hcap ha1 hact
  change runInstructions r0z1_0Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r0z1_0Perm he
  simp only [r0z1_0Perm] at hp
  have hn := r0z1_0New_run s (c) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
#print axioms run_r0z1_0
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport

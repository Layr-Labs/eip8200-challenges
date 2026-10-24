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

def r1c3_1OldP0 : List Instr := [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r1c3_1OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c3_1OldP0 { s with pc := UInt256.ofNat 4450, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4458, stack := ((MachineState.readWord s.memory 2112) * x1) :: x7 :: (MachineState.readWord s.memory 2112) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  simp [r1c3_1OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2112, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def r1c3_1OldP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r1c3_1OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1OldP1 { s with pc := UInt256.ofNat 4458, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4464, stack := (UInt256.gt x0 (UInt256.mulMod x4 x2 x1)) :: (UInt256.mulMod x4 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r1c3_1OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1OldP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩)]
theorem r1c3_1OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1OldP2 { s with pc := UInt256.ofNat 4464, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4470, stack := (x3 + x2) :: x5 :: (x3 + x2) :: (x0 - x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c3_1OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1OldP3 : List Instr := [.op .ADD, .op (.Swap ⟨5, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .LT, .op (.Swap ⟨3, by decide⟩), .op .GT]
theorem r1c3_1OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1OldP3 { s with pc := UInt256.ofNat 4470, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4476, stack := (UInt256.gt x5 x2) :: x3 :: x4 :: (UInt256.lt (x0 + x1) x7) :: x6 :: (x0 + x1) :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c3_1OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1OldP4 : List Instr := [.op .SUB, .op .SUB, .op .ADD]
theorem r1c3_1OldP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1OldP4 { s with pc := UInt256.ofNat 4476, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4479, stack := (((x0 - x1) - x2) + x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [r1c3_1OldP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1Old : List Instr := r1c3_1OldP0 ++ r1c3_1OldP1 ++ r1c3_1OldP2 ++ r1c3_1OldP3 ++ r1c3_1OldP4
theorem r1c3_1Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c3_1Old { s with pc := UInt256.ofNat 4450, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4479, stack := ((((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2112) * z1))) - ((UInt256.gt ((MachineState.readWord s.memory 2112) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7))) - ((MachineState.readWord s.memory 2112) * z1)) + (UInt256.lt ((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z2) z2)) :: z1 :: ((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z2) :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r1c3_1OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap hact
  have g1 := r1c3_1OldP1_run s (((MachineState.readWord s.memory 2112) * z1)) (z7) ((MachineState.readWord s.memory 2112)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r1c3_1OldP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2112) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7))) ((UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) (((MachineState.readWord s.memory 2112) * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r1c3_1OldP3_run s ((z0 + ((MachineState.readWord s.memory 2112) * z1))) (z2) ((z0 + ((MachineState.readWord s.memory 2112) * z1))) (((UInt256.gt ((MachineState.readWord s.memory 2112) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7))) (((MachineState.readWord s.memory 2112) * z1)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r1c3_1OldP4_run s ((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2112) * z1)))) (((UInt256.gt ((MachineState.readWord s.memory 2112) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7))) (((MachineState.readWord s.memory 2112) * z1)) ((UInt256.lt ((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z2) z2)) (z1) (((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z2)) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r1c3_1Old, List.append_assoc] using h

def r1c3_1NewP0 : List Instr := [.push 2 2112, .op .MLOAD, .op (.Dup ⟨8, by decide⟩), .op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨1, by decide⟩)]
theorem r1c3_1NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c3_1NewP0 { s with pc := UInt256.ofNat 4294, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4302, stack := (MachineState.readWord s.memory 2112) :: x1 :: (MachineState.readWord s.memory 2112) :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  simp [r1c3_1NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2112, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def r1c3_1NewP1 : List Instr := [.op .MUL, .op (.Swap ⟨2, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩)]
theorem r1c3_1NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1NewP1 { s with pc := UInt256.ofNat 4302, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } =
    some { s with pc := UInt256.ofNat 4308, stack := (x0 * x1) :: (UInt256.mulMod x5 x2 x3) :: (UInt256.mulMod x5 x2 x3) :: (x0 * x1) :: x4 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c3_1NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1NewP2 : List Instr := [.op .GT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩)]
theorem r1c3_1NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1NewP2 { s with pc := UInt256.ofNat 4308, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4314, stack := x8 :: (x4 + x3) :: ((UInt256.gt x0 x1) - x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r1c3_1NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1NewP3 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Swap ⟨7, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op .LT, .op (.Swap ⟨3, by decide⟩)]
theorem r1c3_1NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1NewP3 { s with pc := UInt256.ofNat 4314, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4320, stack := x4 :: x1 :: x2 :: x3 :: (UInt256.lt (x1 + x0) x8) :: x5 :: x6 :: x7 :: (x1 + x0) :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r1c3_1NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1NewP4 : List Instr := [.op .GT, .op .SUB, .op .SUB, .op .ADD]
theorem r1c3_1NewP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r1c3_1NewP4 { s with pc := UInt256.ofNat 4320, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4324, stack := ((((UInt256.gt x0 x1) - x2) - x3) + x4) :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r1c3_1NewP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r1c3_1New : List Instr := r1c3_1NewP0 ++ r1c3_1NewP1 ++ r1c3_1NewP2 ++ r1c3_1NewP3 ++ r1c3_1NewP4
theorem r1c3_1New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c3_1New { s with pc := UInt256.ofNat 4294, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4324, stack := ((((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2112) * z1))) - ((UInt256.gt ((MachineState.readWord s.memory 2112) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7))) - ((MachineState.readWord s.memory 2112) * z1)) + (UInt256.lt ((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z5) z5)) :: z2 :: z3 :: z4 :: ((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z5) :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r1c3_1NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap hact
  have g1 := r1c3_1NewP1_run s ((MachineState.readWord s.memory 2112)) (z1) ((MachineState.readWord s.memory 2112)) (z7) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r1c3_1NewP2_run s (((MachineState.readWord s.memory 2112) * z1)) ((UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) ((UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) (((MachineState.readWord s.memory 2112) * z1)) (z0) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r1c3_1NewP3_run s (z5) ((z0 + ((MachineState.readWord s.memory 2112) * z1))) (((UInt256.gt ((MachineState.readWord s.memory 2112) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7))) (((MachineState.readWord s.memory 2112) * z1)) (z0) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r1c3_1NewP4_run s (z0) ((z0 + ((MachineState.readWord s.memory 2112) * z1))) (((UInt256.gt ((MachineState.readWord s.memory 2112) * z1) (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7)) - (UInt256.mulMod z1 (MachineState.readWord s.memory 2112) z7))) (((MachineState.readWord s.memory 2112) * z1)) ((UInt256.lt ((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z5) z5)) (z2) (z3) (z4) (((z0 + ((MachineState.readWord s.memory 2112) * z1)) + z5)) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r1c3_1New, List.append_assoc] using h

def r1c3_1Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest => v0 :: v3 :: v4 :: v5 :: v2 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest
  | xs => xs

theorem run_r1c3_1 (s : State) (c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1c3_1New
      { s with pc := UInt256.ofNat 4294, stack := c :: d :: p2 :: p1 :: p0 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4324, stack := (mCarry a3 d c p3 k) :: p2 :: p1 :: p0 :: (mSum a3 d c p3) :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r1c3_1Old_run s (c) (d) (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r1c3 s c d p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 rest hcap ha3 hact
  change runInstructions r1c3_1Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r1c3_1Perm he
  simp only [r1c3_1Perm] at hp
  have hn := r1c3_1New_run s (c) (d) (p2) (p1) (p0) (p3) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

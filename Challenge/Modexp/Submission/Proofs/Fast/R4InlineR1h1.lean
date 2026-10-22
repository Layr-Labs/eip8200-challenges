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

def r1h_1OldP0 : List Instr := [.op .JUMPDEST, .push 2 2176, .op .MLOAD, .push 2 2208, .op .MLOAD, .push 0 0]
theorem r1h_1OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1h_1OldP0 { s with pc := UInt256.ofNat 4382, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 4392, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2208) :: (MachineState.readWord s.memory 2176) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
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
  have hc14 : rest.length + 14 < 1024 := by omega
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  have hl2208 : (2208 : UInt256).toNat = 2208 := rfl
  simp [r1h_1OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hl2176, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact, hl2208, Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact] <;> rfl

def r1h_1Old : List Instr := r1h_1OldP0
theorem r1h_1Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1h_1Old { s with pc := UInt256.ofNat 4382, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 4392, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2208) :: (MachineState.readWord s.memory 2176) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r1h_1OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have h := g0
  simpa only [r1h_1Old, List.append_assoc] using h

def r1h_1NewP0 : List Instr := [.push 2 2176, .op .MLOAD, .push 2 2208, .op .MLOAD, .push 0 0]
theorem r1h_1NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1h_1NewP0 { s with pc := UInt256.ofNat 9188, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 9197, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2208) :: (MachineState.readWord s.memory 2176) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
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
  have hc14 : rest.length + 14 < 1024 := by omega
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  have hl2208 : (2208 : UInt256).toNat = 2208 := rfl
  simp [r1h_1NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hl2176, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact, hl2208, Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact] <;> rfl

def r1h_1New : List Instr := r1h_1NewP0
theorem r1h_1New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1h_1New { s with pc := UInt256.ofNat 9188, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 9197, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2208) :: (MachineState.readWord s.memory 2176) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r1h_1NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have h := g0
  simpa only [r1h_1New, List.append_assoc] using h

def r1h_1Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: rest => v0 :: v1 :: v2 :: v4 :: v5 :: v6 :: v3 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: rest
  | xs => xs

theorem run_r1h_1 (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a1 a0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (ha0 : MachineState.readWord s.memory 2208 = a0)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r1h_1New
      { s with pc := UInt256.ofNat 9188, stack := p2 :: p1 :: p0 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 9197, stack := (⟨0⟩ : UInt256) :: a0 :: a1 :: p2 :: p1 :: p0 :: p3 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r1h_1Old_run s (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r1h s p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a1 a0 rest hcap ha1 ha0 hact
  change runInstructions r1h_1Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r1h_1Perm he
  simp only [r1h_1Perm] at hp
  have hn := r1h_1New_run s (p2) (p1) (p0) (p3) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
#print axioms run_r1h_1
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport

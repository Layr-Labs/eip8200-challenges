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

def r3h_3OldP0 : List Instr := [.op .JUMPDEST, .push 2 2112, .op .MLOAD, .push 2 2144, .op .MLOAD, .push 0 0]
theorem r3h_3OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r3h_3OldP0 { s with pc := UInt256.ofNat 4577, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 4587, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2144) :: (MachineState.readWord s.memory 2112) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
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
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [r3h_3OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hl2112, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact] <;> rfl

def r3h_3Old : List Instr := r3h_3OldP0
theorem r3h_3Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r3h_3Old { s with pc := UInt256.ofNat 4577, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 4587, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2144) :: (MachineState.readWord s.memory 2112) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r3h_3OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have h := g0
  simpa only [r3h_3Old, List.append_assoc] using h

def r3h_3NewP0 : List Instr := [.op .JUMPDEST, .push 2 2112, .op .MLOAD, .push 2 2144, .op .MLOAD, .push 0 0]
theorem r3h_3NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r3h_3NewP0 { s with pc := UInt256.ofNat 9569, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 9579, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2144) :: (MachineState.readWord s.memory 2112) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
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
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [r3h_3NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hl2112, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact] <;> rfl

def r3h_3New : List Instr := r3h_3NewP0
theorem r3h_3New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r3h_3New { s with pc := UInt256.ofNat 9569, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 9579, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2144) :: (MachineState.readWord s.memory 2112) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r3h_3NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have h := g0
  simpa only [r3h_3New, List.append_assoc] using h

def r3h_3Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: rest => v0 :: v1 :: v2 :: v6 :: v3 :: v4 :: v5 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: rest
  | xs => xs

theorem run_r3h_3 (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r3h_3New
      { s with pc := UInt256.ofNat 9569, stack := p0 :: p3 :: p2 :: p1 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 9579, stack := (⟨0⟩ : UInt256) :: a2 :: a3 :: p0 :: p3 :: p2 :: p1 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r3h_3Old_run s (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r3h s p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a3 a2 rest hcap ha3 ha2 hact
  change runInstructions r3h_3Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r3h_3Perm he
  simp only [r3h_3Perm] at hp
  have hn := r3h_3New_run s (p0) (p3) (p2) (p1) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
#print axioms run_r3h_3
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport

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

def r2h_2OldP0 : List Instr := [.op .JUMPDEST, .push 2 2144, .op .MLOAD, .push 2 2176, .op .MLOAD, .push 0 0]
theorem r2h_2OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r2h_2OldP0 { s with pc := UInt256.ofNat 4494, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 4504, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2176) :: (MachineState.readWord s.memory 2144) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  simp [r2h_2OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact, hl2176, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact] <;> rfl

def r2h_2Old : List Instr := r2h_2OldP0
theorem r2h_2Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r2h_2Old { s with pc := UInt256.ofNat 4494, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 4504, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2176) :: (MachineState.readWord s.memory 2144) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r2h_2OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have h := g0
  simpa only [r2h_2Old, List.append_assoc] using h

def r2h_2NewP0 : List Instr := [.push 2 2144, .op .MLOAD, .push 2 2176, .op .MLOAD, .push 0 0]
theorem r2h_2NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r2h_2NewP0 { s with pc := UInt256.ofNat 4424, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 4433, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2176) :: (MachineState.readWord s.memory 2144) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  simp [r2h_2NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact, hl2176, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact] <;> rfl

def r2h_2New : List Instr := r2h_2NewP0
theorem r2h_2New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r2h_2New { s with pc := UInt256.ofNat 4424, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 4433, stack := (0 : UInt256) :: (MachineState.readWord s.memory 2176) :: (MachineState.readWord s.memory 2144) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r2h_2NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have h := g0
  simpa only [r2h_2New, List.append_assoc] using h

def r2h_2Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: rest => v0 :: v1 :: v2 :: v5 :: v6 :: v3 :: v4 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: rest
  | xs => xs

theorem run_r2h_2 (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a2 a1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (ha1 : MachineState.readWord s.memory 2176 = a1)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r2h_2New
      { s with pc := UInt256.ofNat 4424, stack := p1 :: p0 :: p3 :: p2 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4433, stack := (⟨0⟩ : UInt256) :: a1 :: a2 :: p1 :: p0 :: p3 :: p2 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r2h_2Old_run s (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r2h s p3 p2 p1 p0 p4 k n0 n1 n2 n3 np a2 a1 rest hcap ha2 ha1 hact
  change runInstructions r2h_2Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r2h_2Perm he
  simp only [r2h_2Perm] at hp
  have hn := r2h_2New_run s (p1) (p0) (p3) (p2) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

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

def r0z2_0OldP0 : List Instr := [.push 2 2144, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r0z2_0OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z2_0OldP0 { s with pc := UInt256.ofNat 4326, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest } =
    some { s with pc := UInt256.ofNat 4334, stack := ((MachineState.readWord s.memory 2144) * x3) :: x4 :: (MachineState.readWord s.memory 2144) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [r0z2_0OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def r0z2_0OldP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r0z2_0OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0z2_0OldP1 { s with pc := UInt256.ofNat 4334, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4340, stack := (UInt256.gt x0 (UInt256.mulMod x6 x2 x1)) :: (UInt256.mulMod x6 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r0z2_0OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z2_0OldP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩)]
theorem r0z2_0OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0z2_0OldP2 { s with pc := UInt256.ofNat 4340, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4346, stack := x3 :: (x3 + x2) :: (x0 - x1) :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r0z2_0OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z2_0OldP3 : List Instr := [.op .GT, .op .SUB, .op .SUB]
theorem r0z2_0OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0z2_0OldP3 { s with pc := UInt256.ofNat 4346, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4349, stack := (((UInt256.gt x0 x1) - x2) - x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r0z2_0OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z2_0Old : List Instr := r0z2_0OldP0 ++ r0z2_0OldP1 ++ r0z2_0OldP2 ++ r0z2_0OldP3
theorem r0z2_0Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z2_0Old { s with pc := UInt256.ofNat 4326, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: rest } =
    some { s with pc := UInt256.ofNat 4349, stack := (((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2144) * z3))) - ((UInt256.gt ((MachineState.readWord s.memory 2144) * z3) (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4)) - (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4))) - ((MachineState.readWord s.memory 2144) * z3)) :: (z0 + ((MachineState.readWord s.memory 2144) * z3)) :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: rest } := by
  have g0 := r0z2_0OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap hact
  have g1 := r0z2_0OldP1_run s (((MachineState.readWord s.memory 2144) * z3)) (z4) ((MachineState.readWord s.memory 2144)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap
  have g2 := r0z2_0OldP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2144) * z3) (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4))) ((UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4)) (((MachineState.readWord s.memory 2144) * z3)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap
  have g3 := r0z2_0OldP3_run s (z0) ((z0 + ((MachineState.readWord s.memory 2144) * z3))) (((UInt256.gt ((MachineState.readWord s.memory 2144) * z3) (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4)) - (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4))) (((MachineState.readWord s.memory 2144) * z3)) ((z0 + ((MachineState.readWord s.memory 2144) * z3))) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3)))
  simpa only [r0z2_0Old, List.append_assoc] using h

def r0z2_0NewP0 : List Instr := [.push 2 2144, .op .MLOAD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r0z2_0NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z2_0NewP0 { s with pc := UInt256.ofNat 4083, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest } =
    some { s with pc := UInt256.ofNat 4091, stack := ((MachineState.readWord s.memory 2144) * x3) :: x4 :: (MachineState.readWord s.memory 2144) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [r0z2_0NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2144, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def r0z2_0NewP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r0z2_0NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0z2_0NewP1 { s with pc := UInt256.ofNat 4091, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4097, stack := (UInt256.gt x0 (UInt256.mulMod x6 x2 x1)) :: (UInt256.mulMod x6 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r0z2_0NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z2_0NewP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩)]
theorem r0z2_0NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0z2_0NewP2 { s with pc := UInt256.ofNat 4097, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4103, stack := x3 :: (x3 + x2) :: (x0 - x1) :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r0z2_0NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z2_0NewP3 : List Instr := [.op .GT, .op .SUB, .op .SUB]
theorem r0z2_0NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0z2_0NewP3 { s with pc := UInt256.ofNat 4103, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4106, stack := (((UInt256.gt x0 x1) - x2) - x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r0z2_0NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z2_0New : List Instr := r0z2_0NewP0 ++ r0z2_0NewP1 ++ r0z2_0NewP2 ++ r0z2_0NewP3
theorem r0z2_0New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z2_0New { s with pc := UInt256.ofNat 4083, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: rest } =
    some { s with pc := UInt256.ofNat 4106, stack := (((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2144) * z3))) - ((UInt256.gt ((MachineState.readWord s.memory 2144) * z3) (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4)) - (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4))) - ((MachineState.readWord s.memory 2144) * z3)) :: (z0 + ((MachineState.readWord s.memory 2144) * z3)) :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: rest } := by
  have g0 := r0z2_0NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap hact
  have g1 := r0z2_0NewP1_run s (((MachineState.readWord s.memory 2144) * z3)) (z4) ((MachineState.readWord s.memory 2144)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap
  have g2 := r0z2_0NewP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2144) * z3) (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4))) ((UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4)) (((MachineState.readWord s.memory 2144) * z3)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap
  have g3 := r0z2_0NewP3_run s (z0) ((z0 + ((MachineState.readWord s.memory 2144) * z3))) (((UInt256.gt ((MachineState.readWord s.memory 2144) * z3) (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4)) - (UInt256.mulMod z3 (MachineState.readWord s.memory 2144) z4))) (((MachineState.readWord s.memory 2144) * z3)) ((z0 + ((MachineState.readWord s.memory 2144) * z3))) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3)))
  simpa only [r0z2_0New, List.append_assoc] using h

def r0z2_0Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: rest => v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: rest
  | xs => xs

theorem run_r0z2_0 (s : State) (c t1 t0 d k n0 n1 n2 n3 np a2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (ha2 : MachineState.readWord s.memory 2144 = a2)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z2_0New
      { s with pc := UInt256.ofNat 4083, stack := c :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4106, stack := (zCarry a2 d c k) :: (zSum a2 d c) :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r0z2_0Old_run s (c) (t1) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r0z2 s c t1 t0 d k n0 n1 n2 n3 np a2 rest hcap ha2 hact
  change runInstructions r0z2_0Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r0z2_0Perm he
  simp only [r0z2_0Perm] at hp
  have hn := r0z2_0New_run s (c) (t1) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

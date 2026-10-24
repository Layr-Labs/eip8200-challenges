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

def r0z3_0OldP0 : List Instr := [.push 2 2112, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r0z3_0OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z3_0OldP0 { s with pc := UInt256.ofNat 4349, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 4357, stack := ((MachineState.readWord s.memory 2112) * x4) :: x5 :: (MachineState.readWord s.memory 2112) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  simp [r0z3_0OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2112, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def r0z3_0OldP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r0z3_0OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions r0z3_0OldP1 { s with pc := UInt256.ofNat 4357, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4363, stack := (UInt256.gt x0 (UInt256.mulMod x7 x2 x1)) :: (UInt256.mulMod x7 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r0z3_0OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z3_0OldP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩)]
theorem r0z3_0OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions r0z3_0OldP2 { s with pc := UInt256.ofNat 4363, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4369, stack := x3 :: (x3 + x2) :: (x0 - x1) :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r0z3_0OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z3_0OldP3 : List Instr := [.op .GT, .op .SUB, .op .SUB]
theorem r0z3_0OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions r0z3_0OldP3 { s with pc := UInt256.ofNat 4369, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4372, stack := (((UInt256.gt x0 x1) - x2) - x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r0z3_0OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z3_0Old : List Instr := r0z3_0OldP0 ++ r0z3_0OldP1 ++ r0z3_0OldP2 ++ r0z3_0OldP3
theorem r0z3_0Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z3_0Old { s with pc := UInt256.ofNat 4349, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 4372, stack := (((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2112) * z4))) - ((UInt256.gt ((MachineState.readWord s.memory 2112) * z4) (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5)) - (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5))) - ((MachineState.readWord s.memory 2112) * z4)) :: (z0 + ((MachineState.readWord s.memory 2112) * z4)) :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r0z3_0OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have g1 := r0z3_0OldP1_run s (((MachineState.readWord s.memory 2112) * z4)) (z5) ((MachineState.readWord s.memory 2112)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap
  have g2 := r0z3_0OldP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2112) * z4) (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5))) ((UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5)) (((MachineState.readWord s.memory 2112) * z4)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap
  have g3 := r0z3_0OldP3_run s (z0) ((z0 + ((MachineState.readWord s.memory 2112) * z4))) (((UInt256.gt ((MachineState.readWord s.memory 2112) * z4) (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5)) - (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5))) (((MachineState.readWord s.memory 2112) * z4)) ((z0 + ((MachineState.readWord s.memory 2112) * z4))) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3)))
  simpa only [r0z3_0Old, List.append_assoc] using h

def r0z3_0NewP0 : List Instr := [.push 2 2112, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL]
theorem r0z3_0NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z3_0NewP0 { s with pc := UInt256.ofNat 4106, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } =
    some { s with pc := UInt256.ofNat 4114, stack := ((MachineState.readWord s.memory 2112) * x4) :: x5 :: (MachineState.readWord s.memory 2112) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  simp [r0z3_0NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc, hl2112, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact]

def r0z3_0NewP1 : List Instr := [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .MULMOD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT]
theorem r0z3_0NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions r0z3_0NewP1 { s with pc := UInt256.ofNat 4114, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4120, stack := (UInt256.gt x0 (UInt256.mulMod x7 x2 x1)) :: (UInt256.mulMod x7 x2 x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r0z3_0NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z3_0NewP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩)]
theorem r0z3_0NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions r0z3_0NewP2 { s with pc := UInt256.ofNat 4120, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4126, stack := x3 :: (x3 + x2) :: (x0 - x1) :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r0z3_0NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z3_0NewP3 : List Instr := [.op .GT, .op .SUB, .op .SUB]
theorem r0z3_0NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions r0z3_0NewP3 { s with pc := UInt256.ofNat 4126, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4129, stack := (((UInt256.gt x0 x1) - x2) - x3) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r0z3_0NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r0z3_0New : List Instr := r0z3_0NewP0 ++ r0z3_0NewP1 ++ r0z3_0NewP2 ++ r0z3_0NewP3
theorem r0z3_0New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z3_0New { s with pc := UInt256.ofNat 4106, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } =
    some { s with pc := UInt256.ofNat 4129, stack := (((UInt256.gt z0 (z0 + ((MachineState.readWord s.memory 2112) * z4))) - ((UInt256.gt ((MachineState.readWord s.memory 2112) * z4) (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5)) - (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5))) - ((MachineState.readWord s.memory 2112) * z4)) :: (z0 + ((MachineState.readWord s.memory 2112) * z4)) :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: rest } := by
  have g0 := r0z3_0NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap hact
  have g1 := r0z3_0NewP1_run s (((MachineState.readWord s.memory 2112) * z4)) (z5) ((MachineState.readWord s.memory 2112)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap
  have g2 := r0z3_0NewP2_run s ((UInt256.gt ((MachineState.readWord s.memory 2112) * z4) (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5))) ((UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5)) (((MachineState.readWord s.memory 2112) * z4)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap
  have g3 := r0z3_0NewP3_run s (z0) ((z0 + ((MachineState.readWord s.memory 2112) * z4))) (((UInt256.gt ((MachineState.readWord s.memory 2112) * z4) (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5)) - (UInt256.mulMod z4 (MachineState.readWord s.memory 2112) z5))) (((MachineState.readWord s.memory 2112) * z4)) ((z0 + ((MachineState.readWord s.memory 2112) * z4))) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3)))
  simpa only [r0z3_0New, List.append_assoc] using h

def r0z3_0Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: rest => v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: rest
  | xs => xs

theorem run_r0z3_0 (s : State) (c t2 t1 t0 d k n0 n1 n2 n3 np a3 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (ha3 : MachineState.readWord s.memory 2112 = a3)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions r0z3_0New
      { s with pc := UInt256.ofNat 4106, stack := c :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4129, stack := (zCarry a3 d c k) :: (zSum a3 d c) :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r0z3_0Old_run s (c) (t2) (t1) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  have hc := R4Runs.run_r0z3 s c t2 t1 t0 d k n0 n1 n2 n3 np a3 rest hcap ha3 hact
  change runInstructions r0z3_0Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r0z3_0Perm he
  simp only [r0z3_0Perm] at hp
  have hn := r0z3_0New_run s (c) (t2) (t1) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap hact
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

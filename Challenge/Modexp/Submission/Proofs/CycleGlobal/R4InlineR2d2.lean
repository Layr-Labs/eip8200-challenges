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

def r2d_2OldP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op (.Dup ⟨8, by decide⟩)]
theorem r2d_2OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2OldP0 { s with pc := UInt256.ofNat 4505, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4511, stack := x7 :: (UInt256.gt x1 (x1 + x0)) :: (x1 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r2d_2OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2OldP1 : List Instr := [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem r2d_2OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2OldP1 { s with pc := UInt256.ofNat 4511, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4517, stack := x2 :: x3 :: x3 :: x0 :: x1 :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r2d_2OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2OldP2 : List Instr := [.op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩)]
theorem r2d_2OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2OldP2 { s with pc := UInt256.ofNat 4517, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4523, stack := ((UInt256.mulMod x5 x2 x3) - x4) :: (x0 * x1) :: ((UInt256.mulMod x5 x2 x3) - x4) :: (x0 * x1) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r2d_2OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2OldP3 : List Instr := [.op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩)]
theorem r2d_2OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2OldP3 { s with pc := UInt256.ofNat 4523, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4529, stack := x6 :: ((UInt256.lt x0 x1) - x2) :: x3 :: x4 :: x5 :: (x6 + x3) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [r2d_2OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2OldP4 : List Instr := [.op (.Dup ⟨5, by decide⟩), .op .LT, .op .SUB, .op .SUB]
theorem r2d_2OldP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2OldP4 { s with pc := UInt256.ofNat 4529, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4533, stack := (((UInt256.lt x5 x0) - x1) - x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [r2d_2OldP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2Old : List Instr := r2d_2OldP0 ++ r2d_2OldP1 ++ r2d_2OldP2 ++ r2d_2OldP3 ++ r2d_2OldP4
theorem r2d_2Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2Old { s with pc := UInt256.ofNat 4505, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4533, stack := (((UInt256.lt (z3 + ((z1 + z0) * z1)) z3) - ((UInt256.lt ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))) ((z1 + z0) * z1)) - ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))))) - ((z1 + z0) * z1)) :: (z1 + (z1 + z0)) :: z2 :: (z3 + ((z1 + z0) * z1)) :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r2d_2OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g1 := r2d_2OldP1_run s (z7) ((UInt256.gt z1 (z1 + z0))) ((z1 + z0)) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r2d_2OldP2_run s ((z1 + z0)) (z1) (z1) (z7) ((UInt256.gt z1 (z1 + z0))) ((z1 + z0)) ((z1 + (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r2d_2OldP3_run s (((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0)))) (((z1 + z0) * z1)) (((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0)))) (((z1 + z0) * z1)) ((z1 + (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r2d_2OldP4_run s (z3) (((UInt256.lt ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))) ((z1 + z0) * z1)) - ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))))) (((z1 + z0) * z1)) ((z1 + (z1 + z0))) (z2) ((z3 + ((z1 + z0) * z1))) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r2d_2Old, List.append_assoc] using h

def r2d_2NewP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op (.Dup ⟨8, by decide⟩)]
theorem r2d_2NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2NewP0 { s with pc := UInt256.ofNat 4434, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4440, stack := x7 :: (UInt256.gt x1 (x1 + x0)) :: (x1 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [r2d_2NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2NewP1 : List Instr := [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem r2d_2NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2NewP1 { s with pc := UInt256.ofNat 4440, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4446, stack := x2 :: x3 :: x3 :: x0 :: x1 :: x2 :: (x3 + x2) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [r2d_2NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2NewP2 : List Instr := [.op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩)]
theorem r2d_2NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2NewP2 { s with pc := UInt256.ofNat 4446, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } =
    some { s with pc := UInt256.ofNat 4452, stack := ((UInt256.mulMod x5 x2 x3) - x4) :: (x0 * x1) :: ((UInt256.mulMod x5 x2 x3) - x4) :: (x0 * x1) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [r2d_2NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2NewP3 : List Instr := [.op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨7, by decide⟩), .op .ADD, .op (.Swap ⟨6, by decide⟩)]
theorem r2d_2NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2NewP3 { s with pc := UInt256.ofNat 4452, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4458, stack := x8 :: ((UInt256.lt x0 x1) - x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: (x8 + x3) :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r2d_2NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2NewP4 : List Instr := [.op (.Dup ⟨7, by decide⟩), .op .LT, .op .SUB, .op .SUB]
theorem r2d_2NewP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2NewP4 { s with pc := UInt256.ofNat 4458, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4462, stack := (((UInt256.lt x7 x0) - x1) - x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r2d_2NewP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r2d_2New : List Instr := r2d_2NewP0 ++ r2d_2NewP1 ++ r2d_2NewP2 ++ r2d_2NewP3 ++ r2d_2NewP4
theorem r2d_2New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1004) :
    runInstructions r2d_2New { s with pc := UInt256.ofNat 4434, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4462, stack := (((UInt256.lt (z5 + ((z1 + z0) * z1)) z5) - ((UInt256.lt ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))) ((z1 + z0) * z1)) - ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))))) - ((z1 + z0) * z1)) :: (z1 + (z1 + z0)) :: z2 :: z3 :: z4 :: (z5 + ((z1 + z0) * z1)) :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r2d_2NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g1 := r2d_2NewP1_run s (z7) ((UInt256.gt z1 (z1 + z0))) ((z1 + z0)) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r2d_2NewP2_run s ((z1 + z0)) (z1) (z1) (z7) ((UInt256.gt z1 (z1 + z0))) ((z1 + z0)) ((z1 + (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r2d_2NewP3_run s (((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0)))) (((z1 + z0) * z1)) (((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0)))) (((z1 + z0) * z1)) ((z1 + (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r2d_2NewP4_run s (z5) (((UInt256.lt ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))) ((z1 + z0) * z1)) - ((UInt256.mulMod (z1 + z0) z1 z7) - (UInt256.gt z1 (z1 + z0))))) (((z1 + z0) * z1)) ((z1 + (z1 + z0))) (z2) (z3) (z4) ((z5 + ((z1 + z0) * z1))) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r2d_2New, List.append_assoc] using h

def r2d_2Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest => v0 :: v1 :: v4 :: v5 :: v2 :: v3 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest
  | xs => xs

theorem run_r2d_2 (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1004) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions r2d_2New
      { s with pc := UInt256.ofNat 4434, stack := tb :: a :: p1 :: p0 :: p3 :: p2 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4462, stack := (mCarry a a (a * tb) p2 k) :: ((a + a) + tb) :: p1 :: p0 :: p3 :: (mSum a a (a * tb) p2) :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }  := by
  have ho := r2d_2Old_run s (tb) (a) (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  have hc := R4Runs.run_r2d s tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np rest hcap hk htb
  change runInstructions r2d_2Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r2d_2Perm he
  simp only [r2d_2Perm] at hp
  have hn := r2d_2New_run s (tb) (a) (p1) (p0) (p3) (p2) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

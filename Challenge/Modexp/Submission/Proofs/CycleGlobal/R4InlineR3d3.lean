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

def r3d_3OldP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem r3d_3OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3OldP0 { s with pc := UInt256.ofNat 4588, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4594, stack := x1 :: (x1 + x0) :: (x1 + x0) :: x7 :: (x1 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r3d_3OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3OldP1 : List Instr := [.op .GT, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD]
theorem r3d_3OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3OldP1 { s with pc := UInt256.ofNat 4594, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } =
    some { s with pc := UInt256.ofNat 4600, stack := (UInt256.mulMod x5 x2 x3) :: (UInt256.gt x0 x1) :: (x5 * x4) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [r3d_3OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3OldP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]
theorem r3d_3OldP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3OldP2 { s with pc := UInt256.ofNat 4600, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4606, stack := x2 :: ((UInt256.lt (x0 - x1) x2) - (x0 - x1)) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r3d_3OldP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3OldP3 : List Instr := [.op (.Dup ⟨3, by decide⟩), .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .LT, .op .SUB]
theorem r3d_3OldP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3OldP3 { s with pc := UInt256.ofNat 4606, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4612, stack := ((UInt256.lt (x3 + x0) x3) - x1) :: x2 :: (x3 + x0) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [r3d_3OldP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3OldP4 : List Instr := [.op .SUB]
theorem r3d_3OldP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3OldP4 { s with pc := UInt256.ofNat 4612, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4613, stack := (x0 - x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 13) : rest.length + j < 1024 := by omega
  simp [r3d_3OldP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3Old : List Instr := r3d_3OldP0 ++ r3d_3OldP1 ++ r3d_3OldP2 ++ r3d_3OldP3 ++ r3d_3OldP4
theorem r3d_3Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3Old { s with pc := UInt256.ofNat 4588, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4613, stack := (((UInt256.lt (z2 + (z1 * (z1 + z0))) z2) - ((UInt256.lt ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))) (z1 * (z1 + z0))) - ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))))) - (z1 * (z1 + z0))) :: (z2 + (z1 * (z1 + z0))) :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r3d_3OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g1 := r3d_3OldP1_run s (z1) ((z1 + z0)) ((z1 + z0)) (z7) ((z1 + z0)) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r3d_3OldP2_run s ((UInt256.mulMod z1 (z1 + z0) z7)) ((UInt256.gt z1 (z1 + z0))) ((z1 * (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r3d_3OldP3_run s ((z1 * (z1 + z0))) (((UInt256.lt ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))) (z1 * (z1 + z0))) - ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))))) ((z1 * (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r3d_3OldP4_run s (((UInt256.lt (z2 + (z1 * (z1 + z0))) z2) - ((UInt256.lt ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))) (z1 * (z1 + z0))) - ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0)))))) ((z1 * (z1 + z0))) ((z2 + (z1 * (z1 + z0)))) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r3d_3Old, List.append_assoc] using h

def r3d_3NewP0 : List Instr := [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨4, by decide⟩)]
theorem r3d_3NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3NewP0 { s with pc := UInt256.ofNat 4602, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4608, stack := x1 :: (x1 + x0) :: (x1 + x0) :: x7 :: (x1 + x0) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r3d_3NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3NewP1 : List Instr := [.op .GT, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MUL, .op (.Swap ⟨3, by decide⟩), .op .MULMOD]
theorem r3d_3NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3NewP1 { s with pc := UInt256.ofNat 4608, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } =
    some { s with pc := UInt256.ofNat 4614, stack := (UInt256.mulMod x5 x2 x3) :: (UInt256.gt x0 x1) :: (x5 * x4) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [r3d_3NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3NewP2 : List Instr := [.op .SUB, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩)]
theorem r3d_3NewP2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3NewP2 { s with pc := UInt256.ofNat 4614, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4620, stack := x2 :: ((UInt256.lt (x0 - x1) x2) - (x0 - x1)) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [r3d_3NewP2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3NewP3 : List Instr := [.op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .LT, .op .SUB]
theorem r3d_3NewP3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3NewP3 { s with pc := UInt256.ofNat 4620, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 4626, stack := ((UInt256.lt (x4 + x0) x4) - x1) :: x2 :: x3 :: (x4 + x0) :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [r3d_3NewP3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3NewP4 : List Instr := [.op .SUB]
theorem r3d_3NewP4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3NewP4 { s with pc := UInt256.ofNat 4626, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4627, stack := (x0 - x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [r3d_3NewP4, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def r3d_3New : List Instr := r3d_3NewP0 ++ r3d_3NewP1 ++ r3d_3NewP2 ++ r3d_3NewP3 ++ r3d_3NewP4
theorem r3d_3New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions r3d_3New { s with pc := UInt256.ofNat 4602, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4627, stack := (((UInt256.lt (z3 + (z1 * (z1 + z0))) z3) - ((UInt256.lt ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))) (z1 * (z1 + z0))) - ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))))) - (z1 * (z1 + z0))) :: z2 :: (z3 + (z1 * (z1 + z0))) :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := r3d_3NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g1 := r3d_3NewP1_run s (z1) ((z1 + z0)) ((z1 + z0)) (z7) ((z1 + z0)) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g2 := r3d_3NewP2_run s ((UInt256.mulMod z1 (z1 + z0) z7)) ((UInt256.gt z1 (z1 + z0))) ((z1 * (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g3 := r3d_3NewP3_run s ((z1 * (z1 + z0))) (((UInt256.lt ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))) (z1 * (z1 + z0))) - ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))))) ((z1 * (z1 + z0))) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g4 := r3d_3NewP4_run s (((UInt256.lt (z3 + (z1 * (z1 + z0))) z3) - ((UInt256.lt ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0))) (z1 * (z1 + z0))) - ((UInt256.mulMod z1 (z1 + z0) z7) - (UInt256.gt z1 (z1 + z0)))))) ((z1 * (z1 + z0))) (z2) ((z3 + (z1 * (z1 + z0)))) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 (runInstructions_append_some _ _ _ _ _ g3 g4))))
  simpa only [r3d_3New, List.append_assoc] using h

def r3d_3Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: rest => v0 :: v4 :: v1 :: v2 :: v3 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: rest
  | xs => xs

theorem run_r3d_3 (s : State) (tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hk : k = Monpro.maxWord) (htb : tb.toNat ≤ 1) :
    runInstructions r3d_3New
      { s with pc := UInt256.ofNat 4602, stack := tb :: a :: p0 :: p3 :: p2 :: p1 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4627, stack := (mCarry a a (a * tb) p3 k) :: p0 :: (mSum a a (a * tb) p3) :: p2 :: p1 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest }  := by
  have ho := r3d_3Old_run s (tb) (a) (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  have hc := R4Runs.run_r3d s tb a p3 p2 p1 p0 p4 k n0 n1 n2 n3 np rest hcap hk htb
  change runInstructions r3d_3Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r3d_3Perm he
  simp only [r3d_3Perm] at hp
  have hn := r3d_3New_run s (tb) (a) (p0) (p3) (p2) (p1) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

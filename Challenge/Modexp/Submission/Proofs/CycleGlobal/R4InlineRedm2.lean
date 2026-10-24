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

def redm_2OldP0 : List Instr := [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MUL, .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨0, by decide⟩)]
theorem redm_2OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions redm_2OldP0 { s with pc := UInt256.ofNat 4621, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 4627, stack := x7 :: x7 :: (x12 * x5) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [redm_2OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def redm_2OldP1 : List Instr := [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MULMOD, .op (.Dup ⟨8, by decide⟩), .op .ADDMOD]
theorem redm_2OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions redm_2OldP1 { s with pc := UInt256.ofNat 4627, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4632, stack := (UInt256.addMod x8 (UInt256.mulMod x11 x2 x0) x1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [redm_2OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def redm_2Old : List Instr := redm_2OldP0 ++ redm_2OldP1
theorem redm_2Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions redm_2Old { s with pc := UInt256.ofNat 4621, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } =
    some { s with pc := UInt256.ofNat 4632, stack := (UInt256.addMod z5 (UInt256.mulMod z8 (z12 * z5) z7) z7) :: (z12 * z5) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: rest } := by
  have g0 := redm_2OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have g1 := redm_2OldP1_run s (z7) (z7) ((z12 * z5)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 g1)
  simpa only [redm_2Old, List.append_assoc] using h

def redm_2NewP0 : List Instr := [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL, .op (.Dup ⟨7, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩)]
theorem redm_2NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions redm_2NewP0 { s with pc := UInt256.ofNat 4497, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4503, stack := (x11 * x2) :: x6 :: x6 :: (x11 * x2) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [redm_2NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def redm_2NewP1 : List Instr := [.op (.Dup ⟨11, by decide⟩), .op .MULMOD, .op (.Dup ⟨5, by decide⟩), .op .ADDMOD]
theorem redm_2NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions redm_2NewP1 { s with pc := UInt256.ofNat 4503, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } =
    some { s with pc := UInt256.ofNat 4507, stack := (UInt256.addMod x6 (UInt256.mulMod x11 x0 x1) x2) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [redm_2NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, capacity, Nat.add_assoc]

def redm_2New : List Instr := redm_2NewP0 ++ redm_2NewP1
theorem redm_2New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions redm_2New { s with pc := UInt256.ofNat 4497, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := UInt256.ofNat 4507, stack := (UInt256.addMod z2 (UInt256.mulMod z7 (z11 * z2) z6) z6) :: (z11 * z2) :: z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := redm_2NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap
  have g1 := redm_2NewP1_run s ((z11 * z2)) (z6) (z6) ((z11 * z2)) (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 g1)
  simpa only [redm_2New, List.append_assoc] using h

def redm_2Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: rest => v0 :: v1 :: v3 :: v6 :: v7 :: v4 :: v5 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: rest
  | xs => xs

theorem run_redm_2 (s : State) (ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hk : k = Monpro.maxWord)
    (hminv : (n0.toNat * np.toNat + 1) % 2^256 = 0)
    (hguard : np ≠ UInt256.ofNat 1) :
    runInstructions redm_2New
      { s with pc := UInt256.ofNat 4497, stack := v :: p1 :: p0 :: p3 :: p2 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4507, stack := redC n0 (np*p0) p0 k :: (np*p0) :: v :: p1 :: p0 :: p3 :: p2 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := redm_2Old_run s (ret) (v) (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  have hc := R4Runs.run_redm s ret v p3 p2 p1 p0 p4 k n0 n1 n2 n3 np rest hcap hk hminv hguard
  change runInstructions redm_2Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg redm_2Perm he
  simp only [redm_2Perm] at hp
  have hn := redm_2New_run s (v) (p1) (p0) (p3) (p2) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
end CycleSubmission.Global.Fast.R4InlineTransport

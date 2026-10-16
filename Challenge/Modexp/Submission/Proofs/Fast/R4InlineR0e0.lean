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

def r0e_0OldP0 : List Instr := [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4382, .push 2 4621, .op .JUMP]
theorem r0e_0OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hjump0 : Decode.isValidJumpDest s.executionEnv.code (4621 : UInt256).toNat = true) :
    runInstructions r0e_0OldP0 { s with pc := UInt256.ofNat 4372, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := (4621 : UInt256), stack := (4382 : UInt256) :: (0 : UInt256) :: x1 :: x2 :: x3 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
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
  simp [r0e_0OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hjump0] <;> rfl

def r0e_0Old : List Instr := r0e_0OldP0
theorem r0e_0Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) (hjump0 : Decode.isValidJumpDest s.executionEnv.code (4621 : UInt256).toNat = true) :
    runInstructions r0e_0Old { s with pc := UInt256.ofNat 4372, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := (4621 : UInt256), stack := (4382 : UInt256) :: (0 : UInt256) :: z1 :: z2 :: z3 :: z4 :: z0 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := r0e_0OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap hjump0
  have h := g0
  simpa only [r0e_0Old, List.append_assoc] using h

def r0e_0NewP0 : List Instr := [.op (.Swap ⟨4, by decide⟩), .op .POP, .push 0 0, .push 2 4382]
theorem r0e_0NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0e_0NewP0 { s with pc := UInt256.ofNat 9090, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 9096, stack := (4382 : UInt256) :: (0 : UInt256) :: x1 :: x2 :: x3 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
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
  simp [r0e_0NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13] <;> rfl

def r0e_0New : List Instr := r0e_0NewP0
theorem r0e_0New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1009) :
    runInstructions r0e_0New { s with pc := UInt256.ofNat 9090, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := UInt256.ofNat 9096, stack := (4382 : UInt256) :: (0 : UInt256) :: z1 :: z2 :: z3 :: z4 :: z0 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := r0e_0NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap
  have h := g0
  simpa only [r0e_0New, List.append_assoc] using h

def r0e_0Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest => v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest
  | xs => xs

theorem run_r0e_0 (s : State) (c t3 t2 t1 t0 d k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4621 = true) :
    runInstructions r0e_0New
      { s with pc := UInt256.ofNat 9090, stack := c :: t3 :: t2 :: t1 :: t0 :: d :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 9096, stack := (4382 : UInt256) :: (⟨0⟩ : UInt256) :: t3 :: t2 :: t1 :: t0 :: c :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r0e_0Old_run s (c) (t3) (t2) (t1) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap hjd
  have hc := R4Runs.run_r0e s c t3 t2 t1 t0 d k n0 n1 n2 n3 np rest hcap hjd
  change runInstructions r0e_0Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r0e_0Perm he
  simp only [r0e_0Perm] at hp
  have hn := r0e_0New_run s (c) (t3) (t2) (t1) (t0) (d) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
#print axioms run_r0e_0
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport

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

def r3e_3OldP0 : List Instr := [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT, .push 2 4725]
theorem r3e_3OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r3e_3OldP0 { s with pc := UInt256.ofNat 4613, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 4621, stack := (4725 : UInt256) :: (UInt256.lt (x5 + x0) x5) :: x1 :: x2 :: x3 :: x4 :: (x5 + x0) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
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
  simp [r3e_3OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r3e_3Old : List Instr := r3e_3OldP0
theorem r3e_3Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r3e_3Old { s with pc := UInt256.ofNat 4613, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := UInt256.ofNat 4621, stack := (4725 : UInt256) :: (UInt256.lt (z5 + z0) z5) :: z1 :: z2 :: z3 :: z4 :: (z5 + z0) :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := r3e_3OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap
  have h := g0
  simpa only [r3e_3Old, List.append_assoc] using h

def r3e_3NewP0 : List Instr := [.op (.Dup ⟨5, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .LT]
theorem r3e_3NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r3e_3NewP0 { s with pc := UInt256.ofNat 9587, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } =
    some { s with pc := UInt256.ofNat 9592, stack := (UInt256.lt (x5 + x0) x5) :: x1 :: x2 :: x3 :: x4 :: (x5 + x0) :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest } := by
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
  simp [r3e_3NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13]

def r3e_3New : List Instr := r3e_3NewP0
theorem r3e_3New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions r3e_3New { s with pc := UInt256.ofNat 9587, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } =
    some { s with pc := UInt256.ofNat 9592, stack := (UInt256.lt (z5 + z0) z5) :: z1 :: z2 :: z3 :: z4 :: (z5 + z0) :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: rest } := by
  have g0 := r3e_3NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) rest hcap
  have h := g0
  simpa only [r3e_3New, List.append_assoc] using h

def r3e_3Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest => v1 :: v5 :: v2 :: v3 :: v4 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: rest
  | xs => xs

theorem run_r3e_3 (s : State) (c p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1010) :
    runInstructions r3e_3New
      { s with pc := UInt256.ofNat 9587, stack := c :: p0 :: p3 :: p2 :: p1 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 9592, stack := (UInt256.lt (p4 + c) p4) :: p0 :: p3 :: p2 :: p1 :: (p4 + c) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := r3e_3Old_run s (c) (p3) (p2) (p1) (p0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  have hc := R4Runs.run_r3e s c p3 p2 p1 p0 p4 k n0 n1 n2 n3 np rest hcap
  change runInstructions r3e_3Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg r3e_3Perm he
  simp only [r3e_3Perm] at hp
  have hn := r3e_3New_run s (c) (p0) (p3) (p2) (p1) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
#print axioms run_r3e_3
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport

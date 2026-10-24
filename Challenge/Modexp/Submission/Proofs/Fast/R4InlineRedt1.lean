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

def redt_1OldP0 : List Instr := [.op (.Dup ⟨8, by decide⟩), .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .POP, .op .POP, .op (.Swap ⟨5, by decide⟩)]
theorem redt_1OldP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_1OldP0 { s with pc := UInt256.ofNat 4710, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } =
    some { s with pc := UInt256.ofNat 4716, stack := x8 :: x3 :: (x8 + x0) :: x5 :: x6 :: x7 :: x2 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest } := by
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
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [redt_1OldP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def redt_1OldP1 : List Instr := [.op (.Dup ⟨2, by decide⟩), .op .LT, .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .JUMP]
theorem redt_1OldP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) (hjump0 : Decode.isValidJumpDest s.executionEnv.code x6.toNat = true) :
    runInstructions redt_1OldP1 { s with pc := UInt256.ofNat 4716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := x6, stack := x2 :: x3 :: x4 :: x5 :: ((UInt256.lt x2 x0) + x1) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
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
  simp [redt_1OldP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hjump0]

def redt_1Old : List Instr := redt_1OldP0 ++ redt_1OldP1
theorem redt_1Old_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) (hjump0 : Decode.isValidJumpDest s.executionEnv.code z2.toNat = true) :
    runInstructions redt_1Old { s with pc := UInt256.ofNat 4710, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } =
    some { s with pc := z2, stack := (z8 + z0) :: z5 :: z6 :: z7 :: ((UInt256.lt (z8 + z0) z8) + z3) :: z9 :: z10 :: z11 :: z12 :: z13 :: z14 :: rest } := by
  have g0 := redt_1OldP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap
  have g1 := redt_1OldP1_run s (z8) (z3) ((z8 + z0)) (z5) (z6) (z7) (z2) (z9) (z10) (z11) (z12) (z13) (z14) rest hcap hjump0
  have h := (runInstructions_append_some _ _ _ _ _ g0 g1)
  simpa only [redt_1Old, List.append_assoc] using h

def redt_1NewP0 : List Instr := [.op (.Dup ⟨7, by decide⟩), .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .POP, .op (.Swap ⟨5, by decide⟩)]
theorem redt_1NewP0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_1NewP0 { s with pc := UInt256.ofNat 9374, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } =
    some { s with pc := UInt256.ofNat 9379, stack := x7 :: x2 :: x3 :: x4 :: (x7 + x0) :: x6 :: x1 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest } := by
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
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [redt_1NewP0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

def redt_1NewP1 : List Instr := [.op (.Dup ⟨4, by decide⟩), .op .LT, .op .ADD, .op (.Swap ⟨4, by decide⟩), .op .POP]
theorem redt_1NewP1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_1NewP1 { s with pc := UInt256.ofNat 9379, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } =
    some { s with pc := UInt256.ofNat 9384, stack := x2 :: x3 :: x4 :: x5 :: ((UInt256.lt x4 x0) + x1) :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest } := by
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
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [redt_1NewP1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

def redt_1New : List Instr := redt_1NewP0 ++ redt_1NewP1
theorem redt_1New_run (s : State) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions redt_1New { s with pc := UInt256.ofNat 9374, stack := z0 :: z1 :: z2 :: z3 :: z4 :: z5 :: z6 :: z7 :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } =
    some { s with pc := UInt256.ofNat 9384, stack := z3 :: z4 :: (z7 + z0) :: z6 :: ((UInt256.lt (z7 + z0) z7) + z2) :: z8 :: z9 :: z10 :: z11 :: z12 :: z13 :: rest } := by
  have g0 := redt_1NewP0_run s (z0) (z1) (z2) (z3) (z4) (z5) (z6) (z7) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have g1 := redt_1NewP1_run s (z7) (z2) (z3) (z4) ((z7 + z0)) (z6) (z1) (z8) (z9) (z10) (z11) (z12) (z13) rest hcap
  have h := (runInstructions_append_some _ _ _ _ _ g0 g1)
  simpa only [redt_1New, List.append_assoc] using h

def redt_1Perm : List UInt256 → List UInt256
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: rest => v2 :: v3 :: v0 :: v1 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: rest
  | xs => xs

theorem run_redt_1 (s : State) (c m ret v p3 q2 q1 q0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007)
    (hjd : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstructions redt_1New
      { s with pc := UInt256.ofNat 9374, stack := c :: m :: v :: q1 :: q0 :: p3 :: q2 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 9384, stack := q1 :: q0 :: (p4 + c) :: q2 :: (v + (UInt256.lt (p4 + c) p4)) :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  have ho := redt_1Old_run s (c) (m) (ret) (v) (p3) (q2) (q1) (q0) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap hjd
  have hc := R4Runs.run_redt s c m ret v p3 q2 q1 q0 p4 k n0 n1 n2 n3 np rest hcap hjd
  change runInstructions redt_1Old _ = _ at hc
  have he := congrArg State.stack (Option.some.inj (ho.symm.trans hc))
  have hp := congrArg redt_1Perm he
  simp only [redt_1Perm] at hp
  have hn := redt_1New_run s (c) (m) (v) (q1) (q0) (p3) (q2) (p4) (k) (n0) (n1) (n2) (n3) (np) rest hcap
  simpa only [hp] using hn
#print axioms run_redt_1
end Challenge.Modexp.Submission.Proofs.Fast.R4InlineTransport

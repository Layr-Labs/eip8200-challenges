import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.R4InlineTailPrograms
import Challenge.Modexp.Submission.Proofs.Fast.R4Runs
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.Fast.R4InlineTailRuns
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open CycleSubmission.Global.Fast.R4InlineTailBlocks Challenge.Modexp.Submission.Proofs.Fast.R4Math
theorem run_tail_zero (s : State) (p3 p2 p1 p0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) :
    runInstructions prog_tail
      { s with pc := UInt256.ofNat 4727, stack := p3 :: p2 :: p1 :: p0 :: (⟨0⟩ : UInt256) :: rest } =
    some { s with pc := UInt256.ofNat 4732,
                  stack := p3 :: p2 :: p1 :: p0 :: (⟨0⟩ : UInt256) :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 8) : rest.length + j < 1024 := by omega
  have hf : ¬ UInt256.isTrue (⟨0⟩ : UInt256) := by decide
  simp [prog_tail, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, hf,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, capacity, Nat.add_assoc]

/-- Tail head with a nonzero overflow word: jumps to `rare4`. -/
theorem run_tail_rare (s : State) (p3 p2 p1 p0 p4 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1013) (hp4 : p4 ≠ ⟨0⟩)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4769 = true) :
    runInstructions prog_tail
      { s with pc := UInt256.ofNat 4727, stack := p3 :: p2 :: p1 :: p0 :: p4 :: rest } =
    some { s with pc := UInt256.ofNat 4769, stack := p3 :: p2 :: p1 :: p0 :: p4 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 8) : rest.length + j < 1024 := by omega
  have ht : UInt256.isTrue p4 := by
    show p4.toNat ≠ 0
    intro h; exact hp4 (Challenge.EvmProof.Word.word_ext (by rw [h]; rfl))
  have hl : (4769 : UInt256).toNat = 4769 := rfl
  simp [prog_tail, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, ht, hl,
    hjd, Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, capacity, Nat.add_assoc]

def prog_rare4_0 : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .SUB, .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT]

/-- `rare4`, limb 0: `d0 = p0 - n0` replaces `p0`, borrow `p0 < n0` on top. -/
theorem run_rare4_0 (s : State) (p3 p2 p1 p0 p4 k n0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009) :
    runInstructions prog_rare4_0
      { s with pc := UInt256.ofNat 4769, stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: rest } =
    some { s with pc := UInt256.ofNat 4778,
                  stack := UInt256.lt p0 n0 :: p3 :: p2 :: p1 :: (p0 - n0) :: p4 :: k :: n0 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 12) : rest.length + j < 1024 := by omega
  simp [prog_rare4_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, capacity, Nat.add_assoc]

def prog_rare4_1 : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB,
   .op (.Swap ⟨6, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR]

/-- `rare4`, limb 1: `e1 = n1 + b0`, `d1 = p1 - e1`, borrow `(b0 > e1) | (p1 < e1)`. -/
theorem run_rare4_1 (s : State) (b0 p3 p2 p1 d0 p4 k n0 n1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1009) :
    runInstructions prog_rare4_1
      { s with pc := UInt256.ofNat 4778,
               stack := b0 :: p3 :: p2 :: p1 :: d0 :: p4 :: k :: n0 :: n1 :: rest } =
    some { s with pc := UInt256.ofNat 4792,
                  stack := UInt256.lor (UInt256.gt b0 (n1 + b0)) (UInt256.lt p1 (n1 + b0)) ::
                    p3 :: p2 :: (p1 - (n1 + b0)) :: d0 :: p4 :: k :: n0 :: n1 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [prog_rare4_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, capacity, Nat.add_assoc]

def prog_rare4_2 : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .SUB,
   .op (.Swap ⟨5, by decide⟩), .op .POP, .op .LT, .op (.Swap ⟨1, by decide⟩), .op .GT, .op .OR]

/-- `rare4`, limb 2: `e2 = n2 + b1`, `d2 = p2 - e2`, borrow `(b1 > e2) | (p2 < e2)`. -/
theorem run_rare4_2 (s : State) (b1 p3 p2 d1 d0 p4 k n0 n1 n2 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) :
    runInstructions prog_rare4_2
      { s with pc := UInt256.ofNat 4792,
               stack := b1 :: p3 :: p2 :: d1 :: d0 :: p4 :: k :: n0 :: n1 :: n2 :: rest } =
    some { s with pc := UInt256.ofNat 4806,
                  stack := UInt256.lor (UInt256.gt b1 (n2 + b1)) (UInt256.lt p2 (n2 + b1)) ::
                    p3 :: (p2 - (n2 + b1)) :: d1 :: d0 :: p4 :: k :: n0 :: n1 :: n2 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [prog_rare4_2, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, capacity, Nat.add_assoc]

def prog_rare4_3 : List Instr :=
  [.op (.Dup ⟨10, by decide⟩), .op .ADD, .op (.Swap ⟨0, by decide⟩), .op .SUB, .push 0 0,
   .op (.Swap ⟨4, by decide⟩), .op .POP, .push 2 4732, .op .JUMP]

/-- `rare4`, limb 3: `d3 = p3 - (n3 + b2)`; the overflow word becomes zero; back to `st4`. -/
theorem run_rare4_3 (s : State) (b2 p3 d2 d1 d0 p4 k n0 n1 n2 n3 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1009)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4732 = true) :
    runInstructions prog_rare4_3
      { s with pc := UInt256.ofNat 4806,
               stack := b2 :: p3 :: d2 :: d1 :: d0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: rest } =
    some { s with pc := UInt256.ofNat 4732,
                  stack := (p3 - (n3 + b2)) :: d2 :: d1 :: d0 :: (⟨0⟩ : UInt256) ::
                    k :: n0 :: n1 :: n2 :: n3 :: rest } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 13) : rest.length + j < 1024 := by omega
  have hl : (4732 : UInt256).toNat = 4732 := rfl
  simp [prog_rare4_3, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, hl,
    hjd, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    hc0, capacity, Nat.add_assoc]

theorem prog_rare4_split :
    prog_rare4 = prog_rare4_0 ++ (prog_rare4_1 ++ (prog_rare4_2 ++ prog_rare4_3)) := rfl

/-- `rare4`: the borrow-chain subtraction of `n0..n3`, overflow word zeroed, back to `st4`. -/
theorem run_rare4 (s : State) (p3 p2 p1 p0 p4 k n0 n1 n2 n3 np : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4732 = true) :
    runInstructions prog_rare4
      { s with pc := UInt256.ofNat 4769,
               stack := p3 :: p2 :: p1 :: p0 :: p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: rest } =
    some { s with pc := UInt256.ofNat 4732,
                  stack := (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t3 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t2 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t1 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t0 ::
                    (sub4 n0 n1 n2 n3 ⟨p0, p1, p2, p3, p4⟩).t4 ::
                    k :: n0 :: n1 :: n2 :: n3 :: np :: rest } := by
  rw [prog_rare4_split]
  have g0 := run_rare4_0 s p3 p2 p1 p0 p4 k n0 (n1 :: n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega)
  have g1 := run_rare4_1 s (UInt256.lt p0 n0) p3 p2 p1 (p0 - n0) p4 k n0 n1 (n2 :: n3 :: np :: rest)
    (by simp only [List.length_cons]; omega)
  have g2 := run_rare4_2 s (UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
      (UInt256.lt p1 (n1 + UInt256.lt p0 n0))) p3 p2 (p1 - (n1 + UInt256.lt p0 n0)) (p0 - n0)
    p4 k n0 n1 n2 (n3 :: np :: rest) (by simp only [List.length_cons]; omega)
  have g3 := run_rare4_3 s
    (UInt256.lor (UInt256.gt (UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
        (UInt256.lt p1 (n1 + UInt256.lt p0 n0)))
      (n2 + UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
        (UInt256.lt p1 (n1 + UInt256.lt p0 n0))))
      (UInt256.lt p2 (n2 + UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
        (UInt256.lt p1 (n1 + UInt256.lt p0 n0)))))
    p3
    (p2 - (n2 + UInt256.lor (UInt256.gt (UInt256.lt p0 n0) (n1 + UInt256.lt p0 n0))
      (UInt256.lt p1 (n1 + UInt256.lt p0 n0))))
    (p1 - (n1 + UInt256.lt p0 n0)) (p0 - n0) p4 k n0 n1 n2 n3 (np :: rest)
    (by simp only [List.length_cons]; omega) hjd
  exact runInstructions_append_some _ _ _ _ _ g0
    (runInstructions_append_some _ _ _ _ _ g1 (runInstructions_append_some _ _ _ _ _ g2 g3))

def prog_st4_0 : List Instr :=
  [.op .JUMPDEST, .push 2 2112, .op .MSTORE, .push 2 2144, .op .MSTORE]

theorem run_st4_0 (s : State) (x0 x1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1019)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_st4_0
      { s with pc := UInt256.ofNat 4732, stack := x0 :: x1 :: rest } =
    some { s with pc := UInt256.ofNat 4741,
                  stack := rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x0.toNat 32) 2112)
          (Data.Bytes.natToBytesPadded x1.toNat 32) 2144) } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 4) : rest.length + j < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hl2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hl2144 : (2144 : UInt256).toNat = 2144 := rfl
  simp [hc0, hz0, prog_st4_0, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, capacity, Nat.add_assoc, hl2112, hl2144, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact]

def prog_st4_1 : List Instr :=
  [.push 2 2176, .op .MSTORE,
   .push 2 2208, .op .MSTORE]

theorem run_st4_1 (s : State) (x0 x1 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1017)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_st4_1
      { s with pc := UInt256.ofNat 4741, stack := x0 :: x1 :: rest } =
    some { s with pc := UInt256.ofNat 4749,
                  stack := rest,
                  memory := (MachineState.writeBytes (MachineState.writeBytes s.memory
          (Data.Bytes.natToBytesPadded x0.toNat 32) 2176)
          (Data.Bytes.natToBytesPadded x1.toNat 32) 2208) } := by
  have hc0 : rest.length < 1024 := by omega
  have capacity (j : Nat) (hj : j ≤ 6) : rest.length + j < 1024 := by omega
  have hz0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have hl2176 : (2176 : UInt256).toNat = 2176 := rfl
  have hl2208 : (2208 : UInt256).toNat = 2208 := rfl
  simp [hc0, hz0, prog_st4_1, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, capacity, Nat.add_assoc, hl2176, hl2208, State.activeWordsAfterUInt256, Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact, Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact]

theorem run_tail_moreOld116 (s : State) (p4 k n0 n1 n2 n3 np c e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 pbi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000)
    (hc : UInt256.isTrue c)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4037 = true) :
    runInstructions prog_branchOld116
      { s with pc := UInt256.ofNat 4749, stack := p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: c :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } =
    some { s with pc := UInt256.ofNat 4037, stack := n0 :: n1 :: n2 :: n3 :: np :: (e5+c) :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  simp [prog_branchOld116, prog_m4, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, hc, hjd, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    capacity, Nat.add_assoc]

theorem run_tail_moreAlias116 (s : State) (p4 k n0 n1 n2 n3 np c e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 pbi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000)
    (hke : k = e5)
    (hc : UInt256.isTrue c)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 4037 = true) :
    runInstructions prog_branch
      { s with pc := UInt256.ofNat 4749, stack := p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: c :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } =
    some { s with pc := UInt256.ofNat 4037, stack := n0 :: n1 :: n2 :: n3 :: np :: (e5+c) :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  simp [hke, prog_branch, prog_m4, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, hc, hjd, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    capacity, Nat.add_assoc]
  exact Challenge.EvmProof.Word.word_add_comm c e5

theorem run_tail_fallOld116 (s : State) (p4 k n0 n1 n2 n3 np c e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 pbi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000)
    (hc : ¬ UInt256.isTrue c) :
    runInstructions prog_branchOld116
      { s with pc := UInt256.ofNat 4749, stack := p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: c :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } =
    some { s with pc := UInt256.ofNat 4759, stack := n0 :: n1 :: n2 :: n3 :: np :: (e5+c) :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  simp [prog_branchOld116, prog_m4, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, hc, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    capacity, Nat.add_assoc]

theorem run_tail_fallAlias116 (s : State) (p4 k n0 n1 n2 n3 np c e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 pbi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000)
    (hke : k = e5)
    (hc : ¬ UInt256.isTrue c) :
    runInstructions prog_branch
      { s with pc := UInt256.ofNat 4749, stack := p4 :: k :: n0 :: n1 :: n2 :: n3 :: np :: c :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } =
    some { s with pc := UInt256.ofNat 4759, stack := n0 :: n1 :: n2 :: n3 :: np :: (e5+c) :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  simp [hke, prog_branch, prog_m4, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, hc, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    capacity, Nat.add_assoc]
  exact Challenge.EvmProof.Word.word_add_comm c e5

theorem run_tail_exit (s : State) (n0 n1 n2 n3 np c e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 pbi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1000)
    (hjd : Decode.isValidJumpDest s.executionEnv.code 3482 = true) :
    runInstructions prog_m4
      { s with pc := UInt256.ofNat 4759, stack := n0 :: n1 :: n2 :: n3 :: np :: c :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: pbi :: rest } =
    some { s with pc := UInt256.ofNat 3482, stack := pbi :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: e8 :: e9 :: e10 :: e11 :: e12 :: e13 :: c :: rest } := by
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  simp [prog_branch, prog_m4, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, hjd, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    capacity, Nat.add_assoc]

private theorem wb_comm (bs b1 b2 : ByteArray) (a1 a2 : Nat)
    (h1 : b1.size ≠ 0) (h2 : b2.size ≠ 0) (hd : a1 + b1.size ≤ a2 ∨ a2 + b2.size ≤ a1) :
    MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2 =
      MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1 := by
  have hsize : (MachineState.writeBytes (MachineState.writeBytes bs b1 a1) b2 a2).size =
      (MachineState.writeBytes (MachineState.writeBytes bs b2 a2) b1 a1).size := by
    rw [MachineState.writeBytes_size, MachineState.writeBytes_size, MachineState.writeBytes_size,
      MachineState.writeBytes_size, if_neg h1, if_neg h2, if_neg h2, if_neg h1]
    omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [MachineState.writeBytes_getElem?_getD]
  split_ifs <;> first | rfl | omega

/-- `st4` stores `0x840, 0x860, 0x880, 0x8a0` in stack order; the four windows are disjoint and
word-aligned, so the nesting is the `r4Mem` order. -/
private theorem st4_mem_reorder (m a b c d : ByteArray)
    (ha : a.size = 32) (hb : b.size = 32) (hc : c.size = 32) (hd : d.size = 32) :
    MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
      (MachineState.writeBytes m a 2112) b 2144) c 2176) d 2208 =
    MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
      (MachineState.writeBytes m d 2208) c 2176) b 2144) a 2112 := by
  have ha0 : a.size ≠ 0 := by omega
  have hb0 : b.size ≠ 0 := by omega
  have hc0 : c.size ≠ 0 := by omega
  have hd0 : d.size ≠ 0 := by omega
  rw [wb_comm (MachineState.writeBytes (MachineState.writeBytes m a 2112) b 2144) c d 2176 2208
        hc0 hd0 (by omega),
    wb_comm (MachineState.writeBytes m a 2112) b d 2144 2208 hb0 hd0 (by omega),
    wb_comm m a d 2112 2208 ha0 hd0 (by omega),
    wb_comm (MachineState.writeBytes (MachineState.writeBytes m d 2208) a 2112) b c 2144 2176
        hb0 hc0 (by omega),
    wb_comm (MachineState.writeBytes m d 2208) a c 2112 2176 ha0 hc0 (by omega),
    wb_comm (MachineState.writeBytes (MachineState.writeBytes m d 2208) c 2176) a b 2112 2144
        ha0 hb0 (by omega)]

theorem run_st4_stores (s : State) (p3 p2 p1 p0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1017)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prog_st4
      { s with pc := UInt256.ofNat 4732, stack := p3 :: p2 :: p1 :: p0 :: rest } =
    some { s with
      pc := UInt256.ofNat 4749, stack := rest,
      memory := MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
        (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p0.toNat 32) 2208)
        (Data.Bytes.natToBytesPadded p1.toNat 32) 2176)
        (Data.Bytes.natToBytesPadded p2.toNat 32) 2144)
        (Data.Bytes.natToBytesPadded p3.toNat 32) 2112 } := by
  have g0 := run_st4_0 s p3 p2 (p1 :: p0 :: rest)
    (by simp only [List.length_cons]; omega) hact
  have g1 := run_st4_1 { s with memory := (MachineState.writeBytes
    (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded p3.toNat 32) 2112)
    (Data.Bytes.natToBytesPadded p2.toNat 32) 2144) } p1 p0 rest (by omega) hact
  have h := runInstructions_append_some prog_st4_0 prog_st4_1 _ _ _ g0 g1
  have hs : ∀ n : Nat, (Data.Bytes.natToBytesPadded n 32).size = 32 :=
    fun n => YulEvmCompiler.BytesLemmas.natToBytesPadded_size n 32
  rw [st4_mem_reorder s.memory (Data.Bytes.natToBytesPadded p3.toNat 32)
    (Data.Bytes.natToBytesPadded p2.toNat 32) (Data.Bytes.natToBytesPadded p1.toNat 32)
    (Data.Bytes.natToBytesPadded p0.toNat 32) (hs _) (hs _) (hs _) (hs _)] at h
  exact h


end CycleSubmission.Global.Fast.R4InlineTailRuns

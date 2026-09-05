import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1099 : Artifact.h39Artifact.instructionPC 1099 = 3096 := by decide
@[simp] private theorem pc1100 : Artifact.h39Artifact.instructionPC 1100 = 3097 := by decide
@[simp] private theorem pc1101 : Artifact.h39Artifact.instructionPC 1101 = 3100 := by decide
@[simp] private theorem pc1102 : Artifact.h39Artifact.instructionPC 1102 = 3101 := by decide
@[simp] private theorem pc1103 : Artifact.h39Artifact.instructionPC 1103 = 3104 := by decide

private def pre3096 : List Located :=
  [opAt 1099 (.Dup ⟨0, by decide⟩),
   pushAt 1100 2 1000,
   opAt 1101 (.EQ),
   pushAt 1102 2 4107]

private theorem run_pre3096 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre3096 (stateAt s bytes 3096) =
      some (atPC s 3104 [UInt256.ofNat 4107, UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre3096, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases3096 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 1000 ∧ Trace (stateAt s bytes 3096) (stateAt s bytes 4107)) ∨
      (bytes.size ≠ 1000 ∧ Trace (stateAt s bytes 3096) (stateAt s bytes 3105)) := by
  by_cases heq : bytes.size = 1000
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 1000 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 1103 .JUMPI) s 3104 4107
      (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc1103
      (by decide) (by decide) (by simp) hc hcode jump4107
    refine Or.inl ⟨heq, join_branch pre3096 (opAt 1103 .JUMPI) (run_pre3096 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 1000 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 1103 .JUMPI) s 3104 4107
      (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc1103
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre3096 (opAt 1103 .JUMPI) (run_pre3096 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


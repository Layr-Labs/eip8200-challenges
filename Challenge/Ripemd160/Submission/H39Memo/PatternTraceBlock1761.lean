import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc869 : Artifact.h39Artifact.instructionPC 869 = 1761 := by decide
@[simp] private theorem pc870 : Artifact.h39Artifact.instructionPC 870 = 1762 := by decide
@[simp] private theorem pc871 : Artifact.h39Artifact.instructionPC 871 = 1764 := by decide
@[simp] private theorem pc872 : Artifact.h39Artifact.instructionPC 872 = 1765 := by decide
@[simp] private theorem pc873 : Artifact.h39Artifact.instructionPC 873 = 1768 := by decide

private def pre1761 : List Located :=
  [opAt 869 (.Dup ⟨0, by decide⟩),
   pushAt 870 1 55,
   opAt 871 (.EQ),
   pushAt 872 2 3529]

private theorem run_pre1761 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1761 (stateAt s bytes 1761) =
      some (atPC s 1768 [UInt256.ofNat 3529, UInt256.eq (UInt256.ofNat 55) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1761, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1761 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 55 ∧ Trace (stateAt s bytes 1761) (stateAt s bytes 3529)) ∨
      (bytes.size ≠ 55 ∧ Trace (stateAt s bytes 1761) (stateAt s bytes 1769)) := by
  by_cases heq : bytes.size = 55
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 55) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 55 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 873 .JUMPI) s 1768 3529
      (UInt256.eq (UInt256.ofNat 55) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc873
      (by decide) (by decide) (by simp) hc hcode jump3529
    refine Or.inl ⟨heq, join_branch pre1761 (opAt 873 .JUMPI) (run_pre1761 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 55) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 55 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 873 .JUMPI) s 1768 3529
      (UInt256.eq (UInt256.ofNat 55) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc873
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1761 (opAt 873 .JUMPI) (run_pre1761 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc895 : Artifact.h39Artifact.instructionPC 895 = 1834 := by decide
@[simp] private theorem pc896 : Artifact.h39Artifact.instructionPC 896 = 1835 := by decide
@[simp] private theorem pc897 : Artifact.h39Artifact.instructionPC 897 = 1837 := by decide
@[simp] private theorem pc898 : Artifact.h39Artifact.instructionPC 898 = 1838 := by decide
@[simp] private theorem pc899 : Artifact.h39Artifact.instructionPC 899 = 1841 := by decide

private def pre1834 : List Located :=
  [opAt 895 (.Dup ⟨0, by decide⟩),
   pushAt 896 1 65,
   opAt 897 (.EQ),
   pushAt 898 2 3768]

private theorem run_pre1834 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1834 (stateAt s bytes 1834) =
      some (atPC s 1841 [UInt256.ofNat 3768, UInt256.eq (UInt256.ofNat 65) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1834, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1834 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 65 ∧ Trace (stateAt s bytes 1834) (stateAt s bytes 3768)) ∨
      (bytes.size ≠ 65 ∧ Trace (stateAt s bytes 1834) (stateAt s bytes 1842)) := by
  by_cases heq : bytes.size = 65
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 65) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 65 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 899 .JUMPI) s 1841 3768
      (UInt256.eq (UInt256.ofNat 65) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc899
      (by decide) (by decide) (by simp) hc hcode jump3768
    refine Or.inl ⟨heq, join_branch pre1834 (opAt 899 .JUMPI) (run_pre1834 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 65) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 65 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 899 .JUMPI) s 1841 3768
      (UInt256.eq (UInt256.ofNat 65) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc899
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1834 (opAt 899 .JUMPI) (run_pre1834 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


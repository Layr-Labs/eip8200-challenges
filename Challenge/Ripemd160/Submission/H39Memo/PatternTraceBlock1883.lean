import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc906 : Artifact.h39Artifact.instructionPC 906 = 1883 := by decide
@[simp] private theorem pc907 : Artifact.h39Artifact.instructionPC 907 = 1884 := by decide
@[simp] private theorem pc908 : Artifact.h39Artifact.instructionPC 908 = 1886 := by decide
@[simp] private theorem pc909 : Artifact.h39Artifact.instructionPC 909 = 1887 := by decide
@[simp] private theorem pc910 : Artifact.h39Artifact.instructionPC 910 = 1890 := by decide

private def pre1883 : List Located :=
  [opAt 906 (.Dup ⟨0, by decide⟩),
   pushAt 907 1 119,
   opAt 908 (.EQ),
   pushAt 909 2 3838]

private theorem run_pre1883 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1883 (stateAt s bytes 1883) =
      some (atPC s 1890 [UInt256.ofNat 3838, UInt256.eq (UInt256.ofNat 119) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1883, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1883 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 119 ∧ Trace (stateAt s bytes 1883) (stateAt s bytes 3838)) ∨
      (bytes.size ≠ 119 ∧ Trace (stateAt s bytes 1883) (stateAt s bytes 1891)) := by
  by_cases heq : bytes.size = 119
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 119) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 119 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 910 .JUMPI) s 1890 3838
      (UInt256.eq (UInt256.ofNat 119) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc910
      (by decide) (by decide) (by simp) hc hcode jump3838
    refine Or.inl ⟨heq, join_branch pre1883 (opAt 910 .JUMPI) (run_pre1883 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 119) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 119 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 910 .JUMPI) s 1890 3838
      (UInt256.eq (UInt256.ofNat 119) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc910
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1883 (opAt 910 .JUMPI) (run_pre1883 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


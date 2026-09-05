import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc911 : Artifact.h39Artifact.instructionPC 911 = 1891 := by decide
@[simp] private theorem pc912 : Artifact.h39Artifact.instructionPC 912 = 1892 := by decide
@[simp] private theorem pc913 : Artifact.h39Artifact.instructionPC 913 = 1894 := by decide
@[simp] private theorem pc914 : Artifact.h39Artifact.instructionPC 914 = 1895 := by decide
@[simp] private theorem pc915 : Artifact.h39Artifact.instructionPC 915 = 1898 := by decide

private def pre1891 : List Located :=
  [opAt 911 (.Dup ⟨0, by decide⟩),
   pushAt 912 1 120,
   opAt 913 (.EQ),
   pushAt 914 2 3908]

private theorem run_pre1891 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1891 (stateAt s bytes 1891) =
      some (atPC s 1898 [UInt256.ofNat 3908, UInt256.eq (UInt256.ofNat 120) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1891, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1891 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 120 ∧ Trace (stateAt s bytes 1891) (stateAt s bytes 3908)) ∨
      (bytes.size ≠ 120 ∧ Trace (stateAt s bytes 1891) (stateAt s bytes 1899)) := by
  by_cases heq : bytes.size = 120
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 120) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 120 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 915 .JUMPI) s 1898 3908
      (UInt256.eq (UInt256.ofNat 120) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc915
      (by decide) (by decide) (by simp) hc hcode jump3908
    refine Or.inl ⟨heq, join_branch pre1891 (opAt 915 .JUMPI) (run_pre1891 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 120) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 120 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 915 .JUMPI) s 1898 3908
      (UInt256.eq (UInt256.ofNat 120) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc915
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1891 (opAt 915 .JUMPI) (run_pre1891 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


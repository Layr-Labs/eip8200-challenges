import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc890 : Artifact.h39Artifact.instructionPC 890 = 1826 := by decide
@[simp] private theorem pc891 : Artifact.h39Artifact.instructionPC 891 = 1827 := by decide
@[simp] private theorem pc892 : Artifact.h39Artifact.instructionPC 892 = 1829 := by decide
@[simp] private theorem pc893 : Artifact.h39Artifact.instructionPC 893 = 1830 := by decide
@[simp] private theorem pc894 : Artifact.h39Artifact.instructionPC 894 = 1833 := by decide

private def pre1826 : List Located :=
  [opAt 890 (.Dup ⟨0, by decide⟩),
   pushAt 891 1 64,
   opAt 892 (.EQ),
   pushAt 893 2 3739]

private theorem run_pre1826 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1826 (stateAt s bytes 1826) =
      some (atPC s 1833 [UInt256.ofNat 3739, UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1826, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1826 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 64 ∧ Trace (stateAt s bytes 1826) (stateAt s bytes 3739)) ∨
      (bytes.size ≠ 64 ∧ Trace (stateAt s bytes 1826) (stateAt s bytes 1834)) := by
  by_cases heq : bytes.size = 64
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 64 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 894 .JUMPI) s 1833 3739
      (UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc894
      (by decide) (by decide) (by simp) hc hcode jump3739
    refine Or.inl ⟨heq, join_branch pre1826 (opAt 894 .JUMPI) (run_pre1826 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 64 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 894 .JUMPI) s 1833 3739
      (UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc894
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1826 (opAt 894 .JUMPI) (run_pre1826 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


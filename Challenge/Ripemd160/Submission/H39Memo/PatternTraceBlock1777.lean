import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc879 : Artifact.h39Artifact.instructionPC 879 = 1777 := by decide
@[simp] private theorem pc880 : Artifact.h39Artifact.instructionPC 880 = 1778 := by decide
@[simp] private theorem pc881 : Artifact.h39Artifact.instructionPC 881 = 1780 := by decide
@[simp] private theorem pc882 : Artifact.h39Artifact.instructionPC 882 = 1781 := by decide
@[simp] private theorem pc883 : Artifact.h39Artifact.instructionPC 883 = 1784 := by decide

private def pre1777 : List Located :=
  [opAt 879 (.Dup ⟨0, by decide⟩),
   pushAt 880 1 63,
   opAt 881 (.EQ),
   pushAt 882 2 3669]

private theorem run_pre1777 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1777 (stateAt s bytes 1777) =
      some (atPC s 1784 [UInt256.ofNat 3669, UInt256.eq (UInt256.ofNat 63) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1777, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1777 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 63 ∧ Trace (stateAt s bytes 1777) (stateAt s bytes 3669)) ∨
      (bytes.size ≠ 63 ∧ Trace (stateAt s bytes 1777) (stateAt s bytes 1785)) := by
  by_cases heq : bytes.size = 63
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 63) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 63 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 883 .JUMPI) s 1784 3669
      (UInt256.eq (UInt256.ofNat 63) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc883
      (by decide) (by decide) (by simp) hc hcode jump3669
    refine Or.inl ⟨heq, join_branch pre1777 (opAt 883 .JUMPI) (run_pre1777 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 63) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 63 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 883 .JUMPI) s 1784 3669
      (UInt256.eq (UInt256.ofNat 63) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc883
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1777 (opAt 883 .JUMPI) (run_pre1777 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


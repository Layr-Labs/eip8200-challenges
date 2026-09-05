import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc864 : Artifact.h39Artifact.instructionPC 864 = 1753 := by decide
@[simp] private theorem pc865 : Artifact.h39Artifact.instructionPC 865 = 1754 := by decide
@[simp] private theorem pc866 : Artifact.h39Artifact.instructionPC 866 = 1756 := by decide
@[simp] private theorem pc867 : Artifact.h39Artifact.instructionPC 867 = 1757 := by decide
@[simp] private theorem pc868 : Artifact.h39Artifact.instructionPC 868 = 1760 := by decide

private def pre1753 : List Located :=
  [opAt 864 (.Dup ⟨0, by decide⟩),
   pushAt 865 1 32,
   opAt 866 (.EQ),
   pushAt 867 2 3500]

private theorem run_pre1753 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1753 (stateAt s bytes 1753) =
      some (atPC s 1760 [UInt256.ofNat 3500, UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1753, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1753 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 32 ∧ Trace (stateAt s bytes 1753) (stateAt s bytes 3500)) ∨
      (bytes.size ≠ 32 ∧ Trace (stateAt s bytes 1753) (stateAt s bytes 1761)) := by
  by_cases heq : bytes.size = 32
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 32 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 868 .JUMPI) s 1760 3500
      (UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc868
      (by decide) (by decide) (by simp) hc hcode jump3500
    refine Or.inl ⟨heq, join_branch pre1753 (opAt 868 .JUMPI) (run_pre1753 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 32 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 868 .JUMPI) s 1760 3500
      (UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc868
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1753 (opAt 868 .JUMPI) (run_pre1753 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


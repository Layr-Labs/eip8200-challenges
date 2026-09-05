import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc853 : Artifact.h39Artifact.instructionPC 853 = 1705 := by decide
@[simp] private theorem pc854 : Artifact.h39Artifact.instructionPC 854 = 1706 := by decide
@[simp] private theorem pc855 : Artifact.h39Artifact.instructionPC 855 = 1708 := by decide
@[simp] private theorem pc856 : Artifact.h39Artifact.instructionPC 856 = 1709 := by decide
@[simp] private theorem pc857 : Artifact.h39Artifact.instructionPC 857 = 1712 := by decide

private def pre1705 : List Located :=
  [opAt 853 (.Dup ⟨0, by decide⟩),
   pushAt 854 1 31,
   opAt 855 (.EQ),
   pushAt 856 2 3431]

private theorem run_pre1705 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1705 (stateAt s bytes 1705) =
      some (atPC s 1712 [UInt256.ofNat 3431, UInt256.eq (UInt256.ofNat 31) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1705, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1705 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 31 ∧ Trace (stateAt s bytes 1705) (stateAt s bytes 3431)) ∨
      (bytes.size ≠ 31 ∧ Trace (stateAt s bytes 1705) (stateAt s bytes 1713)) := by
  by_cases heq : bytes.size = 31
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 31) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 31 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 857 .JUMPI) s 1712 3431
      (UInt256.eq (UInt256.ofNat 31) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc857
      (by decide) (by decide) (by simp) hc hcode jump3431
    refine Or.inl ⟨heq, join_branch pre1705 (opAt 857 .JUMPI) (run_pre1705 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 31) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 31 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 857 .JUMPI) s 1712 3431
      (UInt256.eq (UInt256.ofNat 31) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc857
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1705 (opAt 857 .JUMPI) (run_pre1705 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


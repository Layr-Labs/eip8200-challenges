import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc874 : Artifact.h39Artifact.instructionPC 874 = 1769 := by decide
@[simp] private theorem pc875 : Artifact.h39Artifact.instructionPC 875 = 1770 := by decide
@[simp] private theorem pc876 : Artifact.h39Artifact.instructionPC 876 = 1772 := by decide
@[simp] private theorem pc877 : Artifact.h39Artifact.instructionPC 877 = 1773 := by decide
@[simp] private theorem pc878 : Artifact.h39Artifact.instructionPC 878 = 1776 := by decide

private def pre1769 : List Located :=
  [opAt 874 (.Dup ⟨0, by decide⟩),
   pushAt 875 1 56,
   opAt 876 (.EQ),
   pushAt 877 2 3599]

private theorem run_pre1769 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1769 (stateAt s bytes 1769) =
      some (atPC s 1776 [UInt256.ofNat 3599, UInt256.eq (UInt256.ofNat 56) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1769, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1769 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 56 ∧ Trace (stateAt s bytes 1769) (stateAt s bytes 3599)) ∨
      (bytes.size ≠ 56 ∧ Trace (stateAt s bytes 1769) (stateAt s bytes 1777)) := by
  by_cases heq : bytes.size = 56
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 56) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 56 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 878 .JUMPI) s 1776 3599
      (UInt256.eq (UInt256.ofNat 56) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc878
      (by decide) (by decide) (by simp) hc hcode jump3599
    refine Or.inl ⟨heq, join_branch pre1769 (opAt 878 .JUMPI) (run_pre1769 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 56) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 56 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 878 .JUMPI) s 1776 3599
      (UInt256.eq (UInt256.ofNat 56) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc878
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1769 (opAt 878 .JUMPI) (run_pre1769 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc847 : Artifact.h39Artifact.instructionPC 847 = 1696 := by decide
@[simp] private theorem pc848 : Artifact.h39Artifact.instructionPC 848 = 1697 := by decide
@[simp] private theorem pc849 : Artifact.h39Artifact.instructionPC 849 = 1698 := by decide
@[simp] private theorem pc850 : Artifact.h39Artifact.instructionPC 850 = 1700 := by decide
@[simp] private theorem pc851 : Artifact.h39Artifact.instructionPC 851 = 1701 := by decide
@[simp] private theorem pc852 : Artifact.h39Artifact.instructionPC 852 = 1704 := by decide

private def pre1696 : List Located :=
  [opAt 847 (.JUMPDEST),
   opAt 848 (.Dup ⟨0, by decide⟩),
   pushAt 849 1 1,
   opAt 850 (.EQ),
   pushAt 851 2 3362]

private theorem run_pre1696 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1696 (stateAt s bytes 1696) =
      some (atPC s 1704 [UInt256.ofNat 3362, UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1696, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1696 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 1 ∧ Trace (stateAt s bytes 1696) (stateAt s bytes 3362)) ∨
      (bytes.size ≠ 1 ∧ Trace (stateAt s bytes 1696) (stateAt s bytes 1705)) := by
  by_cases heq : bytes.size = 1
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 1 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 852 .JUMPI) s 1704 3362
      (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc852
      (by decide) (by decide) (by simp) hc hcode jump3362
    refine Or.inl ⟨heq, join_branch pre1696 (opAt 852 .JUMPI) (run_pre1696 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 1 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 852 .JUMPI) s 1704 3362
      (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc852
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1696 (opAt 852 .JUMPI) (run_pre1696 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

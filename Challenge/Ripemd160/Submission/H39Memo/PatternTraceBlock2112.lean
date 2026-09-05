import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc951 : Artifact.h39Artifact.instructionPC 951 = 2112 := by decide
@[simp] private theorem pc952 : Artifact.h39Artifact.instructionPC 952 = 2113 := by decide
@[simp] private theorem pc953 : Artifact.h39Artifact.instructionPC 953 = 2116 := by decide
@[simp] private theorem pc954 : Artifact.h39Artifact.instructionPC 954 = 2117 := by decide
@[simp] private theorem pc955 : Artifact.h39Artifact.instructionPC 955 = 2120 := by decide

private def pre2112 : List Located :=
  [opAt 951 (.Dup ⟨0, by decide⟩),
   pushAt 952 2 256,
   opAt 953 (.EQ),
   pushAt 954 2 4007]

private theorem run_pre2112 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2112 (stateAt s bytes 2112) =
      some (atPC s 2120 [UInt256.ofNat 4007, UInt256.eq (UInt256.ofNat 256) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre2112, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases2112 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 256 ∧ Trace (stateAt s bytes 2112) (stateAt s bytes 4007)) ∨
      (bytes.size ≠ 256 ∧ Trace (stateAt s bytes 2112) (stateAt s bytes 2121)) := by
  by_cases heq : bytes.size = 256
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 256) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 256 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 955 .JUMPI) s 2120 4007
      (UInt256.eq (UInt256.ofNat 256) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc955
      (by decide) (by decide) (by simp) hc hcode jump4007
    refine Or.inl ⟨heq, join_branch pre2112 (opAt 955 .JUMPI) (run_pre2112 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 256) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 256 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 955 .JUMPI) s 2120 4007
      (UInt256.eq (UInt256.ofNat 256) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc955
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre2112 (opAt 955 .JUMPI) (run_pre2112 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


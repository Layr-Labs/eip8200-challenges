import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc974 : Artifact.h39Artifact.instructionPC 974 = 2247 := by decide
@[simp] private theorem pc975 : Artifact.h39Artifact.instructionPC 975 = 2248 := by decide
@[simp] private theorem pc976 : Artifact.h39Artifact.instructionPC 976 = 2251 := by decide
@[simp] private theorem pc977 : Artifact.h39Artifact.instructionPC 977 = 2252 := by decide
@[simp] private theorem pc978 : Artifact.h39Artifact.instructionPC 978 = 2255 := by decide

private def pre2247 : List Located :=
  [opAt 974 (.Dup ⟨0, by decide⟩),
   pushAt 975 2 376,
   opAt 976 (.EQ),
   pushAt 977 2 4036]

private theorem run_pre2247 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2247 (stateAt s bytes 2247) =
      some (atPC s 2255 [UInt256.ofNat 4036, UInt256.eq (UInt256.ofNat 376) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre2247, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases2247 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 376 ∧ Trace (stateAt s bytes 2247) (stateAt s bytes 4036)) ∨
      (bytes.size ≠ 376 ∧ Trace (stateAt s bytes 2247) (stateAt s bytes 2256)) := by
  by_cases heq : bytes.size = 376
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 376) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 376 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 978 .JUMPI) s 2255 4036
      (UInt256.eq (UInt256.ofNat 376) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc978
      (by decide) (by decide) (by simp) hc hcode jump4036
    refine Or.inl ⟨heq, join_branch pre2247 (opAt 978 .JUMPI) (run_pre2247 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 376) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 376 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 978 .JUMPI) s 2255 4036
      (UInt256.eq (UInt256.ofNat 376) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc978
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre2247 (opAt 978 .JUMPI) (run_pre2247 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


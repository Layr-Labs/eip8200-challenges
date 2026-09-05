import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc922 : Artifact.h39Artifact.instructionPC 922 = 1940 := by decide
@[simp] private theorem pc923 : Artifact.h39Artifact.instructionPC 923 = 1941 := by decide
@[simp] private theorem pc924 : Artifact.h39Artifact.instructionPC 924 = 1943 := by decide
@[simp] private theorem pc925 : Artifact.h39Artifact.instructionPC 925 = 1944 := by decide
@[simp] private theorem pc926 : Artifact.h39Artifact.instructionPC 926 = 1947 := by decide

private def pre1940 : List Located :=
  [opAt 922 (.Dup ⟨0, by decide⟩),
   pushAt 923 1 128,
   opAt 924 (.EQ),
   pushAt 925 2 3978]

private theorem run_pre1940 (s : State) (bytes : ByteArray)
    (_hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre1940 (stateAt s bytes 1940) =
      some (atPC s 1947 [UInt256.ofNat 3978, UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat bytes.size), UInt256.ofNat bytes.size]) := by
  simp [pre1940, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem size_cases1940 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hfit : bytes.size < 2 ^ 64)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode) :
    (bytes.size = 128 ∧ Trace (stateAt s bytes 1940) (stateAt s bytes 3978)) ∨
      (bytes.size ≠ 128 ∧ Trace (stateAt s bytes 1940) (stateAt s bytes 1948)) := by
  by_cases heq : bytes.size = 128
  · have hc : UInt256.isTrue (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat bytes.size)) :=
      (eq_true_iff 128 bytes.size (by decide) (by omega)).2 heq.symm
    have hb := branch_true (opAt 926 .JUMPI) s 1947 3978
      (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc926
      (by decide) (by decide) (by simp) hc hcode jump3978
    refine Or.inl ⟨heq, join_branch pre1940 (opAt 926 .JUMPI) (run_pre1940 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : ¬ UInt256.isTrue (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat bytes.size)) := by
      rw [eq_true_iff 128 bytes.size (by decide) (by omega)]
      exact Ne.symm heq
    have hb := branch_false (opAt 926 .JUMPI) s 1947 3978
      (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat bytes.size)) [UInt256.ofNat bytes.size] rfl pc926
      (by decide) (by simp) hc
    refine Or.inr ⟨heq, join_branch pre1940 (opAt 926 .JUMPI) (run_pre1940 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace


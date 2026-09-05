import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc985 : Artifact.h39Artifact.instructionPC 985 = 2298 := by decide
@[simp] private theorem pc986 : Artifact.h39Artifact.instructionPC 986 = 2301 := by decide
@[simp] private theorem pc987 : Artifact.h39Artifact.instructionPC 987 = 2302 := by decide
@[simp] private theorem pc988 : Artifact.h39Artifact.instructionPC 988 = 2335 := by decide
@[simp] private theorem pc989 : Artifact.h39Artifact.instructionPC 989 = 2336 := by decide
@[simp] private theorem pc990 : Artifact.h39Artifact.instructionPC 990 = 2339 := by decide

private def pre2298 : List Located :=
  [pushAt 985 2 384,
   opAt 986 (.CALLDATALOAD),
   pushAt 987 32 (PatternFacts.prefixWord 12),
   opAt 988 (.XOR),
   pushAt 989 2 3109]

private theorem run_pre2298 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2298 (stateAt s bytes 2298) =
      some (atPC s 2339 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 12) (MachineState.readWord bytes 384), UInt256.ofNat bytes.size]) := by
  simp [pre2298, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2298 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 384 = PatternFacts.prefixWord 12 ∧
      Trace (stateAt s bytes 2298) (stateAt s bytes 2340)) ∨
      Trace (stateAt s bytes 2298) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 384 = PatternFacts.prefixWord 12
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 12) (MachineState.readWord bytes 384)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 990 .JUMPI) s 2339 3109
      (UInt256.xor (PatternFacts.prefixWord 12) (MachineState.readWord bytes 384)) [UInt256.ofNat bytes.size] rfl pc990
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2298 (opAt 990 .JUMPI) (run_pre2298 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 12) (MachineState.readWord bytes 384)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 990 .JUMPI) s 2339 3109
      (UInt256.xor (PatternFacts.prefixWord 12) (MachineState.readWord bytes 384)) [UInt256.ofNat bytes.size] rfl pc990
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2298 (opAt 990 .JUMPI) (run_pre2298 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

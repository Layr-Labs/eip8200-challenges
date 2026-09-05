import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc962 : Artifact.h39Artifact.instructionPC 962 = 2163 := by decide
@[simp] private theorem pc963 : Artifact.h39Artifact.instructionPC 963 = 2166 := by decide
@[simp] private theorem pc964 : Artifact.h39Artifact.instructionPC 964 = 2167 := by decide
@[simp] private theorem pc965 : Artifact.h39Artifact.instructionPC 965 = 2200 := by decide
@[simp] private theorem pc966 : Artifact.h39Artifact.instructionPC 966 = 2201 := by decide
@[simp] private theorem pc967 : Artifact.h39Artifact.instructionPC 967 = 2204 := by decide

private def pre2163 : List Located :=
  [pushAt 962 2 288,
   opAt 963 (.CALLDATALOAD),
   pushAt 964 32 (PatternFacts.prefixWord 9),
   opAt 965 (.XOR),
   pushAt 966 2 3109]

private theorem run_pre2163 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2163 (stateAt s bytes 2163) =
      some (atPC s 2204 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 9) (MachineState.readWord bytes 288), UInt256.ofNat bytes.size]) := by
  simp [pre2163, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2163 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 288 = PatternFacts.prefixWord 9 ∧
      Trace (stateAt s bytes 2163) (stateAt s bytes 2205)) ∨
      Trace (stateAt s bytes 2163) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 288 = PatternFacts.prefixWord 9
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 9) (MachineState.readWord bytes 288)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 967 .JUMPI) s 2204 3109
      (UInt256.xor (PatternFacts.prefixWord 9) (MachineState.readWord bytes 288)) [UInt256.ofNat bytes.size] rfl pc967
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2163 (opAt 967 .JUMPI) (run_pre2163 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 9) (MachineState.readWord bytes 288)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 967 .JUMPI) s 2204 3109
      (UInt256.xor (PatternFacts.prefixWord 9) (MachineState.readWord bytes 288)) [UInt256.ofNat bytes.size] rfl pc967
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2163 (opAt 967 .JUMPI) (run_pre2163 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

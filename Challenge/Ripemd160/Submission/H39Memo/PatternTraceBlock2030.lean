import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc939 : Artifact.h39Artifact.instructionPC 939 = 2030 := by decide
@[simp] private theorem pc940 : Artifact.h39Artifact.instructionPC 940 = 2032 := by decide
@[simp] private theorem pc941 : Artifact.h39Artifact.instructionPC 941 = 2033 := by decide
@[simp] private theorem pc942 : Artifact.h39Artifact.instructionPC 942 = 2066 := by decide
@[simp] private theorem pc943 : Artifact.h39Artifact.instructionPC 943 = 2067 := by decide
@[simp] private theorem pc944 : Artifact.h39Artifact.instructionPC 944 = 2070 := by decide

private def pre2030 : List Located :=
  [pushAt 939 1 192,
   opAt 940 (.CALLDATALOAD),
   pushAt 941 32 (PatternFacts.prefixWord 6),
   opAt 942 (.XOR),
   pushAt 943 2 3109]

private theorem run_pre2030 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2030 (stateAt s bytes 2030) =
      some (atPC s 2070 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 6) (MachineState.readWord bytes 192), UInt256.ofNat bytes.size]) := by
  simp [pre2030, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2030 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 192 = PatternFacts.prefixWord 6 ∧
      Trace (stateAt s bytes 2030) (stateAt s bytes 2071)) ∨
      Trace (stateAt s bytes 2030) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 192 = PatternFacts.prefixWord 6
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 6) (MachineState.readWord bytes 192)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 944 .JUMPI) s 2070 3109
      (UInt256.xor (PatternFacts.prefixWord 6) (MachineState.readWord bytes 192)) [UInt256.ofNat bytes.size] rfl pc944
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2030 (opAt 944 .JUMPI) (run_pre2030 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 6) (MachineState.readWord bytes 192)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 944 .JUMPI) s 2070 3109
      (UInt256.xor (PatternFacts.prefixWord 6) (MachineState.readWord bytes 192)) [UInt256.ofNat bytes.size] rfl pc944
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2030 (opAt 944 .JUMPI) (run_pre2030 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

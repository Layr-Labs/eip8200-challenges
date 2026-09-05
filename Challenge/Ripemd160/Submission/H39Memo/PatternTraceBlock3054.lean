import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1093 : Artifact.h39Artifact.instructionPC 1093 = 3054 := by decide
@[simp] private theorem pc1094 : Artifact.h39Artifact.instructionPC 1094 = 3057 := by decide
@[simp] private theorem pc1095 : Artifact.h39Artifact.instructionPC 1095 = 3058 := by decide
@[simp] private theorem pc1096 : Artifact.h39Artifact.instructionPC 1096 = 3091 := by decide
@[simp] private theorem pc1097 : Artifact.h39Artifact.instructionPC 1097 = 3092 := by decide
@[simp] private theorem pc1098 : Artifact.h39Artifact.instructionPC 1098 = 3095 := by decide

private def pre3054 : List Located :=
  [pushAt 1093 2 960,
   opAt 1094 (.CALLDATALOAD),
   pushAt 1095 32 (PatternFacts.prefixWord 30),
   opAt 1096 (.XOR),
   pushAt 1097 2 3109]

private theorem run_pre3054 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre3054 (stateAt s bytes 3054) =
      some (atPC s 3095 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 30) (MachineState.readWord bytes 960), UInt256.ofNat bytes.size]) := by
  simp [pre3054, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases3054 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 960 = PatternFacts.prefixWord 30 ∧
      Trace (stateAt s bytes 3054) (stateAt s bytes 3096)) ∨
      Trace (stateAt s bytes 3054) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 960 = PatternFacts.prefixWord 30
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 30) (MachineState.readWord bytes 960)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1098 .JUMPI) s 3095 3109
      (UInt256.xor (PatternFacts.prefixWord 30) (MachineState.readWord bytes 960)) [UInt256.ofNat bytes.size] rfl pc1098
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre3054 (opAt 1098 .JUMPI) (run_pre3054 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 30) (MachineState.readWord bytes 960)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1098 .JUMPI) s 3095 3109
      (UInt256.xor (PatternFacts.prefixWord 30) (MachineState.readWord bytes 960)) [UInt256.ofNat bytes.size] rfl pc1098
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre3054 (opAt 1098 .JUMPI) (run_pre3054 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

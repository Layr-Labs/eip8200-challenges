import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc968 : Artifact.h39Artifact.instructionPC 968 = 2205 := by decide
@[simp] private theorem pc969 : Artifact.h39Artifact.instructionPC 969 = 2208 := by decide
@[simp] private theorem pc970 : Artifact.h39Artifact.instructionPC 970 = 2209 := by decide
@[simp] private theorem pc971 : Artifact.h39Artifact.instructionPC 971 = 2242 := by decide
@[simp] private theorem pc972 : Artifact.h39Artifact.instructionPC 972 = 2243 := by decide
@[simp] private theorem pc973 : Artifact.h39Artifact.instructionPC 973 = 2246 := by decide

private def pre2205 : List Located :=
  [pushAt 968 2 320,
   opAt 969 (.CALLDATALOAD),
   pushAt 970 32 (PatternFacts.prefixWord 10),
   opAt 971 (.XOR),
   pushAt 972 2 3109]

private theorem run_pre2205 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2205 (stateAt s bytes 2205) =
      some (atPC s 2246 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 10) (MachineState.readWord bytes 320), UInt256.ofNat bytes.size]) := by
  simp [pre2205, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2205 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 320 = PatternFacts.prefixWord 10 ∧
      Trace (stateAt s bytes 2205) (stateAt s bytes 2247)) ∨
      Trace (stateAt s bytes 2205) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 320 = PatternFacts.prefixWord 10
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 10) (MachineState.readWord bytes 320)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 973 .JUMPI) s 2246 3109
      (UInt256.xor (PatternFacts.prefixWord 10) (MachineState.readWord bytes 320)) [UInt256.ofNat bytes.size] rfl pc973
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2205 (opAt 973 .JUMPI) (run_pre2205 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 10) (MachineState.readWord bytes 320)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 973 .JUMPI) s 2246 3109
      (UInt256.xor (PatternFacts.prefixWord 10) (MachineState.readWord bytes 320)) [UInt256.ofNat bytes.size] rfl pc973
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2205 (opAt 973 .JUMPI) (run_pre2205 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc979 : Artifact.h39Artifact.instructionPC 979 = 2256 := by decide
@[simp] private theorem pc980 : Artifact.h39Artifact.instructionPC 980 = 2259 := by decide
@[simp] private theorem pc981 : Artifact.h39Artifact.instructionPC 981 = 2260 := by decide
@[simp] private theorem pc982 : Artifact.h39Artifact.instructionPC 982 = 2293 := by decide
@[simp] private theorem pc983 : Artifact.h39Artifact.instructionPC 983 = 2294 := by decide
@[simp] private theorem pc984 : Artifact.h39Artifact.instructionPC 984 = 2297 := by decide

private def pre2256 : List Located :=
  [pushAt 979 2 352,
   opAt 980 (.CALLDATALOAD),
   pushAt 981 32 (PatternFacts.prefixWord 11),
   opAt 982 (.XOR),
   pushAt 983 2 3109]

private theorem run_pre2256 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2256 (stateAt s bytes 2256) =
      some (atPC s 2297 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 11) (MachineState.readWord bytes 352), UInt256.ofNat bytes.size]) := by
  simp [pre2256, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2256 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 352 = PatternFacts.prefixWord 11 ∧
      Trace (stateAt s bytes 2256) (stateAt s bytes 2298)) ∨
      Trace (stateAt s bytes 2256) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 352 = PatternFacts.prefixWord 11
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 11) (MachineState.readWord bytes 352)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 984 .JUMPI) s 2297 3109
      (UInt256.xor (PatternFacts.prefixWord 11) (MachineState.readWord bytes 352)) [UInt256.ofNat bytes.size] rfl pc984
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2256 (opAt 984 .JUMPI) (run_pre2256 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 11) (MachineState.readWord bytes 352)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 984 .JUMPI) s 2297 3109
      (UInt256.xor (PatternFacts.prefixWord 11) (MachineState.readWord bytes 352)) [UInt256.ofNat bytes.size] rfl pc984
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2256 (opAt 984 .JUMPI) (run_pre2256 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

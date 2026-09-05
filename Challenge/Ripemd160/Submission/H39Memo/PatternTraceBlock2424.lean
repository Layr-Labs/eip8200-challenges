import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc1003 : Artifact.h39Artifact.instructionPC 1003 = 2424 := by decide
@[simp] private theorem pc1004 : Artifact.h39Artifact.instructionPC 1004 = 2427 := by decide
@[simp] private theorem pc1005 : Artifact.h39Artifact.instructionPC 1005 = 2428 := by decide
@[simp] private theorem pc1006 : Artifact.h39Artifact.instructionPC 1006 = 2461 := by decide
@[simp] private theorem pc1007 : Artifact.h39Artifact.instructionPC 1007 = 2462 := by decide
@[simp] private theorem pc1008 : Artifact.h39Artifact.instructionPC 1008 = 2465 := by decide

private def pre2424 : List Located :=
  [pushAt 1003 2 480,
   opAt 1004 (.CALLDATALOAD),
   pushAt 1005 32 (PatternFacts.prefixWord 15),
   opAt 1006 (.XOR),
   pushAt 1007 2 3109]

private theorem run_pre2424 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2424 (stateAt s bytes 2424) =
      some (atPC s 2465 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 15) (MachineState.readWord bytes 480), UInt256.ofNat bytes.size]) := by
  simp [pre2424, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2424 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 480 = PatternFacts.prefixWord 15 ∧
      Trace (stateAt s bytes 2424) (stateAt s bytes 2466)) ∨
      Trace (stateAt s bytes 2424) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 480 = PatternFacts.prefixWord 15
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 15) (MachineState.readWord bytes 480)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 1008 .JUMPI) s 2465 3109
      (UInt256.xor (PatternFacts.prefixWord 15) (MachineState.readWord bytes 480)) [UInt256.ofNat bytes.size] rfl pc1008
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2424 (opAt 1008 .JUMPI) (run_pre2424 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 15) (MachineState.readWord bytes 480)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 1008 .JUMPI) s 2465 3109
      (UInt256.xor (PatternFacts.prefixWord 15) (MachineState.readWord bytes 480)) [UInt256.ofNat bytes.size] rfl pc1008
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2424 (opAt 1008 .JUMPI) (run_pre2424 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

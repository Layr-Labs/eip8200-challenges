import Challenge.Ripemd160.Submission.H39Memo.PatternTraceJumps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof DispatchState A1000

@[simp] private theorem pc991 : Artifact.h39Artifact.instructionPC 991 = 2340 := by decide
@[simp] private theorem pc992 : Artifact.h39Artifact.instructionPC 992 = 2343 := by decide
@[simp] private theorem pc993 : Artifact.h39Artifact.instructionPC 993 = 2344 := by decide
@[simp] private theorem pc994 : Artifact.h39Artifact.instructionPC 994 = 2377 := by decide
@[simp] private theorem pc995 : Artifact.h39Artifact.instructionPC 995 = 2378 := by decide
@[simp] private theorem pc996 : Artifact.h39Artifact.instructionPC 996 = 2381 := by decide

private def pre2340 : List Located :=
  [pushAt 991 2 416,
   opAt 992 (.CALLDATALOAD),
   pushAt 993 32 (PatternFacts.prefixWord 13),
   opAt 994 (.XOR),
   pushAt 995 2 3109]

private theorem run_pre2340 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock pre2340 (stateAt s bytes 2340) =
      some (atPC s 2381 [UInt256.ofNat 3109, UInt256.xor (PatternFacts.prefixWord 13) (MachineState.readWord bytes 416), UInt256.ofNat bytes.size]) := by
  simp [pre2340, opAt, pushAt, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, stateAt, atPC, hinput, hrun,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem prefix_cases2340 (s : State) (bytes : ByteArray)
    (hinput : s.executionEnv.calldata = bytes) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = h39Bytecode) :
    (MachineState.readWord bytes 416 = PatternFacts.prefixWord 13 ∧
      Trace (stateAt s bytes 2340) (stateAt s bytes 2382)) ∨
      Trace (stateAt s bytes 2340) (stateAt s bytes 3109) := by
  by_cases heq : MachineState.readWord bytes 416 = PatternFacts.prefixWord 13
  · have hc : ¬ UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 13) (MachineState.readWord bytes 416)) := by
      rw [xor_true_iff]
      exact not_not_intro heq.symm
    have hb := branch_false (opAt 996 .JUMPI) s 2381 3109
      (UInt256.xor (PatternFacts.prefixWord 13) (MachineState.readWord bytes 416)) [UInt256.ofNat bytes.size] rfl pc996
      (by decide) (by simp) hc
    refine Or.inl ⟨heq, join_branch pre2340 (opAt 996 .JUMPI) (run_pre2340 s bytes hinput hrun) hrun ?_⟩
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb
  · have hc : UInt256.isTrue (UInt256.xor (PatternFacts.prefixWord 13) (MachineState.readWord bytes 416)) := by
      rw [xor_true_iff]
      exact Ne.symm heq
    have hb := branch_true (opAt 996 .JUMPI) s 2381 3109
      (UInt256.xor (PatternFacts.prefixWord 13) (MachineState.readWord bytes 416)) [UInt256.ofNat bytes.size] rfl pc996
      (by decide) (by decide) (by simp) hc hcode jump3109
    refine Or.inr (join_branch pre2340 (opAt 996 .JUMPI) (run_pre2340 s bytes hinput hrun) hrun ?_)
    simpa only [stateAt, atPC, Word.literal_eq_ofNat] using hb

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

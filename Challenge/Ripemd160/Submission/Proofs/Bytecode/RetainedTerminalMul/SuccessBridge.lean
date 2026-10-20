import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.ResultEdgeBridge

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace RetainedResultEdge112
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace RetainedIntegration105
open DenseScheduleTrace (runInstrSeq_append_running)

def successTemplate : List Instr :=
  [.op .MSIZE, .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .RETURN]

theorem actual_success_slice :
    (RetainedBridge111.Candidate.instructions.drop 5227).take 3 = successTemplate := by
  have hd : RetainedBridge111.Candidate.instructions.drop 5227 =
      RetainedBridge111.Candidate.suffixInstructions.drop 2 := by
    rw [show 5227 = 5225 + 2 by decide, ← List.drop_drop, Candidate.after_data]
  rw [hd]
  rfl

def returned (s : State) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 9422, stack := rho, halt := .Returned, activeWords := UInt256.ofNat 1, hReturn := MachineState.readPadded s.memory 0 32}

theorem run_success (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq successTemplate {s with pc := UInt256.ofNat 9420, stack := rho} =
      some (returned s rho) := by
  have hcap (n : Nat) (hn : n ≤ 3) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [successTemplate, returned, runInstrSeq, DataStepper.runInstr,
    MachineState.msize, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    ha, hrun, show rho.length < 1024 by omega, hcap, UInt256.succ,
    Instr.size, Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    show ({val := 0} : UInt256).toNat = 0 by rfl,
    show ((UInt256.ofNat 9420).add (UInt256.ofNat 1)).add (UInt256.ofNat 1) = UInt256.ofNat 9422 by decide]

/-- Successful raw candidate return, preserving the original arbitrary stack tail. -/
theorem run_actual_return (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4785 = true)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    runInstrSeq (dataAndResult ++ ((RetainedBridge111.Candidate.instructions.drop 5227).take 3))
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some (returned (stored s ExactBindings.digest) rho) := by
  apply runInstrSeq_append_running (run_actual_zero s rho hs hrun ha hv hz)
  · exact hrun
  · rw [actual_success_slice]
    apply run_success (stored s ExactBindings.digest) rho hs hrun
    simp [stored, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      ha, Word.word_toNat_ofNat]

theorem returned_memory (s : State) (rho : List UInt256) :
    (returned (stored s ExactBindings.digest) rho).memory =
      MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded ExactBindings.digest.toNat 32) 0 := rfl

theorem digest_bytes : Data.Bytes.natToBytesPadded ExactBindings.digest.toNat 32 =
    PatternedDigest.paddedDigest := by
  exact PatternedGuardSpec.wordBytes_eq_paddedDigest

theorem returned_bytes (s : State) (rho : List UInt256) :
    (returned (stored s ExactBindings.digest) rho).hReturn = PatternedDigest.paddedDigest := by
  change MachineState.readPadded
    (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded ExactBindings.digest.toNat 32) 0)
    0 32 = _
  have hw := Memory.readPadded_writeBytes_same s.memory
    (Data.Bytes.natToBytesPadded ExactBindings.digest.toNat 32) 0
  have hsize : (Data.Bytes.natToBytesPadded ExactBindings.digest.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize] at hw
  rw [hw, digest_bytes]

theorem returned_spec (s : State) (rho : List UInt256)
    (hn : s.executionEnv.calldata.size = 1000)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    (returned (stored s ExactBindings.digest) rho).hReturn = spec s.executionEnv.calldata := by
  rw [returned_bytes, RetainedBridge111.retained_zero_spec s.executionEnv.calldata hn hz]

/-- The content miss also consumes the retained word, but stops before fallback cleanup. -/
theorem run_content_miss (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4785 = true)
    (hn : s.executionEnv.calldata.size = 1000)
    (hm : s.executionEnv.calldata ≠ PatternedInputData.patternedInput) :
    runInstrSeq dataAndResult
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {(stored s ExactBindings.digest) with pc := UInt256.ofNat 4785, stack := rho} := by
  apply run_actual_nonzero s rho hs hrun ha hv
  intro hz
  apply (RetainedBridge111.retained_nonzero_iff_content_miss s.executionEnv.calldata hn).mpr hm
  exact Word.word_ext (by simpa only [show (0 : UInt256).toNat = 0 by decide] using hz)

#print axioms actual_success_slice
#print axioms run_success
#print axioms run_actual_return
#print axioms returned_bytes
#print axioms returned_spec
#print axioms run_content_miss
end RetainedResultEdge112

import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.EntryBridge

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

def cleanupTemplate : List Instr :=
  [.op .JUMPDEST, .push ⟨0, by decide⟩ 0, .push ⟨0, by decide⟩ 0,
   .op .MSTORE, .push ⟨1, by decide⟩ (UInt256.ofNat 245), .op .JUMP]

theorem actual_cleanup_slice :
    (RetainedBridge111.Candidate.instructions.drop 3502).take 6 = cleanupTemplate := by rfl

/-- The cleanup erases the speculative word, but does not undo its allocation.
    The generic entry proof must absorb the remaining high-water mark. -/
def cleared (s : State) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 245, stack := rho, activeWords := UInt256.ofNat 1, memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded 0 32) 0}

theorem run_cleanup (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1)
    (hv : Decode.isValidJumpDest s.executionEnv.code 245 = true) :
    runInstrSeq cleanupTemplate {s with pc := UInt256.ofNat 4785, stack := rho} =
      some (cleared s rho) := by
  have hcap (n : Nat) (hn : n ≤ 3) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [cleanupTemplate, cleared, runInstrSeq,
    DataStepper.runInstr, MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, ha, hrun, hv,
    show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    show ({val := 0} : UInt256).toNat = 0 by rfl]

/-- Content miss through the actual fallback cleanup: no retained-word leak,
    no speculative digest bytes survive in the first memory word. -/
theorem run_content_miss_cleanup (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hvMiss : Decode.isValidJumpDest s.executionEnv.code 4785 = true)
    (hvGeneric : Decode.isValidJumpDest s.executionEnv.code 245 = true)
    (hn : s.executionEnv.calldata.size = 1000)
    (hm : s.executionEnv.calldata ≠ PatternedInputData.patternedInput) :
    runInstrSeq (dataAndResult ++
      ((RetainedBridge111.Candidate.instructions.drop 3502).take 6))
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some (cleared (stored s ExactBindings.digest) rho) := by
  apply runInstrSeq_append_running (run_content_miss s rho hs hrun ha hvMiss hn hm)
  · exact hrun
  · rw [actual_cleanup_slice]
    apply run_cleanup (stored s ExactBindings.digest) rho hs hrun _ hvGeneric
    simp [stored, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      ha, Word.word_toNat_ofNat]

theorem cleared_first_word (s : State) (rho : List UInt256) :
    MachineState.readPadded (cleared s rho).memory 0 32 = Data.Bytes.natToBytesPadded 0 32 := by
  change MachineState.readPadded
    (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded 0 32) 0) 0 32 = _
  have hw := Memory.readPadded_writeBytes_same s.memory (Data.Bytes.natToBytesPadded 0 32) 0
  have hz : (Data.Bytes.natToBytesPadded 0 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  simpa only [hz] using hw

#print axioms actual_cleanup_slice
#print axioms run_cleanup
#print axioms run_content_miss_cleanup
#print axioms cleared_first_word
end RetainedResultEdge112

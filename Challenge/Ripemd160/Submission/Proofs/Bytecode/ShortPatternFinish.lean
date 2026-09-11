import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinishPrelude
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar
theorem run_store (n : Nat) (input : ByteArray) (sv ov : UInt256)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32) (hsize : input.size = n) :
    run digestStorePath (digestEntryState n input sv ov) =
      some (copyReadyState n input sv ov) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { maxSteps := 400000 })
    [digestStorePath, opAt, pushAt, wfOp, digestEntryState, copyReadyState, tableOffset,
     returnRest, stS, initialState, answerMemory, storeWord, paddedDigestWord,
     List.exchange, hsize, UInt256.eq, UInt256.isTrue, State.activeWordsAfterUInt256,
     MachineState.activeWordsAfter, hzeroNat,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
  all_goals rfl

theorem run_finish (n : Nat) (input : ByteArray) (sv ov : UInt256) :
    run digestFinishPath (sizedState n input sv ov) =
      some (returnedState n input sv ov) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [digestFinishPath, opAt, pushAt, wfOp, sizedState, storedState,
      returnRest, stS, initialState, returnedState, answerMemory, storeWord,
      paddedDigestWord, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter, hzeroNat,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_return (n : Nat) (input : ByteArray) (sv ov : UInt256)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32) (hsize : input.size = n) :
    GasSteps (selectorState n input sv ov) (returnedState n input sv ov) := by
  have gselect := sound selectorPath (run_selector n input sv ov)
  have gstore := sound digestStorePath (run_store n input sv ov hn hsize)
  have hc := Artifact.submissionArtifact.decodeAt_op_index 4100 .CODECOPY
    (by rfl) (by decide) trivial
  have hpc : (copyReadyState n input sv ov).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4100 := by rw [pc4870]; rfl
  have hcopy : (copyReadyState n input sv ov).decodedOp = some .CODECOPY :=
    Artifact.submissionArtifact.state_decodedOp_of (copyReadyState n input sv ov) 4100
      (by rfl) hpc .CODECOPY none hc (by rfl)
  have gcraw := Codecopy.step (s := copyReadyState n input sv ov)
    12 (UInt256.ofNat (tableOffset n)) 20 (returnRest sv ov)
    hcopy rfl (by
      change 11 + Operation.pushArity .CODECOPY ≤ 1024 + Operation.popArity .CODECOPY
      decide)
    rfl deployAddress_not_precompile
  have hoff : (UInt256.ofNat (tableOffset n)).toNat = tableOffset n := by
    rw [Word.word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    unfold tableOffset
    have hlt := Nat.mod_lt (((1015 * n + 9) / 256)) (by decide : 0 < 14)
    omega
  have gc : GasSteps (copyReadyState n input sv ov) (storedState n input sv ov) := by
    simpa [copyReadyState, storedState, stS, initialState, hoff,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Word.succ_ofNat_mod, Word.word_toNat_ofNat,
      show (0 : UInt256).toNat = 0 from rfl,
      show (12 : UInt256).toNat = 12 from rfl,
      show (20 : UInt256).toNat = 20 from rfl,
      show MachineState.writeBytes ByteArray.empty
        (MachineState.readPadded submissionBytecode (tableOffset n) 20) 12 = answerMemory n
        from tableMemory_eq n hn] using gcraw
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4101 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState n input sv ov).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4101 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (storedState n input sv ov).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState n input sv ov) 4101
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop
    (by simp [storedState, returnRest, stS, initialState])
    (by rfl) deployAddress_not_precompile
  have gm : GasSteps (storedState n input sv ov) (sizedState n input sv ov) := by
    simpa [storedState, sizedState, returnRest, stS, initialState,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat] using gmraw
  exact gselect.trans (gstore.trans (gc.trans (gm.trans (sound digestFinishPath
    (run_finish n input sv ov)))))

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256)
    (hne : acc ≠ 0) :
    GasSteps (stS input 250 [sv, ov, acc, P7, M, m7, P, m8])
      (fallbackState input) :=
  Prefix256Cleanup.gasSteps_miss input sv ov acc hne

def gasSteps_finish_hit (n : Nat) (input : ByteArray) (sv ov acc : UInt256)
    (hz : acc = 0) (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32) (hsize : input.size = n) :
    GasSteps (stS input 250 [sv, ov, acc, P7, M, m7, P, m8])
      (returnedState n input sv ov) := by
  subst acc
  exact (Prefix256Cleanup.gasSteps_hit input sv ov).trans
    (gasSteps_return n input sv ov hn hsize)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish

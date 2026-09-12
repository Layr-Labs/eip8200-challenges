import Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-!
# Verifier finish: digest-table store and return with an empty stack

The verifier's hit path reaches the digest-table entry at pc 4836 with an empty
stack (the dispatch `JUMPI` consumed the size word and the verifier consumed
its accumulator).  These lemmas mirror `ShortPatternFinish` but carry `[]` as
the stack rest instead of `returnRest sv ov`; the digest store recomputes the
table offset from `CALLDATASIZE`, so the residue is never read.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierFinish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar
open ShortPatternFinish VerifierRun

/-- Digest entry with an empty stack rest. -/
def vDigestEntry (input : ByteArray) : State := stS input 4836 []

/-- Copy-ready state with an empty stack rest. -/
def vCopyReady (n : Nat) (input : ByteArray) : State :=
  stS input 4862 [12, UInt256.ofNat (tableOffset n), 20]

/-- Stored state with an empty stack rest. -/
def vStored (n : Nat) (input : ByteArray) : State :=
  { stS input 4863 [] with
    memory := answerMemory n
    activeWords := UInt256.ofNat 1 }

/-- Sized state with an empty stack rest. -/
def vSized (n : Nat) (input : ByteArray) : State :=
  { vStored n input with
    pc := UInt256.ofNat 4864
    stack := [UInt256.ofNat 32] }

/-- Returned state with an empty stack rest. -/
def vReturned (n : Nat) (input : ByteArray) : State :=
  { vStored n input with
    pc := UInt256.ofNat 4865
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory n) 0 32 }

theorem run_vstore (n : Nat) (input : ByteArray)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32) (hsize : input.size = n) :
    run digestStorePath (vDigestEntry input) =
      some (vCopyReady n input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { maxSteps := 400000 })
    [digestStorePath, opAt, pushAt, wfOp, vDigestEntry, vCopyReady, tableOffset,
     stS, initialState, answerMemory, storeWord, paddedDigestWord,
     List.exchange, hsize, UInt256.eq, UInt256.isTrue, State.activeWordsAfterUInt256,
     MachineState.activeWordsAfter, hzeroNat,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]
  all_goals rfl

theorem run_vfinish (n : Nat) (input : ByteArray) :
    run digestFinishPath (vSized n input) =
      some (vReturned n input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 400000 })
    [digestFinishPath, opAt, pushAt, wfOp, vSized, vStored,
     stS, initialState, vReturned, answerMemory, storeWord,
     paddedDigestWord, State.activeWordsAfterUInt256,
     MachineState.activeWordsAfter, hzeroNat,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat]

/-- From the verifier's hit state (pc 4836, empty stack) to the returned
state. -/
def gasSteps_vreturn (n : Nat) (input : ByteArray)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32) (hsize : input.size = n) :
    GasSteps (vDigestEntry input) (vReturned n input) := by
  have gstore := sound digestStorePath (run_vstore n input hn hsize)
  have hc := Artifact.submissionArtifact.decodeAt_op_index 4104 .CODECOPY
    (by rfl) (by decide) trivial
  have hpc : (vCopyReady n input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4104 := by rw [pc4870]; rfl
  have hcopy : (vCopyReady n input).decodedOp = some .CODECOPY :=
    Artifact.submissionArtifact.state_decodedOp_of (vCopyReady n input) 4104
      (by rfl) hpc .CODECOPY none hc (by rfl)
  have gcraw := Codecopy.step (s := vCopyReady n input)
    12 (UInt256.ofNat (tableOffset n)) 20 []
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
  have gc : GasSteps (vCopyReady n input) (vStored n input) := by
    simpa [vCopyReady, vStored, stS, initialState, hoff,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Word.succ_ofNat_mod, Word.word_toNat_ofNat,
      show (0 : UInt256).toNat = 0 from rfl,
      show (12 : UInt256).toNat = 12 from rfl,
      show (20 : UInt256).toNat = 20 from rfl,
      show MachineState.writeBytes ByteArray.empty
        (MachineState.readPadded submissionBytecode (tableOffset n) 20) 12 = answerMemory n
        from tableMemory_eq n hn] using gcraw
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4105 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (vStored n input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4105 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (vStored n input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (vStored n input) 4105
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop
    (by simp [vStored, stS, initialState])
    (by rfl) deployAddress_not_precompile
  have gm : GasSteps (vStored n input) (vSized n input) := by
    simpa [vStored, vSized, stS, initialState,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat] using gmraw
  exact gstore.trans (gc.trans (gm.trans (sound digestFinishPath
    (run_vfinish n input))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.VerifierFinish

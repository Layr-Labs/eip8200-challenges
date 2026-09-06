import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactTailTargetTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestResult
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputDirectTrace

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactPaths KnownInputCompactState

def digestWord : UInt256 :=
  UInt256.ofNat 0xaa69deee9a8922e92f8105e007f76110f381e9cf

def bodyRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.messageOffsetWord i, UInt256.ofNat 0x436,
    DriverTrace.blockOffsetWord i, Padding.paddedWord input]

def storedState (s : State) (input : ByteArray) (i : Nat) : State :=
  FastOutputTrace.afterFastStore s (UInt256.ofNat 4916) digestWord
    (bodyRest input i)

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  FastOutputTrace.afterFastReturn (storedState s input i)
    (UInt256.ofNat 4921) (bodyRest input i)

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

theorem run_direct (s : State) (i : Nat) (hrun : s.halt = .Running) :
    run directPath (bodyEntry s KnownInputData.targetInput i) =
      some (resultState s KnownInputData.targetInput i) := by
  simp (config := { maxSteps := 1000000 })
    [directPath, KnownInputCompactPaths.opAt, KnownInputCompactPaths.pushAt,
      KnownInputCompactPaths.wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, resultState, storedState, bodyRest, digestWord,
      FastOutputTrace.afterFastStore, FastOutputTrace.afterFastReturn,
      FastOutputTemplate.fastStoreAndSetup, FastOutputTemplate.push0,
      FastOutputTemplate.fastOutputReturnTemplate,
      DenseScheduleTemplate.push1, DenseScheduleTemplate.op,
      hrun, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_direct (s : State) (i : Nat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (bodyEntry s KnownInputData.targetInput i)
      (resultState s KnownInputData.targetInput i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka directPath
  · change (bodyEntry s KnownInputData.targetInput i).executionEnv.code =
        submissionBytecode
    simpa [bodyEntry] using hcode
  · simpa [State.fork, bodyEntry] using hfork
  · exact run_direct s i hrun
  · simpa [bodyEntry] using hrun
  · simpa [bodyEntry] using hnp

theorem resultState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).callStack = s.callStack := by rfl

theorem resultState_returned (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = .Returned := by rfl

private theorem digestBytes :
    Data.Bytes.natToBytesPadded digestWord.toNat 32 =
      ByteArray.mk (Array.replicate 12 0) ++ KnownInputDigest.targetDigest := by
  apply ByteArray.ext
  norm_num (config := { maxSteps := 1000000 })
    [digestWord, KnownInputDigest.targetDigest, KnownInputDigest.H16,
      SpecBridge.emitDigest, EvmSemantics.Crypto.Ripemd160.writeLE32,
      Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE,
      YulEvmCompiler.natToBE, List.range, List.range.loop,
      List.range', List.foldl, ByteArray.empty,
      ByteArray.emptyWithCapacity, ByteArray.push]
  ; decide

private theorem spec_eq (input : ByteArray) :
    spec input = ByteArray.mk (Array.replicate 12 0) ++
      Crypto.Ripemd160.hash input := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem resultState_returnData (s : State) (i : Nat) :
    (resultState s KnownInputData.targetInput i).hReturn =
      spec KnownInputData.targetInput := by
  unfold resultState storedState FastOutputTrace.afterFastReturn
    FastOutputTrace.afterFastStore bodyRest
  change MachineState.readPadded
      (MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded digestWord.toNat 32) 0) 0 32 = _
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same s.memory
    (Data.Bytes.natToBytesPadded digestWord.toNat 32) 0
  rw [show MachineState.readPadded
      (MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded digestWord.toNat 32) 0) 0 32 =
      Data.Bytes.natToBytesPadded digestWord.toNat 32 by
    simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hread]
  rw [digestBytes, spec_eq, KnownDigestResult.hash_target]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputDirectTrace

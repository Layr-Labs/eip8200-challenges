import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

def gasSteps_return :
    GasSteps (hitState patternedInput) (returnedState patternedInput) := by
  change GasSteps
    (ShortPatternFinish.selectorState 1000 patternedInput (UInt256.ofNat (scalarAt 32)) 1024)
    (ShortPatternFinish.returnedState 1000 patternedInput (UInt256.ofNat (scalarAt 32)) 1024)
  exact ShortPatternFinish.gasSteps_return 1000 patternedInput
    (UInt256.ofNat (scalarAt 32)) 1024 (by decide) patternedInput_size

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

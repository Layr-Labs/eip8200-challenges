import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DigestReturn

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec

def gasSteps_return :
    GasSteps (hitState patternedInput) (returnedState patternedInput) := by
  have select := Prefix256Select.gasSteps_select patternedInput
  rw [Prefix256Value.selected_1000 patternedInput patternedInput_size] at select
  exact select.trans (DigestReturn.gasSteps_return patternedInput paddedDigestWord)

#print axioms gasSteps_return

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

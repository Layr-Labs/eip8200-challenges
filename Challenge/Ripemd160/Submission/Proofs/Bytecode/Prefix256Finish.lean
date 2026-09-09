import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Select
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DigestReturn

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord : UInt256 := Prefix256Digest.paddedDigestWord

def paddedDigest : ByteArray := Prefix256Digest.paddedDigest

def answerMemory : ByteArray := DigestReturn.answerMemory paddedDigestWord

def storedState (input : ByteArray) : State := DigestReturn.storedState input paddedDigestWord

def returnedState (input : ByteArray) : State := DigestReturn.returnedState input paddedDigestWord

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Memory.natToBytesPadded_eq_natToBE]
  decide

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory DigestReturn.answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (input : ByteArray) :
    (returnedState input).hReturn = paddedDigest := answerMemory_read

@[simp] theorem returnedState_hReturn_size (input : ByteArray) :
    (returnedState input).hReturn.size = 32 := by
  rw [returnedState_hReturn, paddedDigest_size]

def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 424 [sv, ov, acc, P7, M, m7, P, m8]) (fallbackState input) :=
  Prefix256Cleanup.gasSteps_miss input sv ov acc hne

def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hz : acc = 0) (hsize : input.size = 376) :
    GasSteps (stS input 424 [sv, ov, acc, P7, M, m7, P, m8]) (returnedState input) := by
  subst acc
  have select := Prefix256Select.gasSteps_select input
  rw [Prefix256Value.selected_256 input hsize] at select
  exact (Prefix256Cleanup.gasSteps_hit input sv ov).trans
    (select.trans (DigestReturn.gasSteps_return input paddedDigestWord))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Finish

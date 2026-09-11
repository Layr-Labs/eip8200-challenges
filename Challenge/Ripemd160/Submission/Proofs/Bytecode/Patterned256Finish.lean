import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Finish
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord : UInt256 := Patterned256Digest.paddedDigestWord
def paddedDigest : ByteArray := Patterned256Digest.paddedDigest
def answerMemory : ByteArray := ShortPatternFinish.answerMemory 256
def returnRest : List UInt256 := ShortPatternFinish.returnRest (UInt256.ofNat (scalarAt 8)) 256
def returnedState (input : ByteArray) : State :=
  ShortPatternFinish.returnedState 256 input (UInt256.ofNat (scalarAt 8)) 256
@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide
theorem answerMemory_read : MachineState.readPadded answerMemory 0 32 = paddedDigest :=
  ShortPatternFinish.answerMemory_read 256
@[simp] theorem returnedState_hReturn (input : ByteArray) :
    (returnedState input).hReturn = paddedDigest := answerMemory_read
@[simp] theorem returnedState_hReturn_size (input : ByteArray) :
    (returnedState input).hReturn.size = 32 := by
  rw [returnedState_hReturn, paddedDigest_size]
def gasSteps_miss (input : ByteArray) (sv ov acc : UInt256) (hne : acc ≠ 0) :
    GasSteps (stS input 259 [sv, ov, acc, P7, M, m7, P, m8]) (fallbackState input) :=
  ShortPatternFinish.gasSteps_miss input sv ov acc hne
def gasSteps_finish_hit (input : ByteArray) (sv ov acc : UInt256)
    (hz : acc = 0) (hsize : input.size = 256) :
    GasSteps (stS input 259 [sv, ov, acc, P7, M, m7, P, m8])
      (ShortPatternFinish.returnedState 256 input sv ov) :=
  ShortPatternFinish.gasSteps_finish_hit 256 input sv ov acc hz (by decide) hsize
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Finish

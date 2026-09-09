import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar

def scanAccFinal (input : ByteArray) : UInt256 := scanAcc input 32

theorem isTrue_iff (x : UInt256) : UInt256.isTrue x ↔ x ≠ 0 := by
  unfold UInt256.isTrue
  have hz : (0 : UInt256).toNat = 0 := by decide
  exact ⟨fun h hx => h (by rw [hx, hz]),
    fun h hx => h (Challenge.EvmProof.Word.word_ext (by rw [hx, hz]))⟩

/-- A zero accumulator means the calldata is the vector, so the guard answers. -/
def gasSteps_tail_hit (input : ByteArray) (hz : scanAccFinal input = 0) :
    GasSteps (tailState input (scanAcc input 32)) (hitState input) := by
  change scanAcc input 32 = 0 at hz
  unfold tailState
  rw [hz]
  exact Prefix256Cleanup.gasSteps_hit input (UInt256.ofNat (scalarAt 32)) 1024

def gasSteps_tail_miss (input : ByteArray) (hne : scanAccFinal input ≠ 0) :
    GasSteps (tailState input (scanAcc input 32)) (fallbackState input) :=
  Prefix256Cleanup.gasSteps_miss input (UInt256.ofNat (scalarAt 32)) 1024
    (scanAcc input 32) hne

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

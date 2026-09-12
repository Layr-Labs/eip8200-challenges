import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- Mathematical chaining state after `n` padded blocks. -/
def hashAfter (input : ByteArray) (n : Nat) : Array UInt32 :=
  SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
    (Padding.paddedMessage input) 0 n

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def initialHashState : Compression.HashState :=
  { h0 := Crypto.Ripemd160.H0[0]!
    h1 := Crypto.Ripemd160.H0[1]!
    h2 := Crypto.Ripemd160.H0[2]!
    h3 := Crypto.Ripemd160.H0[3]!
    h4 := Crypto.Ripemd160.H0[4]! }

def hashStateAfter (input : ByteArray) : Nat → Compression.HashState
  | 0 => initialHashState
  | n + 1 => CompressionCorrect.compressModel
      (fun i =>
        (CompressionCorrect.schedule (Padding.paddedMessage input)
          (DriverTrace.blockOffset n))[i]!)
      (hashStateAfter input n)

theorem hashAfter_succ (input : ByteArray) (n : Nat) :
    CompressionSeamBridge.hashAfter input (n + 1) =
      Crypto.Ripemd160.compressBlock
        (CompressionSeamBridge.hashAfter input n)
        (Padding.paddedMessage input) (n * 64) := by
  unfold CompressionSeamBridge.hashAfter
  simpa using SpecBridge.absorbBlocks_succ Crypto.Ripemd160.H0
    (Padding.paddedMessage input) 0 n

theorem hashArray_hashStateAfter (input : ByteArray) (n : Nat) :
    CompressionCorrect.hashArray (hashStateAfter input n) =
      CompressionSeamBridge.hashAfter input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [hashStateAfter, DriverTrace.blockOffset,
        CompressionCorrect.compressModel_eq_compressBlock,
        ih, hashAfter_succ]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge

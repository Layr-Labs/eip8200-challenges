import Challenge.Sha256.Reference.Proofs.Bytecode.Padding

set_option warningAsError true

/-!
# Normalized functional target for direct-bytecode SHA-256 proofs

This module deliberately contains only the small, stable functional model.
Execution-specific byte and memory bridges live in separate modules so an
optimized submission can replace those lemmas without changing its target.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge

open EvmSemantics.Crypto

/-- Fold `count` consecutive SHA blocks beginning at byte offset `base`. -/
def absorbBlocks (H : Array UInt32) (bs : ByteArray) (base count : Nat) :
    Array UInt32 :=
  (List.range count).foldl
    (fun state block => Sha256.compressBlock state bs (base + block * 64)) H

/-- Emit the eight SHA state words as the canonical 32-byte digest. -/
def emitDigest (H : Array UInt32) : ByteArray :=
  (List.range 8).foldl
    (fun output i => Sha256.writeBE32 output H[i]!) ByteArray.empty

/-- The direct-bytecode proof's functional target: absorb the exact padded
message image established by the padding proof, then emit the digest. -/
def paddedHash (input : ByteArray) : ByteArray :=
  emitDigest (absorbBlocks Sha256.H0 (Padding.paddedMessage input) 0
    (Padding.paddedLength input.size / 64))

@[simp] theorem absorbBlocks_zero (H : Array UInt32) (bs : ByteArray)
    (base : Nat) : absorbBlocks H bs base 0 = H := by
  rfl

theorem absorbBlocks_succ (H : Array UInt32) (bs : ByteArray)
    (base count : Nat) :
    absorbBlocks H bs base (count + 1) =
      Sha256.compressBlock (absorbBlocks H bs base count) bs
        (base + count * 64) := by
  simp [absorbBlocks, List.range_succ, List.foldl_append]

end Challenge.Sha256.Reference.Proofs.Bytecode.SpecBridge

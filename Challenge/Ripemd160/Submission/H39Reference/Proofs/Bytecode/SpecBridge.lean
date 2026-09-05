import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Padding
set_option warningAsError true
/-!
# Normalized RIPEMD-160 target for direct-bytecode proofs

The execution proof consumes one already-padded memory image.  This stable
model states that target independently of the reference program's control
flow and stack convention.
-/

namespace Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.SpecBridge

open EvmSemantics.Crypto

def absorbBlocks (h : Array UInt32) (bs : ByteArray) (base count : Nat) :
    Array UInt32 :=
  (List.range count).foldl
    (fun state block => Ripemd160.compressBlock state bs (base + block * 64)) h

def emitDigest (h : Array UInt32) : ByteArray :=
  (List.range 5).foldl
    (fun output i => Ripemd160.writeLE32 output h[i]!) ByteArray.empty

def paddedHash (input : ByteArray) : ByteArray :=
  emitDigest (absorbBlocks Ripemd160.H0 (Padding.paddedMessage input) 0
    (Padding.paddedLength input.size / 64))

@[simp] theorem absorbBlocks_zero (h : Array UInt32) (bs : ByteArray)
    (base : Nat) : absorbBlocks h bs base 0 = h := by
  rfl

theorem absorbBlocks_succ (h : Array UInt32) (bs : ByteArray)
    (base count : Nat) :
    absorbBlocks h bs base (count + 1) =
      Ripemd160.compressBlock (absorbBlocks h bs base count) bs
        (base + count * 64) := by
  simp [absorbBlocks, List.range_succ, List.foldl_append]

end Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.SpecBridge

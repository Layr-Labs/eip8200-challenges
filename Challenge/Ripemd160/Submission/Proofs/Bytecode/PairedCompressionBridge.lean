import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCryptoBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCompressionBridge

open EvmSemantics PairedLaneCryptoBridge

def toWorking (q : CryptoLane) : Compression.Working :=
  ⟨q.a, q.b, q.c, q.d, q.e⟩

def ofWorking (q : Compression.Working) : CryptoLane :=
  ⟨q.a, q.b, q.c, q.d, q.e⟩

theorem working_roundtrip (q : Compression.Working) :
    toWorking (ofWorking q) = q := by cases q; rfl

theorem lane_roundtrip (q : CryptoLane) :
    ofWorking (toWorking q) = q := by cases q; rfl

theorem projected_step (j r : Nat) (word k : UInt32) (q : CryptoLane) :
    toWorking (cryptoStep j r word k q) =
      Compression.round (toWorking q) j word r k := by rfl

theorem projected_left_fold (words : Nat → UInt32)
    (fold : Nat → CryptoLane → CryptoLane)
    (hz : ∀ q, fold 0 q = q)
    (hs : ∀ i q, fold (i + 1) q =
      cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
        (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! (fold i q))
    (count : Nat) (q : CryptoLane) :
    toWorking (fold count q) = CompressionCorrect.leftRounds words count (toWorking q) := by
  induction count with
  | zero => rw [hz]; rfl
  | succ i ih =>
    rw [hs, projected_step, CompressionCorrect.leftRounds, ih]
    rfl

theorem projected_right_fold (words : Nat → UInt32)
    (fold : Nat → CryptoLane → CryptoLane)
    (hz : ∀ q, fold 0 q = q)
    (hs : ∀ i q, fold (i + 1) q =
      cryptoStep (4 - i / 16) Crypto.Ripemd160.sP[i]!
        (words Crypto.Ripemd160.rP[i]!) Crypto.Ripemd160.KP[i / 16]! (fold i q))
    (count : Nat) (q : CryptoLane) :
    toWorking (fold count q) = CompressionCorrect.rightRounds words count (toWorking q) := by
  induction count with
  | zero => rw [hz]; rfl
  | succ i ih =>
    rw [hs, projected_step, CompressionCorrect.rightRounds, ih]
    rfl

/-- The right-plus-left grouping used by the raw paired tail. -/
def combineLanes (h : Compression.HashState) (left right : CryptoLane) :
    Compression.HashState :=
  ⟨h.h1 + (right.d + left.c), h.h2 + (right.e + left.d),
    h.h3 + (right.a + left.e), h.h4 + (right.b + left.a),
    h.h0 + (right.c + left.b)⟩

theorem projected_combination (h : Compression.HashState) (left right : CryptoLane) :
    combineLanes h left right = Compression.combine h (toWorking left) (toWorking right) := by
  have rearrange (a b c : UInt32) : a + (c + b) = a + b + c := by
    rw [UInt32.add_comm c b, UInt32.add_assoc]
  simp only [combineLanes, Compression.combine, toWorking, rearrange]

/-- A parametric fold interface: actual core folds discharge its equations by rfl. -/
theorem paired_compression_eq_spec (bs : ByteArray) (blockOff : Nat)
    (h : Compression.HashState)
    (leftFold rightFold : Nat → CryptoLane → CryptoLane)
    (hlz : ∀ q, leftFold 0 q = q)
    (hrz : ∀ q, rightFold 0 q = q)
    (hls : ∀ i q, leftFold (i + 1) q =
      cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
        ((CompressionCorrect.schedule bs blockOff)[Crypto.Ripemd160.r[i]!]!)
        Crypto.Ripemd160.K[i / 16]! (leftFold i q))
    (hrs : ∀ i q, rightFold (i + 1) q =
      cryptoStep (4 - i / 16) Crypto.Ripemd160.sP[i]!
        ((CompressionCorrect.schedule bs blockOff)[Crypto.Ripemd160.rP[i]!]!)
        Crypto.Ripemd160.KP[i / 16]! (rightFold i q)) :
    CompressionCorrect.hashArray (combineLanes h
      (leftFold 80 (ofWorking (CompressionCorrect.workingOfHash h)))
      (rightFold 80 (ofWorking (CompressionCorrect.workingOfHash h)))) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs blockOff := by
  rw [projected_combination,
    projected_left_fold _ leftFold hlz hls,
    projected_right_fold _ rightFold hrz hrs,
    working_roundtrip]
  exact CompressionCorrect.compressModel_eq_compressBlock bs blockOff h

#print axioms working_roundtrip
#print axioms lane_roundtrip
#print axioms projected_step
#print axioms projected_left_fold
#print axioms projected_right_fold
#print axioms projected_combination
#print axioms paired_compression_eq_spec

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCompressionBridge

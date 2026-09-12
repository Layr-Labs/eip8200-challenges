import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordBooleanBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGroupTwoHoist
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordGroupTwo
open EvmSemantics Paired144Core Paired144WordRound PairedLaneUInt256Bridge
open PairedLaneGroupTwoHoist (Supported newBoolean oldBoolean adjustedConstant newBoolean_add_adjusted)

theorem pack_supported (a b : BitVec 32) : Supported pairMask (pack a b) := by
  unfold Supported
  rw [← normalize_eq_and, normalize_pack]

theorem bits_hoistedBoolean (b c d : UInt256) :
    bits (hoistedBoolean b c d) = newBoolean (bits b) (bits c) (bits d) := by
  calc
    bits (hoistedBoolean b c d) =
        bits (UInt256.lor (UInt256.lnot c) b) ^^^ bits d := bits_xor _ _
    _ = (bits (UInt256.lnot c) ||| bits b) ^^^ bits d :=
      congrArg (fun x : BitVec 256 => x ^^^ bits d) (bits_lor _ _)
    _ = newBoolean (bits b) (bits c) (bits d) :=
      congrArg (fun x : BitVec 256 => (x ||| bits b) ^^^ bits d) (bits_lnot c)

#print axioms bits_hoistedBoolean

theorem rawHoistedBoolean_eq (b c d : UInt256) :
    rawHoistedBoolean b c d = hoistedBoolean b c d := by
  apply bits_injective
  simp only [rawHoistedBoolean, hoistedBoolean, bits_xor, bits_lor]
  calc
    bits d ^^^ (bits b ||| bits (UInt256.lnot c)) =
        (bits b ||| bits (UInt256.lnot c)) ^^^ bits d := BitVec.xor_comm _ _
    _ = (bits (UInt256.lnot c) ||| bits b) ^^^ bits d :=
      congrArg (fun x : BitVec 256 => x ^^^ bits d) (BitVec.or_comm _ _)

#print axioms rawHoistedBoolean_eq

theorem bits_adjustedK (k : UInt256) :
    bits (adjustedK k) = adjustedConstant pairMask (bits k) := by
  calc
    bits (adjustedK k) =
        bits (UInt256.add k pairWord) + bits (UInt256.ofNat 1) := bits_add _ _
    _ = (bits k + bits pairWord) + BitVec.ofNat 256 1 :=
      congrArg₂ (fun x y : BitVec 256 => x + y) (bits_add k pairWord) (bits_ofNat 1)
    _ = adjustedConstant pairMask (bits k) :=
      congrArg (fun x : BitVec 256 => (bits k + x) + 1#256) (bits_word pairMask)

#print axioms bits_adjustedK

/-- No support premise is needed for K; only B/C/D occupy the two lanes. -/
theorem boolean_add_adjusted (b c d k : UInt256)
    (hb : Supported pairMask (bits b)) (hc : Supported pairMask (bits c))
    (hd : Supported pairMask (bits d)) :
    UInt256.add (hoistedBoolean b c d) (adjustedK k) =
      UInt256.add (booleanPair 2 b c d) k := by
  apply bits_injective
  calc
    bits (UInt256.add (hoistedBoolean b c d) (adjustedK k)) =
        bits (hoistedBoolean b c d) + bits (adjustedK k) := bits_add _ _
    _ = newBoolean (bits b) (bits c) (bits d) + adjustedConstant pairMask (bits k) :=
      congrArg₂ (fun x y : BitVec 256 => x + y)
        (bits_hoistedBoolean b c d) (bits_adjustedK k)
    _ = oldBoolean pairMask (bits b) (bits c) (bits d) + bits k :=
      newBoolean_add_adjusted pairMask (bits b) (bits c) (bits d) (bits k) hb hc hd
    _ = bits (booleanPair 2 b c d) + bits k :=
      congrArg (fun x : BitVec 256 => x + bits k) (Paired144WordBooleanBridge.bits_booleanPair 2 b c d).symm
    _ = bits (UInt256.add (booleanPair 2 b c d) k) := (bits_add _ _).symm

#print axioms boolean_add_adjusted

theorem add_rearrange (a f m k : UInt256) :
    UInt256.add (UInt256.add (UInt256.add a f) m) k =
      UInt256.add (UInt256.add a m) (UInt256.add f k) := by
  apply bits_injective
  change ((bits a + bits f) + bits m) + bits k = (bits a + bits m) + (bits f + bits k)
  ac_rfl

theorem hoistedSum_eq (a b c d message k : UInt256)
    (hb : Supported pairMask (bits b)) (hc : Supported pairMask (bits c))
    (hd : Supported pairMask (bits d)) :
    hoistedSum a b c d message (adjustedK k) = wordSum 2 a b c d message k := by
  unfold hoistedSum wordSum
  exact (add_rearrange a (hoistedBoolean b c d) message (adjustedK k)).trans
    ((congrArg (fun z => UInt256.add (UInt256.add a message) z)
      (boolean_add_adjusted b c d k hb hc hd)).trans
      (add_rearrange a (booleanPair 2 b c d) message k).symm)

theorem rawWordStep2_eq (r s : Nat) (message k : UInt256) (q : WordLane)
    (hb : Supported pairMask (bits q.b)) (hc : Supported pairMask (bits q.c))
    (hd : Supported pairMask (bits q.d)) :
    rawWordStep2 r s message (adjustedK k) q = wordStep 2 r s message k q := by
  exact congrArg
    (fun x : UInt256 => PairedLaneWordRound.WordLane.mk q.e
      (UInt256.land (UInt256.add (wordRotate x r s) q.e) pairWord) q.b
      (UInt256.land (wordShift q.c 28) pairWord) q.d)
    (hoistedSum_eq q.a q.b q.c q.d message k hb hc hd)

theorem packCrypto_supported (l q : CryptoLane) :
    Supported pairMask (bits (packCrypto l q).b) ∧
    Supported pairMask (bits (packCrypto l q).c) ∧
    Supported pairMask (bits (packCrypto l q).d) :=
  ⟨pack_supported l.b.toBitVec q.b.toBitVec, pack_supported l.c.toBitVec q.c.toBitVec,
    pack_supported l.d.toBitVec q.d.toBitVec⟩

#print axioms boolean_add_adjusted
#print axioms hoistedSum_eq
#print axioms rawWordStep2_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordGroupTwo

import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGroupTwoHoist
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordGroupTwoHoist

open EvmSemantics
open PairedLaneCore PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedLaneWordRotate PairedLaneWordRound PairedLaneGroupTwoHoist

def hoistedBoolean (b c d : UInt256) : UInt256 :=
  UInt256.xor (UInt256.lor (UInt256.lnot c) b) d

/-- The operand order emitted by the new inline EVM template. -/
def rawHoistedBoolean (b c d : UInt256) : UInt256 :=
  UInt256.xor d (UInt256.lor b (UInt256.lnot c))

def adjustedK (k : UInt256) : UInt256 :=
  UInt256.add (UInt256.add k pairWord) (UInt256.ofNat 1)

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
      congrArg (fun x : BitVec 256 => x + bits k) (bits_booleanPair 2 b c d).symm
    _ = bits (UInt256.add (booleanPair 2 b c d) k) := (bits_add _ _).symm

#print axioms boolean_add_adjusted

theorem add_rearrange (a f m k : UInt256) :
    UInt256.add (UInt256.add (UInt256.add a f) m) k =
      UInt256.add (UInt256.add a m) (UInt256.add f k) := by
  apply bits_injective
  change ((bits a + bits f) + bits m) + bits k =
    (bits a + bits m) + (bits f + bits k)
  ac_rfl

#print axioms add_rearrange

def hoistedSum (a b c d message cachedK : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.add (UInt256.add (UInt256.add a (hoistedBoolean b c d)) message) cachedK)
    pairWord

theorem hoistedSum_eq (a b c d message k : UInt256)
    (hb : Supported pairMask (bits b)) (hc : Supported pairMask (bits c))
    (hd : Supported pairMask (bits d)) :
    hoistedSum a b c d message (adjustedK k) = wordSum 2 a b c d message k := by
  exact congrArg (fun x : UInt256 => UInt256.land x pairWord) (calc
    UInt256.add (UInt256.add (UInt256.add a (hoistedBoolean b c d)) message) (adjustedK k) =
        UInt256.add (UInt256.add a message) (UInt256.add (hoistedBoolean b c d) (adjustedK k)) :=
      add_rearrange a (hoistedBoolean b c d) message (adjustedK k)
    _ = UInt256.add (UInt256.add a message) (UInt256.add (booleanPair 2 b c d) k) :=
      congrArg (fun x : UInt256 => UInt256.add (UInt256.add a message) x)
        (boolean_add_adjusted b c d k hb hc hd)
    _ = UInt256.add (UInt256.add (UInt256.add a (booleanPair 2 b c d)) message) k :=
      (add_rearrange a (booleanPair 2 b c d) message k).symm)

#print axioms hoistedSum_eq

def hoistedT (r s : Nat) (a b c d e message cachedK : UInt256) : UInt256 :=
  UInt256.land (UInt256.add (wordRotate (hoistedSum a b c d message cachedK) r s) e) pairWord

theorem hoistedT_eq (r s : Nat) (a b c d e message k : UInt256)
    (hb : Supported pairMask (bits b)) (hc : Supported pairMask (bits c))
    (hd : Supported pairMask (bits d)) :
    hoistedT r s a b c d e message (adjustedK k) = wordT 2 r s a b c d e message k := by
  exact congrArg
    (fun x : UInt256 => UInt256.land (UInt256.add (wordRotate x r s) e) pairWord)
    (hoistedSum_eq a b c d message k hb hc hd)

#print axioms hoistedT_eq

/-- A distinct raw transition for the new group-two instructions.
It is defined on every raw WordLane and every cached constant. It is NOT
identified with the old raw transition on unnormalized inputs. -/
def rawWordStep2 (r s : Nat) (message cachedK : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, hoistedT r s q.a q.b q.c q.d q.e message cachedK, q.b,
    UInt256.land (wordShift q.c 22) pairWord, q.d⟩

theorem rawWordStep2_eq_of_supported (r s : Nat) (message k : UInt256) (q : WordLane)
    (hb : Supported pairMask (bits q.b)) (hc : Supported pairMask (bits q.c))
    (hd : Supported pairMask (bits q.d)) :
    rawWordStep2 r s message (adjustedK k) q = wordStep 2 r s message k q := by
  exact congrArg
    (fun x : UInt256 => WordLane.mk q.e x q.b
      (UInt256.land (wordShift q.c 22) pairWord) q.d)
    (hoistedT_eq r s q.a q.b q.c q.d q.e message k hb hc hd)

#print axioms rawWordStep2_eq_of_supported

theorem packCrypto_supported (l q : PairedLaneCryptoBridge.CryptoLane) :
    Supported pairMask (bits (packCrypto l q).b) ∧
      Supported pairMask (bits (packCrypto l q).c) ∧
      Supported pairMask (bits (packCrypto l q).d) := by
  exact ⟨pack_supported l.b.toBitVec q.b.toBitVec,
    pack_supported l.c.toBitVec q.c.toBitVec, pack_supported l.d.toBitVec q.d.toBitVec⟩

#print axioms packCrypto_supported

theorem rawWordStep2_of_crypto (r s : Nat)
    (hr0 : 0 < r) (hr : r < 32) (hs0 : 0 < s) (hs : s < 32)
    (wl wr kl kr : UInt32) (l q : PairedLaneCryptoBridge.CryptoLane) :
    rawWordStep2 r s (word (pack wl.toBitVec wr.toBitVec))
        (adjustedK (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      packCrypto (PairedLaneCryptoBridge.cryptoStep 2 r wl kl l)
        (PairedLaneCryptoBridge.cryptoStep 2 s wr kr q) := by
  obtain ⟨hb, hc, hd⟩ := packCrypto_supported l q
  exact (rawWordStep2_eq_of_supported r s
    (word (pack wl.toBitVec wr.toBitVec)) (word (pack kl.toBitVec kr.toBitVec))
    (packCrypto l q) hb hc hd).trans
      (wordStep_of_crypto 2 r s hr0 hr hs0 hs wl wr kl kr l q)


#print axioms rawWordStep2_of_crypto

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordGroupTwoHoist

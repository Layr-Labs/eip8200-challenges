import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Algorithm
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Compression
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80WordRound
open Paired80CryptoBridge (CryptoLane)
open Paired80Algorithm

def low32 (x : UInt256) : UInt32 := UInt32.ofNat x.toNat

def high32 (x : UInt256) : UInt32 := low32 (UInt256.shiftRight x (UInt256.ofNat 80))

theorem low32_packed (a b : UInt32) : low32 (packed32 a b) = a := by
  apply UInt32.eq_of_toBitVec_eq
  change (bits (packed32 a b)).setWidth 32 = a.toBitVec
  rw [packed32, bits_word, BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 256)]
  exact low_pack a.toBitVec b.toBitVec

theorem high32_packed (a b : UInt32) : high32 (packed32 a b) = b := by
  apply UInt32.eq_of_toBitVec_eq
  change (bits (UInt256.shiftRight (packed32 a b) (UInt256.ofNat 80))).setWidth 32 = b.toBitVec
  rw [bits_shr _ 80 (by decide), packed32, bits_word,
    BitVec.setWidth_ushiftRight_eq_extractLsb]
  exact high_pack a.toBitVec b.toBitVec

def unpackLeft (q : WordLane) : CryptoLane :=
  ⟨low32 q.a, low32 q.b, low32 q.c, low32 q.d, low32 q.e⟩

def unpackRight (q : WordLane) : CryptoLane :=
  ⟨high32 q.a, high32 q.b, high32 q.c, high32 q.d, high32 q.e⟩

theorem unpackLeft_packCrypto (l q : CryptoLane) : unpackLeft (packCrypto l q) = l := by
  cases l; cases q
  simp only [unpackLeft, packCrypto, liftLane, Paired80RoundSemantic.packLane,
    PairedLaneCryptoBridge.bits]
  change (⟨low32 (packed32 _ _), low32 (packed32 _ _), low32 (packed32 _ _),
    low32 (packed32 _ _), low32 (packed32 _ _)⟩ : CryptoLane) = _
  simp only [low32_packed]

theorem unpackRight_packCrypto (l q : CryptoLane) : unpackRight (packCrypto l q) = q := by
  cases l; cases q
  simp only [unpackRight, packCrypto, liftLane, Paired80RoundSemantic.packLane,
    PairedLaneCryptoBridge.bits]
  change (⟨high32 (packed32 _ _), high32 (packed32 _ _), high32 (packed32 _ _),
    high32 (packed32 _ _), high32 (packed32 _ _)⟩ : CryptoLane) = _
  simp only [high32_packed]

def combine (h : Compression.HashState) (q : WordLane) : Compression.HashState :=
  PairedCompressionBridge.combineLanes h (unpackLeft q) (unpackRight q)

theorem combine_packCrypto (h : Compression.HashState) (l q : CryptoLane) :
    combine h (packCrypto l q) = PairedCompressionBridge.combineLanes h l q := by
  rw [combine, unpackLeft_packCrypto, unpackRight_packCrypto]

theorem fold_compression (bs : ByteArray) (off : Nat) (h : Compression.HashState)
    (message : Nat → UInt256)
    (hm : MessageReady message (fun k => (CompressionCorrect.schedule bs off)[k]!) 80) :
    CompressionCorrect.hashArray
      (combine h (fold message 80 (packCrypto
        (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))
        (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))))) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs off := by
  rw [fold_crypto message (fun k => (CompressionCorrect.schedule bs off)[k]!)
      80 (by decide) _ _ hm, combine_packCrypto]
  exact PairedCompressionBridge.paired_compression_eq_spec bs off h
    (leftFold (fun k => (CompressionCorrect.schedule bs off)[k]!))
    (rightFold (fun k => (CompressionCorrect.schedule bs off)[k]!))
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

#print axioms low32_packed
#print axioms high32_packed
#print axioms unpackLeft_packCrypto
#print axioms unpackRight_packCrypto
#print axioms fold_compression
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Compression

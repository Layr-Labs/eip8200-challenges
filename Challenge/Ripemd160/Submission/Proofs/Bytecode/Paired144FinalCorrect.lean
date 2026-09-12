import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144AlgorithmCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailBinding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCompressionBridge
set_option warningAsError true
set_option maxRecDepth 8000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144FinalCorrect
open EvmSemantics Paired144Core Paired144WordRound PairedLaneUInt256Bridge
open Paired144Algorithm PersistentTailBinding

theorem normalizeWord_eq_land (x : UInt256) :
    normalizeWord x = UInt256.land x pairWord := by
  apply bits_injective
  simp only [normalizeWord,bits_word,bits_land,pairWord,normalize_eq_and]

@[simp] theorem normalizeWord_pack (a b : BitVec 32) :
    normalizeWord (word (pack a b)) = word (pack a b) := by
  rw [normalizeWord,bits_word,normalize_pack]

@[simp] theorem normalizeLane_packCrypto (l q : CryptoLane) :
    normalizeLane (packCrypto l q) = packCrypto l q := by
  simp only [normalizeLane,packCrypto,normalizeWord_pack]

theorem rawFinish_normalized (r s : Nat) (message k : UInt256) (l q : CryptoLane) :
    normalizeLane (rawFinish r s message k (packCrypto l q)) =
      wordStep 4 r s message k (packCrypto l q) := by
  simp only [normalizeLane,rawFinish,wordStep,wordT,packCrypto,normalizeWord_pack]
  simp only [normalizeWord_eq_land]

theorem finalLane_normalized (message : Nat → UInt256) (words : Nat → UInt32)
    (l q : CryptoLane) (hm : MessageReady message words 80) :
    normalizeLane (finalLane message (packCrypto l q)) =
      packCrypto (leftFold words 80 l) (rightFold words 80 q) := by
  have hm79 : MessageReady message words 79 := fun i hi => hm i (by omega)
  rw [finalLane,fold_crypto message words 79 (by decide) l q hm79,finish,rawFinish_normalized]
  have h := step_of_crypto words 79 (by decide) (message 79)
    (leftFold words 79 l) (rightFold words 79 q) (hm 79 (by decide))
  exact h

theorem final_combine (message : Nat → UInt256) (words : Nat → UInt32)
    (h : Compression.HashState) (l q : CryptoLane) (hm : MessageReady message words 80) :
    combine h (finalLane message (packCrypto l q)) =
      PairedCompressionBridge.combineLanes h (leftFold words 80 l) (rightFold words 80 q) := by
  rw [←combine_normalize,finalLane_normalized message words l q hm,combine_packCrypto]
  have rearrange (a b c : UInt32) : a+b+c = a+(c+b) := by
    rw [UInt32.add_comm c b, UInt32.add_assoc]
  simp only [PairedCompressionBridge.combineLanes,rearrange]

theorem final_compression (bs : ByteArray) (off : Nat) (h : Compression.HashState)
    (message : Nat → UInt256)
    (hm : MessageReady message (fun k => (CompressionCorrect.schedule bs off)[k]!) 80) :
    CompressionCorrect.hashArray
      (combine h (finalLane message (packCrypto
        (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))
        (PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h))))) =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs off := by
  rw [final_combine message (fun k => (CompressionCorrect.schedule bs off)[k]!) h _ _ hm]
  exact PairedCompressionBridge.paired_compression_eq_spec bs off h
    (leftFold (fun k => (CompressionCorrect.schedule bs off)[k]!))
    (rightFold (fun k => (CompressionCorrect.schedule bs off)[k]!))
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

#print axioms rawFinish_normalized
#print axioms finalLane_normalized
#print axioms final_combine
#print axioms final_compression
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144FinalCorrect

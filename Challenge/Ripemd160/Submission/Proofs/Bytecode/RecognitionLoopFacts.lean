import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLoopFacts
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RecognitionFrame RecognitionBodyRaw RecognitionAccumulator RecognitionRecurrence

theorem off_toNat (input : ByteArray) (n k : Nat) (hk : k ≤ 31) :
    (fullFrame input n k).off.toNat = 32*k := by
  change (UInt256.ofNat (32*k)).toNat = _
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem full_toNat (input : ByteArray) (n k : Nat) (hn : Allowed n) :
    (fullFrame input n k).full.toNat = 32*(n/32) := by
  have h := allowed_bounds n hn
  change (UInt256.ofNat (32*(n/32))).toNat = _
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem stop_toNat (input : ByteArray) (n k : Nat) (hn : Allowed n) :
    (fullFrame input n k).stop.toNat = stop n k := by
  have h := allowed_bounds n hn
  have hs : stop n k ≤ 32*(n/32) := Nat.min_le_left _ _
  change (UInt256.ofNat (stop n k)).toNat = _
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem lt_stop_iff (input : ByteArray) (n k : Nat) (hn : Allowed n) (hk : k ≤ n/32) :
    (fullFrame input n k).off.toNat < (fullFrame input n k).stop.toNat ↔
      k < n/32 ∧ boundary k = false := by
  have h := allowed_bounds n hn
  rw [off_toNat input n k (by omega), stop_toNat input n k hn]
  simp only [stop, lt_min_iff, boundary, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  omega

theorem off_lt_full_iff (input : ByteArray) (n k : Nat) (hn : Allowed n) (hk : k ≤ n/32) :
    (fullFrame input n k).off.toNat < (fullFrame input n k).full.toNat ↔ k < n/32 := by
  have h := allowed_bounds n hn
  rw [off_toNat input n k (by omega), full_toNat input n k hn]
  omega

theorem off_eq_size_iff (input : ByteArray) (n : Nat) (hn : Allowed n) (hsize : input.size=n) :
    (fullFrame input n (n/32)).off.toNat = input.size % 2^256 ↔ n % 32 = 0 := by
  have h := allowed_bounds n hn
  rw [off_toNat input n (n/32) (by omega), hsize, Nat.mod_eq_of_lt (by omega)]
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLoopFacts

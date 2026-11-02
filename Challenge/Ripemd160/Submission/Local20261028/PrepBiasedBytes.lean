import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolByte
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.BiasedBytes
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def key : Nat := 2840853838
def source (a w t : Nat) : Nat := a * 2^192 + w * 2^144 + t
theorem byte_unchanged (a w t j : Nat)
    (ha : a < 2^64) (hw : w < 2^32) (ht : t < 2^144)
    (hj : j < 32) (hregion : j < 9 ∨ 14 ≤ j) :
    PoolByte.byte (UInt256.ofNat (source a w t + key * 2^144)) j =
      PoolByte.byte (UInt256.ofNat (source a w t)) j := by
  have hbound : source a w t + key * 2^144 < 2^256 := by
    unfold source key
    norm_num at *
    omega
  have hbase : source a w t < 2^256 := lt_of_le_of_lt (Nat.le_add_right _ _) hbound
  apply UInt8.toNat_inj.mp
  simp only [PoolByte.byte_toNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt hbase]
  unfold source key
  interval_cases j <;> norm_num at * <;> omega
theorem source_parts (v : UInt256)
    (h8 : PoolByte.byte v 8 = 0) (h9 : PoolByte.byte v 9 = 0) :
    v.toNat = source (v.toNat / 2^192) (v.toNat / 2^144 % 2^32) (v.toNat % 2^144) := by
  have e8 := congrArg UInt8.toNat h8
  have e9 := congrArg UInt8.toNat h9
  simp only [PoolByte.byte_toNat] at e8 e9
  change v.toNat / 2^184 % 256 = 0 at e8
  change v.toNat / 2^176 % 256 = 0 at e9
  unfold source
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] at e8 e9 ⊢
  omega

theorem word_byte_unchanged (v : UInt256)
    (h8 : PoolByte.byte v 8 = 0) (h9 : PoolByte.byte v 9 = 0)
    (j : Nat) (hj : j < 32) (hr : j < 9 ∨ 14 ≤ j) :
    PoolByte.byte (UInt256.add (UInt256.ofNat (key * 2^144)) v) j = PoolByte.byte v j := by
  have hv := source_parts v h8 h9
  have ha : v.toNat / 2^192 < 2^64 := by
    have hbound : v.toNat < 2^256 := v.val.isLt
    norm_num only [Nat.reducePow] at hbound ⊢
    omega
  have hw : v.toNat / 2^144 % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
  have ht : v.toNat % 2^144 < 2^144 := Nat.mod_lt _ (by decide)
  have hword : UInt256.ofNat (source (v.toNat / 2^192) (v.toNat / 2^144 % 2^32) (v.toNat % 2^144)) = v := by
    rw [← hv]
    exact (Word.word_eq_ofNat_toNat v).symm
  have hadd : UInt256.add (UInt256.ofNat (key*2^144)) v =
      UInt256.ofNat (source (v.toNat / 2^192) (v.toNat / 2^144 % 2^32) (v.toNat % 2^144) + key*2^144) := by
    apply Word.word_ext
    change (UInt256.ofNat (key*2^144) + v).toNat = _
    rw [Word.word_toNat_add, Word.word_toNat_ofNat, Word.word_toNat_ofNat, ← hv]
    simp only [Nat.add_mod, Nat.mod_mod, Nat.add_comm]
  rw [hadd]
  exact (byte_unchanged _ _ _ j ha hw ht hj hr).trans (congrArg (fun w => PoolByte.byte w j) hword)
def consumer (h w : Nat) : Nat := h * 2^48 + w

theorem consumer_before (h w j : Nat)
    (hh : h<2^208) (hw : w<2^32) (hj : j<27) :
    PoolByte.byte (UInt256.ofNat (consumer h w + key)) j =
      PoolByte.byte (UInt256.ofNat (consumer h w)) j := by
  have hbound : consumer h w + key < 2^256 := by
    unfold consumer key
    norm_num at *
    omega
  have hbase : consumer h w < 2^256 := lt_of_le_of_lt (Nat.le_add_right _ _) hbound
  apply UInt8.toNat_inj.mp
  simp only [PoolByte.byte_toNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt hbase]
  unfold consumer key
  interval_cases j <;> norm_num at * <;> omega

theorem consumer_after (h a w t j : Nat)
    (hh : h<2^208) (ha : a<2^64) (hw : w<2^32) (ht : t<2^144)
    (hj : 27≤j) (hj' : j<32) :
    PoolByte.byte (UInt256.ofNat (consumer h w + key)) j =
      PoolByte.byte (UInt256.ofNat (source a w t + key*2^144)) (j-18) := by
  have hu : consumer h w + key < 2^256 := by
    unfold consumer key
    norm_num at *
    omega
  have hv : source a w t + key*2^144 < 2^256 := by
    unfold source key
    norm_num at *
    omega
  apply UInt8.toNat_inj.mp
  simp only [PoolByte.byte_toNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]
  unfold consumer source key
  interval_cases j <;> norm_num at * <;> omega
#print axioms consumer_before
#print axioms consumer_after
#print axioms source_parts
#print axioms word_byte_unchanged
#print axioms byte_unchanged
end RipemdSubmission20261101.BiasedBytes

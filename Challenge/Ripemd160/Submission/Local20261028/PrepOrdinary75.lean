import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinaryReads
import Challenge.Ripemd160.Submission.Local20261028.PrepBias
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.Ordinary75
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RipemdMemoryBridge20261028
open BiasedBytes

def reference (m : ByteArray) : ByteArray :=
  RipemdMemoryBridge20261028.resultMemory (fanMemory m) RipemdTableOrder20261027.selected
theorem reference_bytes (m : ByteArray)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0) (a : Nat) :
    (reference m)[a]?.getD 0 = valuation m (RipemdTableOrder20261027.result RipemdTableOrder20261027.selected a) :=
  result_matches _ _ (actual_fan_matches m hz) (valuation_zero m) _ a
theorem coupled_sources : ∀ j : Fin 6,
    RipemdTableOrder20261027.result RipemdTableOrder20261027.selected (944+j.val) =
      RipemdTableOrder20261027.fan (142+j.val) := by decide +kernel

theorem source_window (m : ByteArray) :
    (MachineState.readWord m 134).toNat / 2^144 % 2^48 =
      Precompile.bytesToNatPadded m 142 6 := by
  have h := Bytes.readWord_shift_toNat m 134 14 (by decide)
  rw [Nat.shiftRight_eq_div_pow, show (32-14)*8=144 from rfl] at h
  rw [h, show (14:Nat)=8+6 from rfl, Bytes.bytesToNatPadded_add]
  have hb := Bytes.bytesToNatPadded_lt_pow m 142 6
  norm_num only [Nat.reducePow, Nat.reduceAdd] at hb ⊢
  omega

theorem coupled_words (m : ByteArray)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0) :
    (MachineState.readWord (reference m) 918).toNat % 2^48 =
      (MachineState.readWord (fanMemory m) 134).toNat / 2^144 % 2^48 := by
  rw [show (2^48:Nat)=256^6 by decide, StaggerTableMemory.readWord_mod_pow _ _ _ (by decide)]
  rw [show (256^6:Nat)=2^48 by decide, source_window]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [reference_bytes m hz, actual_fan_matches m hz, coupled_sources ⟨j,hj⟩]

theorem read_encoded (w : UInt256) :
    MachineState.readWord (Data.Bytes.natToBytesPadded w.toNat 32) 0 = w := by
  apply Word.word_ext
  unfold MachineState.readWord
  rw [Word.word_toNat_ofNat]
  have hs : (Data.Bytes.natToBytesPadded w.toNat 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hr : MachineState.readPadded (Data.Bytes.natToBytesPadded w.toNat 32) 0 32 = Data.Bytes.natToBytesPadded w.toNat 32 := by
    simpa only [hs] using Memory.readPadded_zero_size (Data.Bytes.natToBytesPadded w.toNat 32)
  rw [hr, Memory.bytesToBigEndianNat_natToBytesPadded _ _ (by exact w.val.isLt)]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem read_eq_of_bytes (m : ByteArray) (a : Nat) (w : UInt256)
    (h : ∀ j, j<32 → m[a+j]?.getD 0 = PoolByte.byte w j) :
    MachineState.readWord m a = w := by
  rw [← read_encoded w]
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [h j hj, Nat.zero_add, PoolByte.encoded w j hj]

theorem read_add (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0) :
    MachineState.readWord (OrdinaryTable.result7 s x rho).memory 918 =
      UInt256.add (UInt256.ofNat key) (MachineState.readWord (reference s.memory) 918) := by
  let v := MachineState.readWord (fanMemory s.memory) 134
  let u := MachineState.readWord (reference s.memory) 918
  let a := v.toNat / 2^192
  let w := v.toNat / 2^144 % 2^32
  let t := v.toNat % 2^144
  let h := u.toNat / 2^48
  have hv8 : PoolByte.byte v 8 = 0 := by
    rw [PoolByte.read _ _ _ (by decide), actual_fan_matches s.memory hz]
    rfl
  have hv9 : PoolByte.byte v 9 = 0 := by
    rw [PoolByte.read _ _ _ (by decide), actual_fan_matches s.memory hz]
    rfl
  have hv : v.toNat = source a w t := source_parts v hv8 hv9
  have ha : a<2^64 := by
    have hb : v.toNat<2^256 := v.val.isLt
    dsimp [a]
    norm_num only [Nat.reducePow] at hb ⊢
    omega
  have hw : w<2^32 := Nat.mod_lt _ (by decide)
  have ht : t<2^144 := Nat.mod_lt _ (by decide)
  have hh : h<2^208 := by
    have hb : u.toNat<2^256 := u.val.isLt
    dsimp [h]
    norm_num only [Nat.reducePow] at hb ⊢
    omega
  have hlow : u.toNat % 2^48 = w := by
    have hc := coupled_words s.memory hz
    change u.toNat % 2^48 = v.toNat / 2^144 % 2^48 at hc
    rw [hv] at hc
    unfold source at hc
    norm_num only [Nat.reducePow] at hc hw ht ⊢
    omega
  have hu : u.toNat = consumer h w := by
    unfold consumer
    rw [← hlow]
    simpa only [h, Nat.mul_comm] using (Nat.div_add_mod u.toNat (2^48)).symm
  have huword : UInt256.ofNat (consumer h w) = u := by
    rw [← hu]
    exact (Word.word_eq_ofNat_toNat u).symm
  have hub : UInt256.add (UInt256.ofNat key) u = UInt256.ofNat (consumer h w + key) := by
    apply Word.word_ext
    change (UInt256.ofNat key + u).toNat = _
    rw [Word.word_toNat_add, Word.word_toNat_ofNat, Word.word_toNat_ofNat, ← hu]
    simp only [Nat.add_mod, Nat.mod_mod, Nat.add_comm]
  have hvb : OrdinaryBytes.biased s.memory = UInt256.ofNat (source a w t + key*2^144) := by
    apply Word.word_ext
    change (UInt256.ofNat (key*2^144) + v).toNat = _
    rw [Word.word_toNat_add, Word.word_toNat_ofNat, Word.word_toNat_ofNat, ← hv]
    simp only [Nat.add_mod, Nat.mod_mod, Nat.add_comm]
  change MachineState.readWord _ _ = UInt256.add (UInt256.ofNat key) u
  rw [hub]
  apply read_eq_of_bytes
  intro j hj
  by_cases hj27 : j<27
  · rw [consumer_before h w j hh hw hj27, huword, PoolByte.read _ _ _ hj]
    have hidx : 918+j<1120 := by omega
    have hbefore : 918+j<945 := by omega
    have hc := OrdinaryCertificate.unchanged_sources (⟨918+j,hidx⟩ : Fin 1120) (Or.inl hbefore)
    rw [OrdinaryBytes.actual_bytes s x rho hz,
      hc,
      reference_bytes s.memory hz]
    rfl
  · have hk : j-27<5 := by omega
    have he : 918+j = 945+(j-27) := by omega
    rw [OrdinaryBytes.actual_bytes s x rho hz, he, OrdinaryCertificate.biased_sources ⟨j-27,hk⟩]
    change PoolByte.byte (OrdinaryBytes.biased s.memory) (9+(j-27)) = _
    rw [hvb, show 9+(j-27)=j-18 by omega]
    exact (consumer_after h a w t j hh ha hw ht (by omega) hj).symm
#print axioms coupled_words
#print axioms read_add
end RipemdSubmission20261101.Ordinary75

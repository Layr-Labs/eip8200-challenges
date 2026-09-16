import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Pool

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Slot-indexed table reads, and the round message from a slot-indexed junk budget

The 48-store writer elides thirteen slots and recovers them from the dual lane of the slot
above.  The elided slot then holds the HIGH half of that stored word and the surviving slot
holds its LOW half, so the two carry the SAME schedule word with DIFFERENT junk.  A word-indexed
table function cannot express that, and `StaggerTableLayout.tableWords` is word-indexed, so the
JD8 table image is described by a SLOT-indexed function instead.

`StaggerTableMemory.read_pair_wide` is already stated over an arbitrary slot function; what it
lacks is the truncating form, which needs no hypothesis at all: a table read keeps the low 144
bits of its own slot and the low 112 bits of the slot below, whatever those slots hold.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Table
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof PairedLaneUInt256Bridge Paired144Core
open StaggerTableMemory

/-- Local re-proof of `StaggerTableMemory.readWord_encoded`, which is `private` there and so is
not visible from this module.  Body copied verbatim. -/
private theorem readWord_encoded (value : UInt256) :
    MachineState.readWord (Data.Bytes.natToBytesPadded value.toNat 32) 0 = value := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat]
  unfold Precompile.bytesToNatPadded
  have hs : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hr : MachineState.readPadded (Data.Bytes.natToBytesPadded value.toNat 32) 0 32
      = Data.Bytes.natToBytesPadded value.toNat 32 := by
    simpa only [hs] using Memory.readPadded_zero_size (Data.Bytes.natToBytesPadded value.toNat 32)
  rw [hr]
  exact Memory.bytesToBigEndianNat_natToBytesPadded _ _ (by exact value.val.isLt)

/-- The table read, with NO bound on either slot: the write eighteen bytes below keeps only the
low 144 bits of slot `j`, and the read window keeps only the low 112 bits of slot `j - 1`. -/
theorem read_pair_gen (memory : ByteArray) (words : Nat → UInt256)
    (first count j : Nat) (hfirst : first < j) (hj : j < first + count) :
    (MachineState.readWord (storeDescending memory words first count) (18 * j)).toNat =
      (words j).toNat % 2 ^ 144 + (words (j - 1)).toNat % 2 ^ 112 * 2 ^ 144 := by
  rw [Bytes.readWord_toNat]
  have hp := Bytes.bytesToNatPadded_add (storeDescending memory words first count) (18 * j) 14 18
  change Precompile.bytesToNatPadded (storeDescending memory words first count) (18 * j) 32 = _
  rw [show 32 = 14 + 18 by rfl, hp]
  have hupper : Precompile.bytesToNatPadded (storeDescending memory words first count) (18 * j) 14 =
      Precompile.bytesToNatPadded (Data.Bytes.natToBytesPadded (words (j - 1)).toNat 32) 18 14 := by
    apply bytesToNatPadded_congrOffset
    intro k hk
    rw [getD_pair _ _ _ _ _ _ hfirst hj (by omega), if_pos hk]
  have hlower : Precompile.bytesToNatPadded (storeDescending memory words first count) (18 * j + 14) 18 =
      Precompile.bytesToNatPadded (Data.Bytes.natToBytesPadded (words j).toNat 32) 14 18 := by
    apply bytesToNatPadded_congrOffset
    intro k hk
    have h := getD_pair memory words first count j (14 + k) hfirst hj (by omega)
    rw [if_neg (by omega : ¬14 + k < 14)] at h
    simpa only [← Nat.add_assoc] using h
  rw [hupper, hlower]
  have hupperNat := readWord_mod_pow (Data.Bytes.natToBytesPadded (words (j - 1)).toNat 32) 0 14 (by omega)
  have hlowerNat := readWord_mod_pow (Data.Bytes.natToBytesPadded (words j).toNat 32) 0 18 (by omega)
  rw [readWord_encoded] at hupperNat hlowerNat
  norm_num only at hupperNat hlowerNat
  rw [← hupperNat, ← hlowerNat]
  norm_num only
  omega

/-- Slot 0 is written last and survives whole. -/
theorem read_zero_gen (memory : ByteArray) (words : Nat → UInt256) (count : Nat) :
    MachineState.readWord (storeDescending memory words 0 (count + 1)) 0 = words 0 := by
  change MachineState.readWord
    (PairedScheduleMemory.writeWord (storeDescending memory words 1 count) (18 * 0) (words 0)) 0 = _
  exact PairedScheduleMemory.read_writeWord _ _ _

/-- The 112-bit read window keeps the scalar whole and the junk truncated to 80 bits. -/
private theorem mod112 (s g : Nat) (hs : s < 2 ^ 32) :
    (s + g * 2 ^ 32) % 2 ^ 112 = s + g % 2 ^ 80 * 2 ^ 32 := by
  conv_lhs => rw [← Nat.div_add_mod g (2 ^ 80)]
  have hrw : s + (2 ^ 80 * (g / 2 ^ 80) + g % 2 ^ 80) * 2 ^ 32
      = s + g % 2 ^ 80 * 2 ^ 32 + g / 2 ^ 80 * 2 ^ 112 := by ring
  rw [hrw, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt g (show 0 < 2 ^ 80 by norm_num); omega)

/-- The round message word, read out of a slot-indexed table image.  `jl` is the junk of the
slot the round reads; `jr` is the junk of the slot below it, truncated to the 80 bits the read
window keeps. -/
theorem message_of_slots (memory : ByteArray) (F : Nat → UInt256) (scalar : Nat → UInt32)
    (G : Nat → Nat)
    (hF : ∀ j, j < 61 → (F j).toNat % 2 ^ 144
            = (scalar StaggerTableLayout.slots[j]!).toNat + G j * 2 ^ 32)
    (hG : ∀ j, j < 61 → G j < 2 ^ 112 - 4)
    (i : Nat) (hi : i < 77) :
    bits (StaggerCoreModel.message (storeDescending memory F 0 61) i)
      = pack (scalar Crypto.Ripemd160.r[i]!).toBitVec
          (scalar Crypto.Ripemd160.rP[i + 3]!).toBitVec
        + StaggerRound.junk (G StaggerTableLayout.pairIndices[i]!)
            (G (StaggerTableLayout.pairIndices[i]! - 1) % 2 ^ 80) := by
  obtain ⟨hpos, hlt, hleft, hright⟩ := StaggerTableLayout.layout_valid ⟨i, hi⟩
  change 1 ≤ StaggerTableLayout.pairIndices[i]! at hpos
  change StaggerTableLayout.pairIndices[i]! < 61 at hlt
  change StaggerTableLayout.slots[StaggerTableLayout.pairIndices[i]!]!
    = Crypto.Ripemd160.r[i]! at hleft
  change StaggerTableLayout.slots[StaggerTableLayout.pairIndices[i]! - 1]!
    = Crypto.Ripemd160.rP[i + 3]! at hright
  have hFp := hF StaggerTableLayout.pairIndices[i]! hlt
  have hFq := hF (StaggerTableLayout.pairIndices[i]! - 1) (by omega)
  rw [hleft] at hFp
  rw [hright] at hFq
  have hGp := hG StaggerTableLayout.pairIndices[i]! hlt
  have hs1 : (scalar Crypto.Ripemd160.r[i]!).toNat < 2 ^ 32 :=
    (scalar Crypto.Ripemd160.r[i]!).toBitVec.isLt
  have hs2 : (scalar Crypto.Ripemd160.rP[i + 3]!).toNat < 2 ^ 32 :=
    (scalar Crypto.Ripemd160.rP[i + 3]!).toBitVec.isLt
  have hq80 : G (StaggerTableLayout.pairIndices[i]! - 1) % 2 ^ 80 < 2 ^ 80 :=
    Nat.mod_lt _ (show 0 < 2 ^ 80 by norm_num)
  have hmod : (F (StaggerTableLayout.pairIndices[i]! - 1)).toNat % 2 ^ 112
      = (F (StaggerTableLayout.pairIndices[i]! - 1)).toNat % 2 ^ 144 % 2 ^ 112 :=
    (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : (112 : Nat) ≤ 144))).symm
  apply BitVec.eq_of_toNat_eq
  rw [bits_toNat, BitVec.toNat_add, pack_toNat, StaggerRound.junk, BitVec.toNat_ofNat]
  change (MachineState.readWord (storeDescending memory F 0 61)
    (18 * StaggerTableLayout.pairIndices[i]!)).toNat = _
  rw [read_pair_gen memory F 0 61 StaggerTableLayout.pairIndices[i]! (by omega) (by omega),
    hmod, hFq, hFp, mod112 _ _ hs2]
  simp only [UInt32.toNat_toBitVec] at *
  omega

/-- The scalar field of `Ready`, likewise. -/
theorem low32_of_slots (memory : ByteArray) (F : Nat → UInt256) (scalar : Nat → UInt32)
    (G : Nat → Nat)
    (hF : ∀ j, j < 61 → (F j).toNat % 2 ^ 144
            = (scalar StaggerTableLayout.slots[j]!).toNat + G j * 2 ^ 32)
    (j : Nat) (hj : j < 61) :
    Paired80Compression.low32 (MachineState.readWord
        (storeDescending memory F 0 61) (18 * j))
      = scalar StaggerTableLayout.slots[j]! := by
  have hs : (scalar StaggerTableLayout.slots[j]!).toNat < 2 ^ 32 :=
    (scalar StaggerTableLayout.slots[j]!).toBitVec.isLt
  have hFj := hF j hj
  apply UInt32.toNat_inj.mp
  change (MachineState.readWord (storeDescending memory F 0 61) (18 * j)).toNat % 2 ^ 32 = _
  by_cases hz : j = 0
  · subst hz
    have h0 : MachineState.readWord (storeDescending memory F 0 61) (18 * 0) = F 0 :=
      read_zero_gen memory F 60
    have hmm : (F 0).toNat % 2 ^ 32 = (F 0).toNat % 2 ^ 144 % 2 ^ 32 :=
      (Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : (32 : Nat) ≤ 144))).symm
    rw [h0, hmm, hFj]
    omega
  · rw [read_pair_gen memory F 0 61 j (by omega) (by omega), hFj]
    omega

#print axioms read_pair_gen
#print axioms read_zero_gen
#print axioms message_of_slots
#print axioms low32_of_slots

/-- `StaggerMessage.Ready` from a slot-indexed table and a slot-indexed junk budget.  This is
the junk-tolerant twin of `StaggerMessage.ready_junk`: word-indexed junk cannot describe this
table, because an elided slot and its pair carry the same schedule word with different junk.
`hclean` is what keeps rounds 75 and 76 exact -- the words they read are still masked, so their
slots' junk is zero rather than merely small. -/
theorem ready_slot (memory : ByteArray) (F : Nat → UInt256) (scalar : Nat → UInt32) (G : Nat → Nat)
    (hF : ∀ j, j < 61 → (F j).toNat % 2 ^ 144
            = (scalar StaggerTableLayout.slots[j]!).toNat + G j * 2 ^ 32)
    (hG : ∀ j, j < 61 → G j < 2 ^ 112 - 4)
    (hclean : ∀ j, j < 61 → ¬ StaggerAlgorithm.JDirty StaggerTableLayout.slots[j]! → G j = 0) :
    StaggerMessage.Ready (storeDescending memory F 0 61) scalar := by
  constructor
  · intro i hi
    obtain ⟨hpos, hlt, hleft, hright⟩ := StaggerTableLayout.layout_valid ⟨i, hi⟩
    change 1 ≤ StaggerTableLayout.pairIndices[i]! at hpos
    change StaggerTableLayout.pairIndices[i]! < 61 at hlt
    refine ⟨G StaggerTableLayout.pairIndices[i]!,
      G (StaggerTableLayout.pairIndices[i]! - 1) % 2 ^ 80,
      ⟨hG _ hlt, ?_, ?_⟩,
      message_of_slots memory F scalar G hF hG i hi⟩
    · intro hnd
      exact hclean _ hlt (by rw [hleft]; exact hnd)
    · intro hnd
      rw [hclean _ (by omega) (by rw [hright]; exact hnd)]
      rfl
  · intro j hj
    exact low32_of_slots memory F scalar G hF j hj

#print axioms ready_slot

/-! ## The two byte invariants the NEXT block's pool depends on -/

/-- Bytes 18..27 of a 32-byte encoding are bits 32..111, so they vanish whenever the value is
clean below bit 144 -- which slots 0, 4 and 6 (schedule words 6, 4 and 5) always are. -/
private theorem div_pow_mod_zero (v d : Nat) (hd0 : 32 ≤ d) (hd1 : d + 8 ≤ 144)
    (hv : v % 2 ^ 144 < 2 ^ 32) : v / 2 ^ d % 256 = 0 := by
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hr : v % 2 ^ 144 < 2 ^ d :=
    lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hd0)
  have hmul : (2:Nat) ^ (144 - d) * 2 ^ d = 2 ^ 144 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hsplit : v = v % 2 ^ 144 + v / 2 ^ 144 * 2 ^ (144 - d) * 2 ^ d := by
    calc v = v % 2 ^ 144 + v / 2 ^ 144 * 2 ^ 144 := by omega
      _ = v % 2 ^ 144 + v / 2 ^ 144 * 2 ^ (144 - d) * 2 ^ d := by rw [Nat.mul_assoc, hmul]
  rw [hsplit, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hr, Nat.zero_add]
  have h8 : (2:Nat) ^ (144 - d) = 2 ^ (136 - d) * 256 := by
    rw [show (256:Nat) = 2 ^ 8 by norm_num, ← Nat.pow_add]; congr 1; omega
  rw [h8, ← Nat.mul_assoc]
  exact Nat.mul_mod_left _ _

private theorem encoded_mid_zero (value : UInt256) (hv : value.toNat % 2 ^ 144 < 2 ^ 32)
    (i : Nat) (hi0 : 18 ≤ i) (hi1 : i < 28) :
    (Data.Bytes.natToBytesPadded value.toNat 32)[i]?.getD 0 = 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega),
    show (256:Nat) ^ (32 - 1 - i) = 2 ^ (8 * (32 - 1 - i)) by
      rw [show (256:Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul],
    div_pow_mod_zero _ _ (by omega) (by omega) hv]
  rfl

/-- **The six-byte invariant survives a table write.**  Byte `18*j + k` with `k < 14` is byte
`18 + k` of slot `j - 1`, so the six come from slots 0, 4 and 6 at encoding offsets 26, 27, 22,
23, 20 and 21 -- all inside bits 32..111, all zero for a word the artifact still masks. -/
theorem storeDescending_poolClear (memory : ByteArray) (F : Nat → UInt256)
    (h0 : (F 0).toNat % 2 ^ 144 < 2 ^ 32)
    (h4 : (F 4).toNat % 2 ^ 144 < 2 ^ 32)
    (h6 : (F 6).toNat % 2 ^ 144 < 2 ^ 32) :
    PairStoreGap.PoolClear (storeDescending memory F 0 61) := by
  have key : ∀ (j k : Nat), 0 < j → j < 61 → k < 14 →
      (storeDescending memory F 0 61)[18 * j + k]?.getD 0
        = (Data.Bytes.natToBytesPadded (F (j - 1)).toNat 32)[18 + k]?.getD 0 := by
    intro j k hj0 hj1 hk
    rw [getD_pair _ _ _ _ _ _ hj0 (by omega) (by omega), if_pos hk]
  refine ⟨?_, ?_, ?_⟩
  · exact JD8Pool.window2_of_bytes _ 26
      (by rw [show (26:Nat) = 18 * 1 + 8 from rfl, key 1 8 (by omega) (by omega) (by omega)]
          exact encoded_mid_zero _ h0 _ (by omega) (by omega))
      (by rw [show (26:Nat) + 1 = 18 * 1 + 9 from rfl, key 1 9 (by omega) (by omega) (by omega)]
          exact encoded_mid_zero _ h0 _ (by omega) (by omega))
  · exact JD8Pool.window2_of_bytes _ 94
      (by rw [show (94:Nat) = 18 * 5 + 4 from rfl, key 5 4 (by omega) (by omega) (by omega)]
          exact encoded_mid_zero _ h4 _ (by omega) (by omega))
      (by rw [show (94:Nat) + 1 = 18 * 5 + 5 from rfl, key 5 5 (by omega) (by omega) (by omega)]
          exact encoded_mid_zero _ h4 _ (by omega) (by omega))
  · exact JD8Pool.window2_of_bytes _ 128
      (by rw [show (128:Nat) = 18 * 7 + 2 from rfl, key 7 2 (by omega) (by omega) (by omega)]
          exact encoded_mid_zero _ h6 _ (by omega) (by omega))
      (by rw [show (128:Nat) + 1 = 18 * 7 + 3 from rfl, key 7 3 (by omega) (by omega) (by omega)]
          exact encoded_mid_zero _ h6 _ (by omega) (by omega))

theorem resultMemoryJ_poolClear (memory : ByteArray) (words : Nat → UInt256)
    (h0 : (Pair13Memory.tableJ words 0).toNat % 2 ^ 144 < 2 ^ 32)
    (h4 : (Pair13Memory.tableJ words 4).toNat % 2 ^ 144 < 2 ^ 32)
    (h6 : (Pair13Memory.tableJ words 6).toNat % 2 ^ 144 < 2 ^ 32) :
    PairStoreGap.PoolClear (Pair13Memory.resultMemoryJ memory words) :=
  storeDescending_poolClear memory _ h0 h4 h6

/-- The elided slots hold `hi144` of something, hence below `2 ^ 112`, hence their top four
gap bytes are zero -- `GapClear` for the J image needs no hypothesis at all. -/
theorem resultMemoryJ_gapClear (memory : ByteArray) (words : Nat → UInt256) :
    PairStoreGap.GapClear (Pair13Memory.resultMemoryJ memory words) := by
  intro j hj k hk0 hk1
  have hb := PairStoreGap.lowerPairSlots_bounds j hj
  change (storeDescending memory (Pair13Memory.tableJ words) 0 61)[18 * j + k]?.getD 0 = 0
  rw [getD_pair _ _ _ _ _ _ (by omega) (by omega) (by omega), if_neg (by omega)]
  refine PairStoreGap.encoded_prefix_zero _ ?_ k hk1
  rw [Pair13Memory.tableJ, if_pos hj]
  exact JD8Merge.hi144_lt _

theorem read_resultMemoryJ_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    MachineState.readWord (Pair13Memory.resultMemoryJ memory words) address
      = MachineState.readWord memory address :=
  read_table_outside _ _ _ ha

#print axioms storeDescending_poolClear
#print axioms resultMemoryJ_gapClear

end Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Table

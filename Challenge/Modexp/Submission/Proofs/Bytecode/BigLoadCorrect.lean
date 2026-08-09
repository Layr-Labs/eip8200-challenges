import Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad
import Challenge.Modexp.Submission.Proofs.Bytecode.LoadMath
import Challenge.Modexp.Submission.Proofs.Limbs
import Mathlib.Data.Nat.Bitwise
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Functional correctness of big-endian operand loading

The execution model in `BigLoad` is deliberately instruction-shaped.  This
module connects its word arithmetic and memory writes to the mathematical
little-endian limb representation consumed by the big MODEXP path.

The loader now walks the destination one 256-bit limb at a time, so the
induction below is over limbs and the invariant is
`Represents (loadMemory … k memory) dst n (V % radix ^ k)`: after `k` writes
the destination holds exactly the low `k` limbs of the input.  Every `OR` the
loader performs is against a limb that is still zero, so no bit-level
disjointness argument is needed -- only `0 ||| v = v`.

The per-byte index arithmetic (`loadLimb`, `loadShift`, `loadReverse` and
their word forms) is kept verbatim: it belongs to the *serializer*, which
still walks byte by byte, and `BigSerializeCorrect` consumes it.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigLoadCorrect

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

/-! ## Per-byte index arithmetic (consumed by `BigSerializeCorrect`) -/

theorem loadReverseWord_ofNat (length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i < length) :
    BigLoad.loadReverseWord (UInt256.ofNat length) i =
      UInt256.ofNat (BigLoad.loadReverse length i) := by
  unfold BigLoad.loadReverseWord BigLoad.loadReverse
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) hlength]
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]

theorem loadLimbWord_ofNat (length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i < length) :
    BigLoad.loadLimbWord (UInt256.ofNat length) i =
      UInt256.ofNat (BigLoad.loadLimb length i) := by
  unfold BigLoad.loadLimbWord BigLoad.loadLimb
  rw [loadReverseWord_ofNat length i hlength hi]
  have hreverse : BigLoad.loadReverse length i < 2 ^ 256 := by
    unfold BigLoad.loadReverse
    omega
  rw [Challenge.EvmProof.Word.shiftRight_ofNat hreverse (by omega)]
  congr 1
  rw [Nat.shiftRight_eq_div_pow]

theorem loadShiftWord_ofNat (length i : Nat) (hlength : length < 2 ^ 256)
    (hi : i < length) :
    BigLoad.loadShiftWord (UInt256.ofNat length) i =
      UInt256.ofNat (BigLoad.loadShift length i) := by
  unfold BigLoad.loadShiftWord BigLoad.loadShift
  rw [loadReverseWord_ofNat length i hlength hi]
  have hand : UInt256.land
      (UInt256.ofNat (BigLoad.loadReverse length i)) (UInt256.ofNat 31) =
      UInt256.ofNat (BigLoad.loadReverse length i % 32) := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_land,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    have hreverse : BigLoad.loadReverse length i < 2 ^ 256 := by
      unfold BigLoad.loadReverse
      omega
    rw [Nat.mod_eq_of_lt hreverse]
    norm_num
    have hmod : BigLoad.loadReverse length i % 32 < 2 ^ 256 :=
      (Nat.mod_lt _ (by omega)).trans (by norm_num)
    change BigLoad.loadReverse length i &&& 31 =
      BigLoad.loadReverse length i % 32 % 2 ^ 256
    rw [Nat.mod_eq_of_lt hmod]
    exact Nat.and_two_pow_sub_one_eq_mod (BigLoad.loadReverse length i) 5
  rw [hand]
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by
    have hmod : BigLoad.loadReverse length i % 32 < 32 := Nat.mod_lt _ (by omega)
    norm_num
    omega)]
  congr 1
  rw [show 2 ^ 3 = 8 by norm_num]
  omega

theorem loadAt_ofNat (dst length i : Nat)
    (hlength : length < 2 ^ 256) (hi : i < length)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256) :
    (BigLoad.loadAt (UInt256.ofNat dst) length i).toNat =
      dst + 32 * BigLoad.loadLimb length i := by
  unfold BigLoad.loadAt
  rw [loadLimbWord_ofNat length i hlength hi]
  have hlimb : BigLoad.loadLimb length i < Limbs.limbCount length := by
    unfold BigLoad.loadLimb BigLoad.loadReverse Limbs.limbCount
    omega
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by
    norm_num
    omega)]
  rw [show 2 ^ 5 = 32 by norm_num]
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : dst < 2 ^ 256),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : BigLoad.loadLimb length i * 32 < 2 ^ 256)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
/-! ## Limb lists -/

private theorem ofDigits_set_add (radix : Nat) (digits : List Nat)
    (index delta : Nat) (hindex : index < digits.length) :
    Nat.ofDigits radix (digits.set index (digits[index] + delta)) =
      Nat.ofDigits radix digits + delta * radix ^ index := by
  induction digits generalizing index with
  | nil => simp at hindex
  | cons head tail ih =>
      cases index with
      | zero =>
          change Nat.ofDigits radix ((head + delta) :: tail) = _
          simp only [Nat.ofDigits_cons, Nat.pow_zero, Nat.mul_one]
          omega
      | succ index =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hindex
          simp only [List.set_cons_succ, List.getElem_cons_succ,
            Nat.ofDigits_cons]
          rw [ih index hindex, Nat.pow_succ]
          ring

private theorem getElem_eq_div_mod_ofDigits (radix : Nat) (digits : List Nat)
    (index : Nat) (hradix : 0 < radix) (hindex : index < digits.length)
    (hdigits : ∀ digit ∈ digits, digit < radix) :
    digits[index] = Nat.ofDigits radix digits / radix ^ index % radix := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index hradix digits hdigits]
  rw [List.drop_eq_getElem_cons hindex]
  simp only [Nat.ofDigits_cons]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hdigits digits[index]
    (List.getElem_mem hindex))]

theorem memoryLimbs_write_at (memory : ByteArray) (ptr count index : Nat)
    (value : UInt256) (_hindex : index < count) :
    Limbs.memoryLimbs
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) (ptr + 32 * index))
        ptr count =
      (Limbs.memoryLimbs memory ptr count).set index value.toNat := by
  apply List.ext_get
  · simp [Limbs.memoryLimbs]
  · intro j hjLeft hjRight
    have hj : j < count := by simpa [Limbs.memoryLimbs] using hjLeft
    rw [List.get_eq_getElem, List.get_eq_getElem]
    rw [List.getElem_set hjRight]
    split
    · next heq =>
      subst j
      simp only [Limbs.memoryLimbs, List.getElem_map, List.getElem_range]
      rw [Challenge.EvmProof.Memory.readWord_writeWord]
    · next hne =>
      simp only [Limbs.memoryLimbs, List.getElem_map, List.getElem_range]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      rcases Nat.lt_or_gt_of_ne (Ne.symm hne) with hbefore | hafter
      · left
        omega
      · right
        simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        omega

theorem value_memoryLimbs_write_add (memory : ByteArray)
    (ptr count index delta : Nat) (hindex : index < count)
    (hfit : (MachineState.readWord memory (ptr + 32 * index)).toNat + delta <
      2 ^ 256) :
    Nat.ofDigits Limbs.radix
        (Limbs.memoryLimbs
          (MachineState.writeBytes memory
            (Data.Bytes.natToBytesPadded
              ((MachineState.readWord memory (ptr + 32 * index)).toNat + delta)
              32)
            (ptr + 32 * index)) ptr count) =
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory ptr count) +
        delta * Limbs.radix ^ index := by
  let value := UInt256.ofNat
    ((MachineState.readWord memory (ptr + 32 * index)).toNat + delta)
  have hvalue : value.toNat =
      (MachineState.readWord memory (ptr + 32 * index)).toNat + delta := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  rw [← hvalue]
  change Nat.ofDigits Limbs.radix
      (Limbs.memoryLimbs
        (MachineState.writeBytes memory
          (Data.Bytes.natToBytesPadded value.toNat 32) (ptr + 32 * index))
        ptr count) = _
  rw [memoryLimbs_write_at memory ptr count index value hindex, hvalue]
  have hidxlen : index < (Limbs.memoryLimbs memory ptr count).length := by
    simpa using hindex
  have hget : (Limbs.memoryLimbs memory ptr count)[index]'hidxlen =
      (MachineState.readWord memory (ptr + 32 * index)).toNat := by
    simp [Limbs.memoryLimbs]
  rw [← hget]
  exact ofDigits_set_add Limbs.radix (Limbs.memoryLimbs memory ptr count)
    index delta (by simpa using hindex)
/-! ## Byte extraction (retained) -/

theorem loadByte_toNat (calldata : ByteArray) (offset i : Nat) :
    (BigLoad.loadByte calldata offset i).toNat =
      (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat := by
  unfold BigLoad.loadByte
  rw [Challenge.EvmProof.Bytes.byteAt_zero_readWord]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact (YulSemantics.EVM.byteFrom calldata.toList
    (offset + i)).toNat_lt.trans (by norm_num)

theorem shiftedLoadByte_toNat (calldata : ByteArray) (offset length i : Nat)
    (hlength : length < 2 ^ 256) (hi : i < length) :
    (UInt256.shiftLeft (BigLoad.loadByte calldata offset i)
      (BigLoad.loadShiftWord (UInt256.ofNat length) i)).toNat =
      (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat *
        256 ^ (BigLoad.loadReverse length i % 32) := by
  let byte := (YulSemantics.EVM.byteFrom calldata.toList (offset + i)).toNat
  have hbyte : byte < 256 := (YulSemantics.EVM.byteFrom calldata.toList
    (offset + i)).toNat_lt
  have hrem : BigLoad.loadReverse length i % 32 < 32 :=
    Nat.mod_lt _ (by omega)
  have hshift : BigLoad.loadShift length i < 256 := by
    unfold BigLoad.loadShift
    omega
  have hresult : byte * 2 ^ BigLoad.loadShift length i < 2 ^ 256 := by
    unfold BigLoad.loadShift
    have hbytePow : byte < 2 ^ 8 := by norm_num; exact hbyte
    calc
      byte * 2 ^ (8 * (BigLoad.loadReverse length i % 32)) <
          2 ^ 8 * 2 ^ (8 * (BigLoad.loadReverse length i % 32)) :=
        Nat.mul_lt_mul_of_pos_right hbytePow (Nat.pow_pos (by omega))
      _ = 2 ^ (8 + 8 * (BigLoad.loadReverse length i % 32)) := by
        rw [← Nat.pow_add]
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [loadShiftWord_ofNat length i hlength hi]
  rw [show BigLoad.loadByte calldata offset i = UInt256.ofNat byte by
    apply Challenge.EvmProof.Word.word_ext
    rw [loadByte_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (hbyte.trans (by norm_num))]
    ]
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat
    (hbyte.trans (by norm_num)) hshift hresult]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hresult]
  unfold BigLoad.loadShift
  rw [show 2 ^ (8 * (BigLoad.loadReverse length i % 32)) =
      256 ^ (BigLoad.loadReverse length i % 32) by
    calc
      2 ^ (8 * (BigLoad.loadReverse length i % 32)) =
          (2 ^ 8) ^ (BigLoad.loadReverse length i % 32) :=
        Nat.pow_mul 2 8 _
      _ = 256 ^ (BigLoad.loadReverse length i % 32) := by norm_num]
/-! ## The limb the loader writes

Three bridges from `BigLoad`'s 256-bit word model to `Nat` limb arithmetic,
then one induction. -/

private theorem mod_mul_split (V m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    V % (m * n) = V % m + m * (V / m % n) := by
  have hrem : V % m < m := Nat.mod_lt _ hm
  have hdigit : V / m % n < n := Nat.mod_lt _ hn
  have hlt : m * (V / m % n) + V % m < m * n := by
    have hbound : m * (V / m % n) + m ≤ m * n := by
      calc m * (V / m % n) + m = m * (V / m % n + 1) := by ring
        _ ≤ m * n := Nat.mul_le_mul_left m (by omega)
    omega
  conv_lhs => rw [← Nat.div_add_mod V m]
  rw [Nat.add_mod, Nat.mul_mod_mul_left,
    Nat.mod_eq_of_lt (by omega : V % m < m * n), Nat.mod_eq_of_lt hlt]
  omega

theorem readLimb_of_represents {memory : ByteArray} {ptr count value index : Nat}
    (hrep : Limbs.Represents memory ptr count value) (hindex : index < count) :
    (MachineState.readWord memory (ptr + 32 * index)).toNat =
      value / Limbs.radix ^ index % Limbs.radix := by
  have hget := getElem_eq_div_mod_ofDigits Limbs.radix
    (Limbs.memoryLimbs memory ptr count) index Limbs.radix_pos
    (by simpa using hindex)
    (fun digit hdigit => Limbs.memoryLimb_lt memory ptr count hdigit)
  rw [Limbs.value_of_represents hrep] at hget
  simpa [Limbs.memoryLimbs] using hget

/-- Under the destination-fit hypothesis the address range does not wrap, so
the loop performs exactly `len / 32` full-limb iterations.  This is where the
wrapped branch of `loadRuns` is retired for every real caller. -/
theorem loadRuns_eq (dst length : Nat) (hlength : length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256) :
    BigLoad.loadRuns (UInt256.ofNat dst) (UInt256.ofNat length) = length / 32 := by
  have hdst : dst < 2 ^ 256 := by omega
  have hdstW : (UInt256.ofNat dst).toNat = dst := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hdst]
  have hlenW : (UInt256.ofNat length).toNat = length := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlength]
  have hlimb : 32 * (length / 32) ≤ 32 * Limbs.limbCount length := by
    unfold Limbs.limbCount; omega
  unfold BigLoad.loadRuns BigLoad.fullLimbs
  rw [hdstW, hlenW, if_pos (by omega)]

theorem loadCount_eq (dst length : Nat) (hlength : length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256) :
    BigLoad.loadCount (UInt256.ofNat dst) (UInt256.ofNat length) =
      Limbs.limbCount length := by
  have hlenW : (UInt256.ofNat length).toNat = length := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlength]
  unfold BigLoad.loadCount
  rw [loadRuns_eq dst length hlength hfit, hlenW]
  unfold Limbs.limbCount
  split <;> omega

theorem loadPtr_eq (dst length k : Nat)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hk : k ≤ Limbs.limbCount length) :
    (BigLoad.loadPtr (UInt256.ofNat dst) k).toNat = dst + 32 * k := by
  have hdst : dst < 2 ^ 256 := by omega
  rw [BigLoad.loadPtr_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hdst, Nat.mod_eq_of_lt (by omega)]

/-- A full limb is one 32-byte calldata window. -/
theorem loadWindow_toNat (calldata : ByteArray) (offset length k : Nat)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hk : 32 * (k + 1) ≤ length) :
    (BigLoad.loadWindow calldata (UInt256.ofNat offset)
      (UInt256.ofNat length) k).toNat =
      Precompile.bytesToNatPadded calldata offset length /
        Limbs.radix ^ k % Limbs.radix := by
  have hoffW : (UInt256.ofNat offset).toNat = offset := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoffset]
  have hlenW : (UInt256.ofNat length).toNat = length := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlength]
  unfold BigLoad.loadWindow
  rw [hoffW, hlenW, Challenge.EvmProof.Bytes.readWord_toNat, Limbs.radix]
  exact (LoadMath.limb_eq_window calldata offset length k hk).symm

/-- The single partial top limb is the leading `len % 32` bytes. -/
theorem loadPartialValue_toNat (calldata : ByteArray) (offset length : Nat)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hr : length % 32 ≠ 0) :
    (BigLoad.loadPartialValue calldata (UInt256.ofNat offset)
      (UInt256.ofNat length)).toNat =
      Precompile.bytesToNatPadded calldata offset length /
        Limbs.radix ^ (length / 32) % Limbs.radix := by
  have hoffW : (UInt256.ofNat offset).toNat = offset := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoffset]
  have hlenW : (UInt256.ofNat length).toNat = length := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlength]
  have hprefix : Precompile.bytesToNatPadded calldata offset (length % 32) <
      2 ^ 256 := by
    have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow calldata offset
      (length % 32)
    have hmono : (256 : Nat) ^ (length % 32) ≤ 256 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h256 : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
    omega
  have htop := LoadMath.top_limb_lt calldata offset length hr
  unfold BigLoad.loadPartialValue
  rw [hoffW, hlenW,
    Challenge.EvmProof.Bytes.shiftRight_readWord calldata offset (length % 32)
      (by omega) (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hprefix,
    Limbs.radix, Nat.mod_eq_of_lt htop]
  exact (LoadMath.top_limb_eq_prefix calldata offset length).symm

/-- The word the loader ORs into destination limb `k`. -/
theorem loadLimbValue_toNat (calldata : ByteArray) (offset dst length k : Nat)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hk : k < Limbs.limbCount length) :
    (BigLoad.loadLimbValue calldata (UInt256.ofNat offset)
      (UInt256.ofNat length) (UInt256.ofNat dst) k).toNat =
      Precompile.bytesToNatPadded calldata offset length /
        Limbs.radix ^ k % Limbs.radix := by
  have hruns := loadRuns_eq dst length hlength hfit
  have hlimb : Limbs.limbCount length = (length + 31) / 32 := rfl
  by_cases hfull : k < length / 32
  · rw [BigLoad.loadLimbValue_of_lt _ _ _ _ _ (by omega)]
    exact loadWindow_toNat calldata offset length k hoffset hlength (by omega)
  · have hr : length % 32 ≠ 0 := by
      rw [hlimb] at hk; omega
    have hkeq : k = length / 32 := by
      rw [hlimb] at hk; omega
    rw [BigLoad.loadLimbValue_of_ge _ _ _ _ _ (by omega), hkeq]
    exact loadPartialValue_toNat calldata offset length hoffset hlength hr

/-! ## The limb induction -/

theorem loadMemory_represents_prefix (calldata memory : ByteArray)
    (offset dst length k : Nat)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hzero : Limbs.Represents memory dst (Limbs.limbCount length) 0)
    (hk : k ≤ Limbs.limbCount length) :
    Limbs.Represents
      (BigLoad.loadMemory calldata (UInt256.ofNat offset) (UInt256.ofNat length)
        (UInt256.ofNat dst) k memory)
      dst (Limbs.limbCount length)
      (Precompile.bytesToNatPadded calldata offset length %
        Limbs.radix ^ k) := by
  have hcount := loadCount_eq dst length hlength hfit
  induction k with
  | zero => simpa [BigLoad.loadMemory, Nat.pow_zero, Nat.mod_one] using hzero
  | succ k ih =>
      have hkk : k < Limbs.limbCount length := by omega
      have hbefore := ih (by omega)
      have hpowPos : 0 < Limbs.radix ^ k := Nat.pow_pos Limbs.radix_pos
      have hVk : Precompile.bytesToNatPadded calldata offset length %
          Limbs.radix ^ k < Limbs.radix ^ k := Nat.mod_lt _ hpowPos
      have hguard : k < BigLoad.loadCount (UInt256.ofNat dst)
          (UInt256.ofNat length) := by rw [hcount]; exact hkk
      have hptr := loadPtr_eq dst length k hfit (by omega)
      have hdelta := loadLimbValue_toNat calldata offset dst length k hoffset
        hlength hfit hkk
      have hread : (MachineState.readWord
          (BigLoad.loadMemory calldata (UInt256.ofNat offset)
            (UInt256.ofNat length) (UInt256.ofNat dst) k memory)
          (dst + 32 * k)).toNat = 0 := by
        rw [readLimb_of_represents hbefore hkk, Nat.div_eq_of_lt hVk,
          Nat.zero_mod]
      have hdeltaLt : Precompile.bytesToNatPadded calldata offset length /
          Limbs.radix ^ k % Limbs.radix < 2 ^ 256 := by
        have := Nat.mod_lt (Precompile.bytesToNatPadded calldata offset length /
          Limbs.radix ^ k) Limbs.radix_pos
        rw [Limbs.radix] at this
        exact this
      have hlor : (UInt256.lor
          (MachineState.readWord
            (BigLoad.loadMemory calldata (UInt256.ofNat offset)
              (UInt256.ofNat length) (UInt256.ofNat dst) k memory)
            (dst + 32 * k))
          (BigLoad.loadLimbValue calldata (UInt256.ofNat offset)
            (UInt256.ofNat length) (UInt256.ofNat dst) k)).toNat =
          (MachineState.readWord
            (BigLoad.loadMemory calldata (UInt256.ofNat offset)
              (UInt256.ofNat length) (UInt256.ofNat dst) k memory)
            (dst + 32 * k)).toNat +
            Precompile.bytesToNatPadded calldata offset length /
              Limbs.radix ^ k % Limbs.radix := by
        rw [Challenge.EvmProof.Word.word_toNat_lor, hread, hdelta,
          Nat.zero_or, Nat.zero_add]
      have hwrite := value_memoryLimbs_write_add
        (BigLoad.loadMemory calldata (UInt256.ofNat offset)
          (UInt256.ofNat length) (UInt256.ofNat dst) k memory)
        dst (Limbs.limbCount length) k
        (Precompile.bytesToNatPadded calldata offset length /
          Limbs.radix ^ k % Limbs.radix) hkk (by rw [hread]; omega)
      rw [Limbs.value_of_represents hbefore] at hwrite
      have hfinalLt : Precompile.bytesToNatPadded calldata offset length %
          Limbs.radix ^ (k + 1) < Limbs.radix ^ Limbs.limbCount length := by
        have h1 : Precompile.bytesToNatPadded calldata offset length %
            Limbs.radix ^ (k + 1) < Limbs.radix ^ (k + 1) :=
          Nat.mod_lt _ (Nat.pow_pos Limbs.radix_pos)
        have h2 : Limbs.radix ^ (k + 1) ≤ Limbs.radix ^ Limbs.limbCount length :=
          Nat.pow_le_pow_right Limbs.radix_pos (by omega)
        omega
      apply (Limbs.represents_iff_value hfinalLt).2
      rw [BigLoad.loadMemory_succ _ _ _ _ _ _ hguard, hptr, hlor, hwrite,
        Nat.pow_succ, mod_mul_split _ _ _ hpowPos Limbs.radix_pos]
      ring

theorem loadReturned_represents (s : State) (offset dst length : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hoffset : offset < 2 ^ 256) (hlength : length < 2 ^ 256)
    (hfit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hzero : Limbs.Represents s.memory dst (Limbs.limbCount length) 0) :
    Limbs.Represents
      (BigLoad.loadReturned s (UInt256.ofNat offset) (UInt256.ofNat length)
        (UInt256.ofNat dst) returnDest rest).memory
      dst (Limbs.limbCount length)
        (Precompile.bytesToNatPadded s.executionEnv.calldata offset length) := by
  have hcount := loadCount_eq dst length hlength hfit
  have hmain := loadMemory_represents_prefix s.executionEnv.calldata s.memory
    offset dst length (Limbs.limbCount length) hoffset hlength hfit hzero
    (Nat.le_refl _)
  rw [Nat.mod_eq_of_lt (Limbs.byteValue_fits_limbs s.executionEnv.calldata
    offset length)] at hmain
  rw [BigLoad.loadReturned_eq]
  simpa [BigLoad.loadLoop, hcount] using hmain

end Challenge.Modexp.Submission.Proofs.Bytecode.BigLoadCorrect

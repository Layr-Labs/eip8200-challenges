import Challenge.EvmProof.Memory
import Challenge.Modexp.Submission.Proofs.Limbs

set_option warningAsError true

/-!
# `MCOPY` memory lemmas

The EVM step function models `MCOPY dst src size` as replacing memory by

```
MachineState.writeBytes mem (MachineState.readPadded mem src size) dst
```

i.e. the *whole* source block is read from the original `mem` first, and only
then written at `dst`.  Consequently the transfer lemmas below hold with **no
disjointness hypothesis** relating the source and destination windows.

The file provides

* `readPadded_writeBytes_inside` / `readWord_writeBytes_inside` — reading
  strictly inside a `writeBytes` window sees only the written bytes;
* `readPadded_readPadded_inside` — a sub-read of a zero-padded read;
* `readWord_mcopy_inside` — the key word-transfer lemma for `MCOPY`;
* `readWord_mcopy_disjoint` — the frame lemma for regions untouched by the copy;
* `represents_mcopy` / `represents_mcopy_disjoint_region` — the
  `Limbs.Represents` corollaries the direct-bytecode proofs consume.
-/

namespace Challenge.Modexp.Submission.Proofs.Mcopy

open EvmSemantics
open Challenge.EvmProof

/-! ## Reading inside a `writeBytes` window -/

/-- A zero-padded read that lies entirely inside the window written by
`writeBytes` sees exactly the written bytes, independently of the underlying
array. -/
theorem readPadded_writeBytes_inside (bs bytes : ByteArray) (start k n : Nat)
    (hk : k + n ≤ bytes.size) :
    MachineState.readPadded (MachineState.writeBytes bs bytes start) (start + k) n
      = MachineState.readPadded bytes k n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    have e1 := Memory.readPadded_getElem?_getD
      (MachineState.writeBytes bs bytes start) (start + k) n i
    have e2 := Memory.readPadded_getElem?_getD bytes k n i
    have e3 := MachineState.writeBytes_getElem?_getD bs bytes start (start + k + i)
    rw [← Memory.getD0_eq_getElem _ _ h1, ← Memory.getD0_eq_getElem _ _ h2,
      e1, e2, if_pos hi, if_pos hi, e3,
      if_pos (show start ≤ start + k + i ∧ start + k + i < start + bytes.size by
        omega),
      show start + k + i - start = k + i from by omega]

/-- Word version of `readPadded_writeBytes_inside`: a word read at offset `k`
inside the window written by `writeBytes` is the word at offset `k` of the
written byte array itself. -/
theorem readWord_writeBytes_inside (bs bytes : ByteArray) (start k : Nat)
    (hk : k + 32 ≤ bytes.size) :
    MachineState.readWord (MachineState.writeBytes bs bytes start) (start + k)
      = MachineState.readWord bytes k := by
  unfold MachineState.readWord
  rw [readPadded_writeBytes_inside bs bytes start k 32 hk]

/-- A zero-padded read that stays in range is just `ByteArray.extract`. -/
theorem readPadded_eq_extract (bs : ByteArray) (start n : Nat)
    (h : start + n ≤ bs.size) :
    MachineState.readPadded bs start n = bs.extract start (start + n) := by
  apply ByteArray.ext_getElem
  · rw [Memory.readPadded_size, ByteArray.size_extract, Nat.min_eq_left h]
    omega
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    rw [← Memory.getD0_eq_getElem _ _ h1, Memory.readPadded_getElem?_getD,
      if_pos hi, ByteArray.getElem_extract,
      Memory.getD0_eq_getElem bs (start + i) (by omega)]

/-- `readWord_writeBytes_inside`, phrased with the big-endian value of the
extracted 32-byte slice. -/
theorem readWord_writeBytes_inside_extract (bs bytes : ByteArray) (start k : Nat)
    (hk : k + 32 ≤ bytes.size) :
    MachineState.readWord (MachineState.writeBytes bs bytes start) (start + k)
      = UInt256.ofNat
          (Data.Bytes.bytesToBigEndianNat (bytes.extract k (k + 32))) := by
  rw [readWord_writeBytes_inside bs bytes start k hk]
  show UInt256.ofNat
    (Data.Bytes.bytesToBigEndianNat (MachineState.readPadded bytes k 32)) = _
  rw [readPadded_eq_extract bytes k 32 hk]

/-! ## Sub-reads of a zero-padded read -/

/-- A window that lies inside an already-materialised zero-padded read is the
corresponding window of the original array. -/
theorem readPadded_readPadded_inside (mem : ByteArray) (src size k n : Nat)
    (hk : k + n ≤ size) :
    MachineState.readPadded (MachineState.readPadded mem src size) k n
      = MachineState.readPadded mem (src + k) n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    have e1 := Memory.readPadded_getElem?_getD
      (MachineState.readPadded mem src size) k n i
    have e2 := Memory.readPadded_getElem?_getD mem (src + k) n i
    have e3 := Memory.readPadded_getElem?_getD mem src size (k + i)
    rw [← Memory.getD0_eq_getElem _ _ h1, ← Memory.getD0_eq_getElem _ _ h2,
      e1, e2, if_pos hi, if_pos hi, e3, if_pos (show k + i < size by omega),
      show src + (k + i) = src + k + i from by omega]

/-! ## The `MCOPY` transfer and frame lemmas -/

/-- **Key `MCOPY` lemma.**  Every 32-byte word that lies entirely inside the
copied block reads at the destination exactly what it read at the source in the
*pre-copy* memory.  No disjointness of `[src, src+size)` and `[dst, dst+size)`
is required, because the EVM evaluates `readPadded mem src size` against the
original memory. -/
theorem readWord_mcopy_inside (mem : ByteArray) (dst src size k : Nat)
    (hk : k + 32 ≤ size) :
    MachineState.readWord
        (MachineState.writeBytes mem (MachineState.readPadded mem src size) dst)
        (dst + k)
      = MachineState.readWord mem (src + k) := by
  have hsize : (MachineState.readPadded mem src size).size = size :=
    Memory.readPadded_size mem src size
  rw [readWord_writeBytes_inside mem (MachineState.readPadded mem src size) dst k
    (by rw [hsize]; exact hk)]
  show UInt256.ofNat (Data.Bytes.bytesToBigEndianNat
      (MachineState.readPadded (MachineState.readPadded mem src size) k 32)) = _
  rw [readPadded_readPadded_inside mem src size k 32 hk]
  rfl

/-- **Frame lemma for `MCOPY`.**  A word read from a region disjoint from the
destination window is unchanged by the copy. -/
theorem readWord_mcopy_disjoint (mem : ByteArray) (dst src size ptr : Nat)
    (hdisjoint : ptr + 32 ≤ dst ∨ dst + size ≤ ptr) :
    MachineState.readWord
        (MachineState.writeBytes mem (MachineState.readPadded mem src size) dst)
        ptr
      = MachineState.readWord mem ptr := by
  refine Memory.readWord_writeBytes_disjoint mem _ ptr dst ?_
  rw [Memory.readPadded_size]
  exact hdisjoint

/-! ## Limb-level corollaries -/

/-- The limbs of the copied block at the destination are the limbs of the
source block in the pre-copy memory. -/
theorem memoryLimbs_mcopy (mem : ByteArray) (dst src count : Nat) :
    Limbs.memoryLimbs
        (MachineState.writeBytes mem
          (MachineState.readPadded mem src (32 * count)) dst)
        dst count
      = Limbs.memoryLimbs mem src count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro i hi
  have hi' : i < count := by simpa using hi
  rw [readWord_mcopy_inside mem dst src (32 * count) (32 * i) (by omega)]

/-- `MCOPY` of `32 * count` bytes from `src` to `dst` carries a `count`-limb
representation from `src` to `dst`. -/
theorem represents_mcopy (mem : ByteArray) (dst src count value : Nat)
    (hsrc : Limbs.Represents mem src count value) :
    Limbs.Represents
      (MachineState.writeBytes mem (MachineState.readPadded mem src (32 * count))
        dst)
      dst count value := by
  refine ⟨hsrc.1, ?_⟩
  rw [memoryLimbs_mcopy mem dst src count]
  exact hsrc.2

/-- `MCOPY` preserves every limb region disjoint from its destination window. -/
theorem represents_mcopy_disjoint_region (mem : ByteArray)
    (dst src count ptr pcount value : Nat)
    (hdisjoint : ptr + 32 * pcount ≤ dst ∨ dst + 32 * count ≤ ptr)
    (hrep : Limbs.Represents mem ptr pcount value) :
    Limbs.Represents
      (MachineState.writeBytes mem (MachineState.readPadded mem src (32 * count))
        dst)
      ptr pcount value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro i hi
  have hi' : i < pcount := by simpa using hi
  rw [readWord_mcopy_disjoint mem dst src (32 * count) (ptr + 32 * i)
    (by rcases hdisjoint with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))]


end Challenge.Modexp.Submission.Proofs.Mcopy

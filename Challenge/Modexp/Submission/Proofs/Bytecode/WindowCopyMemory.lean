import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowCopyMemory

open EvmSemantics EvmSemantics.EVM

/-!
# Exponent copies above the window table (MX)

The trampoline at the end of the code stores `e >>> 7` at 544 and `e >>> 3` at 576 on every loop
iteration.  An unaligned `MLOAD` at `514 + k` (resp. `546 + k`) then has the copy's
bytes `k, k + 1` as its two low bytes, so `AND 480` of it is the lookup address the
original `DUPn PUSH1 s SHR` computed from the exponent on the stack.  Only the low two
bytes of each read matter: the table below 512 and the other copy may occupy the rest
of the window.
-/

/-- The two exponent copies the MX trampoline stores above the 16-word table. -/
def copyMem (mem : ByteArray) (e : UInt256) : ByteArray :=
  WindowTableMemory.storeWord
    (WindowTableMemory.storeWord mem 544 (UInt256.shiftRight e (UInt256.ofNat 7)))
    576 (UInt256.shiftRight e (UInt256.ofNat 3))

theorem readWord_copyMem_low (mem : ByteArray) (e : UInt256) (a : Nat) (ha : a + 32 ≤ 544) :
    MachineState.readWord (copyMem mem e) a = MachineState.readWord mem a := by
  unfold copyMem WindowTableMemory.storeWord
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega)),
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by omega))]

theorem natToBE_getD (n w i : Nat) (hi : i < w) :
    ((YulEvmCompiler.natToBE n w)[i]?.getD 0).toNat = n / 256 ^ (w - 1 - i) % 256 := by
  induction w generalizing n with
  | zero => omega
  | succ w ih =>
    rw [YulEvmCompiler.natToBE]
    by_cases h : i < w
    · rw [List.getElem?_append_left (by simp; omega), ih (n / 256) h, Nat.div_div_eq_div_mul,
        ← Nat.pow_succ']
      congr 3
      omega
    · have hiw : i = w := by omega
      subst hiw
      rw [List.getElem?_append_right (by simp)]
      simp

theorem mk_getD (l : List UInt8) (i : Nat) :
    (ByteArray.mk l.toArray)[i]?.getD 0 = l[i]?.getD 0 := by
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem!]
  by_cases h : i < l.length
  · rw [getElem!_pos (ByteArray.mk l.toArray) i
        (by change i < l.toArray.size; rw [List.size_toArray]; exact h),
      List.getElem?_eq_getElem h, Option.getD_some]
    rfl
  · rw [getElem!_neg (ByteArray.mk l.toArray) i
        (by change ¬ i < l.toArray.size; rw [List.size_toArray]; exact h),
      List.getElem?_eq_none (by omega)]
    rfl

theorem storeWord_getD (mem : ByteArray) (off : Nat) (v : UInt256) (j : Nat)
    (hj : j < 32) :
    ((WindowTableMemory.storeWord mem off v)[off + j]?.getD 0).toNat =
      v.toNat / 256 ^ (31 - j) % 256 := by
  unfold WindowTableMemory.storeWord
  rw [MachineState.writeBytes_getElem?_getD,
    if_pos (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega),
    Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE,
    show off + j - off = j by omega, mk_getD, natToBE_getD v.toNat 32 j hj,
    show 32 - 1 - j = 31 - j by omega]

theorem storeWord_getD_other (mem : ByteArray) (off : Nat) (v : UInt256) (a : Nat)
    (h : a < off ∨ off + 32 ≤ a) :
    (WindowTableMemory.storeWord mem off v)[a]?.getD 0 = mem[a]?.getD 0 := by
  unfold WindowTableMemory.storeWord
  rw [MachineState.writeBytes_getElem?_getD,
    if_neg (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]

theorem foldl_mod65536 (L : List UInt8) (h : L.length = 32) :
    L.foldl (fun acc b => acc * 256 + b.toNat) 0 % 65536 =
      (L[30]?.getD 0).toNat * 256 + (L[31]?.getD 0).toNat := by
  have hsplit := List.take_append_drop 30 L
  have hlen : (L.drop 30).length = 2 := by simp [h]
  match hd : L.drop 30, hlen with
  | [x, y], _ =>
    have h30 : L[30]? = some x := by
      rw [show (30 : Nat) = 30 + 0 from rfl, ← List.getElem?_drop, hd]; rfl
    have h31 : L[31]? = some y := by
      rw [show (31 : Nat) = 30 + 1 from rfl, ← List.getElem?_drop, hd]; rfl
    rw [h30, h31, ← hsplit, hd, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Option.getD_some]
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    omega

theorem readWord_mod65536 (bs : ByteArray) (a : Nat) :
    (MachineState.readWord bs a).toNat % 65536 =
      (bs[a + 30]?.getD 0).toNat * 256 + (bs[a + 31]?.getD 0).toNat := by
  unfold MachineState.readWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_mod_of_dvd _ (by decide : (65536 : Nat) ∣ 2 ^ 256)]
  unfold Data.Bytes.bytesToBigEndianNat
  rw [Challenge.EvmProof.Bytecode.toList_eq_data]
  have hsize := Challenge.EvmProof.Memory.readPadded_size bs a 32
  rw [foldl_mod65536 _ (by simp)]
  have h30 := Challenge.EvmProof.Memory.readPadded_getElem?_getD bs a 32 30
  have h31 := Challenge.EvmProof.Memory.readPadded_getElem?_getD bs a 32 31
  rw [if_pos (by decide)] at h30 h31
  rw [← h30, ← h31, Array.getElem?_toList, Array.getElem?_toList]
  rfl

private theorem land480_mod (x : Nat) : 480 &&& x = 480 &&& (x % 65536) := by
  rw [show (65536 : Nat) = 2 ^ 16 by decide, ← Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_comm x, ← Nat.and_assoc, show (480 &&& (2 ^ 16 - 1) : Nat) = 480 by decide]

/-- Low two bytes of the unaligned read of copy `v` stored at `off`, from `off - 30 + k`. -/
private theorem window_low (bs : ByteArray) (off k : Nat) (v : UInt256) (hk : k ≤ 30)
    (hb30 : ((bs[off + k]?.getD 0).toNat) = v.toNat / 256 ^ (31 - k) % 256)
    (hb31 : ((bs[off + k + 1]?.getD 0).toNat) = v.toNat / 256 ^ (30 - k) % 256)
    (hoff : 30 ≤ off) :
    (MachineState.readWord bs (off - 30 + k)).toNat % 65536 = v.toNat / 256 ^ (30 - k) % 65536 := by
  rw [readWord_mod65536, show off - 30 + k + 30 = off + k by omega,
    show off - 30 + k + 31 = off + k + 1 by omega, hb30, hb31]
  have hp : 256 ^ (31 - k) = 256 ^ (30 - k) * 256 := by
    rw [show 31 - k = (30 - k) + 1 by omega, Nat.pow_succ]
  rw [hp, ← Nat.div_div_eq_div_mul]
  omega

theorem land480_copyA (mem : ByteArray) (e : UInt256) (k : Nat) (hk : k ≤ 10) :
    UInt256.land (UInt256.ofNat 480) (MachineState.readWord (copyMem mem e) (514 + k)) =
      UInt256.land (UInt256.ofNat 480) (UInt256.shiftRight e (UInt256.ofNat (247 - 8 * k))) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
    show (UInt256.ofNat 480).toNat = 480 from rfl,
    land480_mod (MachineState.readWord _ _).toNat, land480_mod (e.toNat >>> _)]
  congr 1
  have hw := window_low (copyMem mem e) 544 k (UInt256.shiftRight e (UInt256.ofNat 7)) (by omega)
    (by
      unfold copyMem
      rw [storeWord_getD_other _ _ _ _ (Or.inl (by omega)), storeWord_getD _ _ _ _ (by omega)])
    (by
      unfold copyMem
      rw [storeWord_getD_other _ _ _ _ (Or.inl (by omega)), Nat.add_assoc,
        storeWord_getD _ _ _ _ (by omega), show 31 - (k + 1) = 30 - k by omega])
    (by omega)
  rw [show 544 - 30 + k = 514 + k by omega] at hw
  have hp : (2 : Nat) ^ 7 * 256 ^ (30 - k) = 2 ^ (247 - 8 * k) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  rw [hw, Challenge.EvmProof.Word.shiftRight_toNat _ (by omega), Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, hp]

theorem land480_copyB (mem : ByteArray) (e : UInt256) (k : Nat) (hk : k ≤ 10) :
    UInt256.land (UInt256.ofNat 480) (MachineState.readWord (copyMem mem e) (546 + k)) =
      UInt256.land (UInt256.ofNat 480) (UInt256.shiftRight e (UInt256.ofNat (243 - 8 * k))) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ (by omega),
    show (UInt256.ofNat 480).toNat = 480 from rfl,
    land480_mod (MachineState.readWord _ _).toNat, land480_mod (e.toNat >>> _)]
  congr 1
  have hw := window_low (copyMem mem e) 576 k (UInt256.shiftRight e (UInt256.ofNat 3)) (by omega)
    (by
      unfold copyMem
      rw [storeWord_getD _ _ _ _ (by omega)])
    (by
      unfold copyMem
      rw [Nat.add_assoc, storeWord_getD _ _ _ _ (by omega), show 31 - (k + 1) = 30 - k by omega])
    (by omega)
  rw [show 576 - 30 + k = 546 + k by omega] at hw
  have hp : (2 : Nat) ^ 3 * 256 ^ (30 - k) = 2 ^ (243 - 8 * k) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  rw [hw, Challenge.EvmProof.Word.shiftRight_toNat _ (by omega), Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, hp]

theorem activeWordsAfter_nineteen (a : Nat) (ha : a + 32 ≤ 608) :
    MachineState.activeWordsAfter 19 a 32 = 19 := by
  simp [MachineState.activeWordsAfter]
  omega

/-- Word addresses of the twenty-one lookups: even digits read copy A, odd digits copy B. -/
def laddr (i : Nat) : Nat := if i % 2 = 0 then 514 + i / 2 else 546 + i / 2

theorem land480_laddr (mem : ByteArray) (e : UInt256) (i : Nat) (hi : i < 21) :
    UInt256.land (UInt256.ofNat 480) (MachineState.readWord (copyMem mem e) (laddr i)) =
      UInt256.land (UInt256.ofNat 480) (UInt256.shiftRight e (UInt256.ofNat (247 - 4 * i))) := by
  unfold laddr
  by_cases h : i % 2 = 0
  · rw [if_pos h, land480_copyA mem e (i / 2) (by omega),
      show 247 - 8 * (i / 2) = 247 - 4 * i by omega]
  · rw [if_neg h, land480_copyB mem e (i / 2) (by omega),
      show 243 - 8 * (i / 2) = 247 - 4 * i by omega]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowCopyMemory

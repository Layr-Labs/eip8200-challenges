import Challenge.Modexp.Submission.Proofs.Memo.Logic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Window coverage for unaligned calldata checks

A guard may compare 32-byte calldata windows at arbitrary offsets.  The operand
bytes the specification decodes are determined once every byte of the operand
range lies inside some checked window, and a header word bounded by 1024 (as
`ValidInput` guarantees) is determined by its low two bytes alone.
-/

namespace Challenge.Modexp.Submission.Proofs.Memo.Cover

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Memo.Logic

theorem byte_eq_of_window (input target : ByteArray) (o p : Nat) (hp : o ≤ p) (hp32 : p < o + 32)
    (h : MachineState.readWord input o = MachineState.readWord target o) :
    YulSemantics.EVM.byteFrom input.toList p = YulSemantics.EVM.byteFrom target.toList p := by
  have hlt : p - o < 32 := by omega
  have h1 := Challenge.EvmProof.Bytes.byteAt_readWord input o (p - o) hlt
  have h2 := Challenge.EvmProof.Bytes.byteAt_readWord target o (p - o) hlt
  rw [h] at h1
  rw [show o + (p - o) = p by omega] at h1 h2
  have h3 := congrArg UInt256.toNat (h1.symm.trans h2)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by norm_num))] at h3
  exact UInt8.toNat.inj h3

/-- Every check constant is the target's word at that offset. -/
def checksOk (target : ByteArray) (checks : List (Nat × UInt256)) : Bool :=
  checks.all fun c => decide (c.2 = MachineState.readWord target c.1)

/-- Every byte of `[off, off + len)` lies in the 32-byte window of some check. -/
def coversArith (checks : List (Nat × UInt256)) (off len : Nat) : Bool :=
  (List.range len).all fun i =>
    checks.any fun c => decide (c.1 ≤ off + i) && decide (off + i < c.1 + 32)

theorem window_of_cover {target : ByteArray} {checks : List (Nat × UInt256)} {off len : Nat}
    (hok : checksOk target checks = true) (hc : coversArith checks off len = true) :
    ∀ p, off ≤ p → p < off + len →
      ∃ o, (o, MachineState.readWord target o) ∈ checks ∧ o ≤ p ∧ p < o + 32 := by
  intro p hp1 hp2
  unfold coversArith at hc
  rw [List.all_eq_true] at hc
  have hi := hc (p - off) (List.mem_range.2 (by omega))
  rw [List.any_eq_true] at hi
  obtain ⟨c, hcmem, hcb⟩ := hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcb
  obtain ⟨h1, h2⟩ := hcb
  unfold checksOk at hok
  rw [List.all_eq_true] at hok
  have h3 := hok c hcmem
  rw [decide_eq_true_eq] at h3
  refine ⟨c.1, ?_, by omega, by omega⟩
  rw [← h3]
  exact hcmem

theorem bytesToNatPadded_eq_of_cover (input target : ByteArray)
    (checks : List (Nat × UInt256)) (off len : Nat)
    (hm : WordsMatch checks input) (hok : checksOk target checks = true)
    (hc : coversArith checks off len = true) :
    Precompile.bytesToNatPadded input off len =
      Precompile.bytesToNatPadded target off len := by
  have hcov := window_of_cover hok hc
  clear hc
  induction len with
  | zero => simp
  | succ n ih =>
      rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      rw [ih (fun p h1 h2 => hcov p h1 (by omega))]
      obtain ⟨o, hmem, ho1, ho2⟩ := hcov (off + n) (by omega) (by omega)
      rw [byte_eq_of_window input target o (off + n) ho1 ho2
        (hm (o, MachineState.readWord target o) hmem)]

/-- A header word bounded by 1024 is determined by its low two bytes. -/
theorem header_of_low (input target : ByteArray) (off : Nat)
    (hi : Precompile.bytesToNatPadded input off 32 ≤ 1024)
    (ht : Precompile.bytesToNatPadded target off 32 ≤ 1024)
    (hlow : Precompile.bytesToNatPadded input (off + 30) 2 =
      Precompile.bytesToNatPadded target (off + 30) 2) :
    Precompile.bytesToNatPadded input off 32 = Precompile.bytesToNatPadded target off 32 := by
  have h1 : Precompile.bytesToNatPadded input off 32 =
      Precompile.bytesToNatPadded input off 30 * 65536 +
        Precompile.bytesToNatPadded input (off + 30) 2 :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_add input off 30 2
  have h2 : Precompile.bytesToNatPadded target off 32 =
      Precompile.bytesToNatPadded target off 30 * 65536 +
        Precompile.bytesToNatPadded target (off + 30) 2 :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_add target off 30 2
  omega

theorem isTrue_of_ne_zero (a : UInt256) (h : a ≠ 0) : UInt256.isTrue a := by
  show a.toNat ≠ 0
  intro hz
  apply h
  apply Challenge.EvmProof.Word.word_ext
  rw [hz]
  rfl

end Challenge.Modexp.Submission.Proofs.Memo.Cover

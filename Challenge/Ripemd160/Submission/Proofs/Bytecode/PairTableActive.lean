import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableMemory
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableActive
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open DenseScheduleTemplate PairedScheduleContract

theorem word_active_mono (current : UInt256) (address : Nat)
    (hbound : address + 32 < 2 ^ 256) :
    current.toNat ≤ (UInt256.ofNat
      (MachineState.activeWordsAfter current.toNat address 32)).toNat := by
  have hb : MachineState.activeWordsAfter current.toNat address 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    exact ⟨current.val.isLt, by omega⟩
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hb]
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  exact Nat.le_max_left _ _

theorem loaded_active_mono (s : State) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) :
    s.activeWords.toNat ≤ (loadedActiveWords s (UInt256.ofNat p)).toNat := by
  have hp : (UInt256.ofNat p).toNat = p := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 := word_active_mono s.activeWords p (by omega)
  have h1 := word_active_mono (activeAfterWord s.activeWords (UInt256.ofNat p))
    (p + 32) (by omega)
  unfold loadedActiveWords activeAfterWord
  rw [pointer_add32_toNat p hbound, hp]
  simp only [activeAfterWord, hp] at h1
  exact h0.trans h1

theorem loaded_active_eq_of_allocated (s : State) (p : Nat)
    (hbound : p + 64 < 2 ^ 256) (halign : p % 32 = 0)
    (hallocated : (p + 64) / 32 ≤ s.activeWords.toNat) :
    loadedActiveWords s (UInt256.ofNat p) = s.activeWords := by
  have hp : (UInt256.ofNat p).toNat = p := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha (address : Nat) (haddress : address = p ∨ address = p + 32) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := by
    have hm : MachineState.activeWordsAfter s.activeWords.toNat address 32 =
        s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      rcases haddress with rfl | rfl <;> omega
    rw [hm]
    exact (Word.word_eq_ofNat_toNat _).symm
  unfold loadedActiveWords activeAfterWord
  rw [hp, pointer_add32_toNat p hbound, ha p (Or.inl rfl), ha (p + 32) (Or.inr rfl)]

/-- Loading the complete relocated input block covers all table and hash accesses. -/
theorem loaded_active_ge34 (s : State) (p : Nat)
    (hp : 1024 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    34 ≤ (loadedActiveWords s (UInt256.ofNat p)).toNat := by
  have hcur := (activeAfterWord s.activeWords (UInt256.ofNat p)).val.isLt
  have hnew : MachineState.activeWordsAfter
      (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat (p + 32) 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    constructor
    · exact hcur
    · omega
  change 34 ≤ (UInt256.ofNat (MachineState.activeWordsAfter
    (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat
    (UInt256.ofNat p + UInt256.ofNat 32).toNat 32)).toNat
  rw [pointer_add32_toNat p hbound, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hnew]
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  omega

/-- All static word reads/writes through byte1087 preserve the active-word mark. -/
theorem word_active_preserved (current : UInt256) (address : Nat)
    (hc : 34 ≤ current.toNat) (ha : address ≤ 1056) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have h : MachineState.activeWordsAfter current.toNat address 32 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

theorem zero_active_preserved (current : UInt256) (hc : 34 ≤ current.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat 0 802) = current := by
  have h : MachineState.activeWordsAfter current.toNat 0 802 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (802 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

#print axioms loaded_active_ge34
#print axioms word_active_preserved
#print axioms zero_active_preserved
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableActive

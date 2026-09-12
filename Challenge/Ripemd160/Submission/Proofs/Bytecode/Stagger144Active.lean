import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableActive
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open DenseScheduleTemplate PairedScheduleContract
theorem loaded_active_ge38 (s : State) (p : Nat)
    (hp : 1152 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    38 ≤ (loadedActiveWords s (UInt256.ofNat p)).toNat := by
  have hcur := (activeAfterWord s.activeWords (UInt256.ofNat p)).val.isLt
  have hnew : MachineState.activeWordsAfter
      (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat (p + 32) 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    constructor
    · exact hcur
    · omega
  change 38 ≤ (UInt256.ofNat (MachineState.activeWordsAfter
    (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat
    (UInt256.ofNat p + UInt256.ofNat 32).toNat 32)).toNat
  rw [pointer_add32_toNat p hbound, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hnew]
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  omega

theorem word_active_preserved (current : UInt256) (address : Nat)
    (hc : 35 ≤ current.toNat) (ha : address ≤ 1088) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have h : MachineState.activeWordsAfter current.toNat address 32 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm


#print axioms loaded_active_ge38
#print axioms word_active_preserved
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active

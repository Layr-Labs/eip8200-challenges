import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Memory
import EvmSemantics.EVM.State
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Active
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof


def activeAfterWord (current : UInt256) (offset : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter current.toNat offset.toNat 32)

def loadedActiveWords (s : State) (messageOffset : UInt256) : UInt256 :=
  let a0 := activeAfterWord s.activeWords messageOffset
  activeAfterWord a0 (messageOffset + UInt256.ofNat 32)

theorem pointer_add32_toNat (p : Nat) (hbound : p + 64 < 2 ^ 256) :
    (UInt256.ofNat p + UInt256.ofNat 32).toNat = p + 32 := by
  rw [Word.ofNat_add_ofNat (by omega), Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- Loading the complete relocated input block covers all table and hash accesses. -/
theorem loaded_active_ge53 (s : State) (p : Nat)
    (hp : 1632 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    53 ≤ (loadedActiveWords s (UInt256.ofNat p)).toNat := by
  have hcur := (activeAfterWord s.activeWords (UInt256.ofNat p)).val.isLt
  have hnew : MachineState.activeWordsAfter
      (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat (p + 32) 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    constructor
    · exact hcur
    · omega
  change 53 ≤ (UInt256.ofNat (MachineState.activeWordsAfter
    (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat
    (UInt256.ofNat p + UInt256.ofNat 32).toNat 32)).toNat
  rw [pointer_add32_toNat p hbound, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hnew]
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  omega

/-- All static word reads/writes through byte1695 preserve the active-word mark. -/
theorem word_active_preserved (current : UInt256) (address : Nat)
    (hc : 53 ≤ current.toNat) (ha : address ≤ 1664) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have h : MachineState.activeWordsAfter current.toNat address 32 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

theorem zero_active_preserved (current : UInt256) (hc : 53 ≤ current.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat 0 1418) = current := by
  have h : MachineState.activeWordsAfter current.toNat 0 1418 = current.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (1418 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

#print axioms loaded_active_ge53
#print axioms word_active_preserved
#print axioms zero_active_preserved
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Active

import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

def normalHead (n : Nat) : Nat := if n = 4 then 10683 else 2667
def zeroHead (n : Nat) : Nat := if n = 4 then 3760 else 3588
def head (n : Nat) (k : UInt256) : Nat := if k.toNat = 0 then zeroHead n else normalHead n

def packed (n : Nat) (k : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight
      (UInt256.ofNat ((3932*65536)+18699) - UInt256.ofNat ((43*65536)+2004)*UInt256.ofNat n)
      (UInt256.ofNat 16 * UInt256.isZero k))
    (UInt256.ofNat 65535)

theorem packed_eq (n : Nat) (k : UInt256) (hn : n = 4 ∨ n = 8) :
    packed n k = UInt256.ofNat (head n k) := by
  by_cases hk : k.toNat = 0
  · have hz : UInt256.isZero k = UInt256.ofNat 1 := by
      apply Challenge.EvmProof.Word.word_ext
      rw [Challenge.EvmProof.Word.word_toNat_isZero]
      simp [hk]
    rcases hn with rfl | rfl <;> simp only [packed, head, if_pos hk, hz] <;> decide
  · have hz : UInt256.isZero k = UInt256.ofNat 0 := by
      apply Challenge.EvmProof.Word.word_ext
      rw [Challenge.EvmProof.Word.word_toNat_isZero]
      simp [hk]
    rcases hn with rfl | rfl <;> simp only [packed, head, if_neg hk, hz] <;> decide

theorem zero_complement (mem : ByteArray) (hpre : Shift.PreOK mem)
    (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hk : MachineState.readWord mem 1536 = UInt256.ofNat 0) :
    MachineState.readWord mem 1600 = UInt256.ofNat 256 := by
  obtain ⟨v,hv,hL,rest⟩ := Shift.pre_facts (MachineState.readWord mem 0) hd
  have hk' : Shift.preK (MachineState.readWord mem 0) = UInt256.ofNat 0 := by
    rw [← hpre.1]
    exact hk
  have hv0 : v = 0 := by
    have hnat := congrArg UInt256.toNat hk'
    rw [Shift.preK_toNat _ v hv hL] at hnat
    exact hnat
  apply Challenge.EvmProof.Word.word_ext
  have hs := hpre.2.2.1
  change MachineState.readWord mem 1600 = _ at hs
  rw [hs, Shift.preS_toNat _ v hv hL, hv0]
  decide

#print axioms packed_eq
#print axioms zero_complement
end CycleSubmission.Global.ZeroShiftMath

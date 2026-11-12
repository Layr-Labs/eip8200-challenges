import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
open EvmSemantics
namespace CycleSubmission.Global.ZeroRemainderMath
theorem residual (d inv lo rho : UInt256) (h : d * inv = UInt256.ofNat 1) :
 lo - d * (inv * (lo - rho)) = rho := by
  have hv : d.val * inv.val = (1 : Fin UInt256.size) := congrArg UInt256.val h
  apply Challenge.EvmProof.Word.word_ext
  change (lo.val - d.val * (inv.val * (lo.val - rho.val))).val = rho.val.val
  rw [← mul_assoc, hv, one_mul, sub_sub_cancel]
#print axioms residual

open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift
theorem divisor_and_inverse (mem : ByteArray) (hpre : PreOK mem)
    (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hk : MachineState.readWord mem 1536 = UInt256.ofNat 0) :
    MachineState.readWord mem 1568 = MachineState.readWord mem 0 ∧
    MachineState.readWord mem 0 * MachineState.readWord mem 1664 = UInt256.ofNat 1 := by
  obtain ⟨v,hv,hL,hmul,hodd,rest⟩ := pre_facts (MachineState.readWord mem 0) hd
  have hk' : preK (MachineState.readWord mem 0) = UInt256.ofNat 0 := hpre.1.symm.trans hk
  have hv0 : v = 0 := by
    have hnat := congrArg UInt256.toNat hk'
    rw [preK_toNat _ v hv hL] at hnat
    exact hnat
  have heq : preDodd (MachineState.readWord mem 0) = MachineState.readWord mem 0 := by
    apply Challenge.EvmProof.Word.word_ext
    simpa [hv0] using hmul
  constructor
  · exact hpre.2.1.trans heq
  · have hi := preDinv_inv (MachineState.readWord mem 0) hodd
    have hp : preDodd (MachineState.readWord mem 0) * preDinv (MachineState.readWord mem 0) = UInt256.ofNat 1 := by
      apply Challenge.EvmProof.Word.word_ext
      change ((preDodd (MachineState.readWord mem 0)).toNat *
        (preDinv (MachineState.readWord mem 0)).toNat) % (2^256) = 1
      exact hi
    have hinv : MachineState.readWord mem 1664 = preDinv (MachineState.readWord mem 0) := hpre.2.2.2.2
    rw [hinv]
    simpa only [heq] using hp
#print axioms divisor_and_inverse
end CycleSubmission.Global.ZeroRemainderMath

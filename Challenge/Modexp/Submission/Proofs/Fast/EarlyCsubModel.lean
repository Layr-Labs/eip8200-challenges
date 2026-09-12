import Challenge.Modexp.Submission.Proofs.Fast.CsubCore
import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubCheck

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open EarlyCsub

/-- The guarded subtraction leaves SUBB untouched when the leading limb
    already proves that the accumulator is below the modulus. -/
def csResultMemory (memory : ByteArray) (n pdst : Nat) : ByteArray :=
  if Skip memory then
    MachineState.writeBytes memory (MachineState.readPadded memory 2112 (32*n)) pdst
  else subResultMemory memory n pdst

def csReturnedState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := ret
    stack := rest
    memory := if Skip memory then
      MachineState.writeBytes memory (MachineState.readPadded memory 2112 (32*n)) pdst.toNat
    else (subReturnedState s memory n j pdst ret rest).memory }

theorem csReturnedState_memory (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) :
    (csReturnedState s memory n n pdst ret rest).memory =
      csResultMemory memory n pdst.toNat := rfl

theorem csub_correct (memory : ByteArray) (n tlow mm tn pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (ht : Model.FastRepresents memory 2112 n tlow)
    (hm : Model.FastRepresents memory 0 n mm)
    (htnv : (MachineState.readWord memory 2080).toNat = tn) (htn1 : tn ≤ 1)
    (hmpos : 0 < mm) (hbound : tn * Limbs.radix ^ n + tlow < 2 * mm) :
    Model.FastRepresents (csResultMemory memory n pdst) pdst n
      ((tn * Limbs.radix ^ n + tlow) % mm) := by
  unfold csResultMemory
  split
  · rename_i hskip
    have hs := (skip_iff memory).1 hskip
    have htlt := high_limb_lt (by omega) ht hm hs.2
    have htn0 : tn = 0 := by omega
    rw [htn0, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt htlt]
    exact fastRepresents_mcopy memory 2112 pdst n tlow (by omega) ht
  · exact csub_sub_correct memory n tlow mm tn pdst hn hn32 ht hm htnv htn1 hmpos hbound

theorem csub_preserves_region (memory : ByteArray) (n pdst ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisjSubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hdisjDst : pdst + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pdst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (csResultMemory memory n pdst) ptr cnt v := by
  unfold csResultMemory
  split
  · exact fastRepresents_mcopy_disjoint memory 2112 pdst (32*n) ptr cnt v hdisjDst hrep
  · exact csub_sub_preserves_region memory n pdst ptr cnt v hn hdisjSubb hdisjDst hrep

theorem guarded_readWord_outside (memory : ByteArray) (n pdst addr : Nat)
    (hn : 1 ≤ n) (hsubb : addr+32 ≤ 1792 ∨ 1792+32*n ≤ addr)
    (hdst : addr+32 ≤ pdst ∨ pdst+32*n ≤ addr) :
    MachineState.readWord (csResultMemory memory n pdst) addr =
      MachineState.readWord memory addr := by
  have hcopy (mem : ByteArray) (src : Nat) :
      MachineState.readWord (MachineState.writeBytes mem
        (MachineState.readPadded mem src (32*n)) pdst) addr = MachineState.readWord mem addr := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [Challenge.EvmProof.Memory.readPadded_size]
    exact hdst
  unfold csResultMemory
  split
  · exact hcopy memory 2112
  · unfold subResultMemory
    rw [hcopy]
    exact csStep_readWord_disjoint memory n addr hn hsubb n le_rfl

end Challenge.Modexp.Submission.Proofs.Fast.Csub

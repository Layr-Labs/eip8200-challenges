/- Adapted from delordemm1 submission 173ec87d-b01c-4a3b-b36a-e0a008eb4d72,
   commit b07846bed58c2c028c8c9b987eaa0e049ca5587a. -/
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.CarryResult
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel CarryScratchAgreement

def selectedRows (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  if n = 4 ∨ n = 8 then rowsCarry mem pa pb n i else rowsMem mem pa pb n i

theorem selectedRows_agree (mem : ByteArray) (pa pb n i : Nat)
    (hpa : pa+32*n ≤ 8192) (hpb : pb+32*n ≤ 8192)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i ≤ n) :
    Agree (selectedRows mem pa pb n i) (rowsMem mem pa pb n i) := by
  unfold selectedRows
  split
  · exact rows_agree mem pa pb n i hpa hpb hn hn32 hi
  · exact refl _

theorem selectedRows_readWord_outside (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 32) (hout : addr+32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (selectedRows mem pa pb n i) addr = MachineState.readWord mem addr := by
  unfold selectedRows
  split
  · exact readWord_rowsCarry mem pa pb n addr hn hout i
  · exact rowsMem_readWord_outside mem pa pb n i addr hn hout

/-- The memory a whole `MonPro(pa, pb) → pd` call leaves behind. -/
def monproMem (s : State) (mem : ByteArray) (pa pb n pdst : Nat) : ByteArray :=
  Csub.csResultMemory (selectedRows (mpZeroed s mem n) pa pb n n) n pdst

theorem monproMem_def (s : State) (mem : ByteArray) (pa pb n pdst : Nat) :
    monproMem s mem pa pb n pdst =
      Csub.csResultMemory (selectedRows (mpZeroed s mem n) pa pb n n) n pdst := rfl

/-- `gasSteps_monproFull` ends with exactly this memory. -/
theorem csReturnedState_memory_monproMem (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) :
    (Csub.csReturnedState s (selectedRows (mpZeroed s mem n) pa pb n n) n n pdst ret
      rest).memory = monproMem s mem pa pb n pdst.toNat := rfl

/-- Every word outside `SUBB`, outside the CIOS scratch `[8192, 9280)` and
outside the destination survives a `MONPRO` call. -/
theorem monproMem_readWord_outside (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 8192 ∨ 9280 ≤ addr)
    (hdst : addr + 32 ≤ pdst ∨ pdst + 32 * n ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr := by
  rw [monproMem_def,
    csResultMemory_readWord_outside _ n pdst addr hn hsubb hdst,
    selectedRows_readWord_outside _ pa pb n n addr hn32 hscratch,
    mpZeroed_readWord_outside s mem n addr (by omega)]

/-- Everything at or above `9280` survives, given only that the destination is
one of the named blocks below `T_ = 8192`. -/
theorem monproMem_readWord_high (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hdst : pdst + 32 * n ≤ 8192) (haddr : 9280 ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr :=
  monproMem_readWord_outside s mem pa pb n pdst addr hn hn32 (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega))

/-- The five configuration words `V_S32`, `V_MINV`, `V_ML`, `V_TL`, `V_EOFF`
are unchanged by a `MONPRO` call. -/
theorem monproMem_frame (s : State) (mem : ByteArray) (pa pb n pdst : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hdst : pdst + 32 * n ≤ 8192) :
    MachineState.readWord (monproMem s mem pa pb n pdst) 9344 =
        MachineState.readWord mem 9344 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9376 =
        MachineState.readWord mem 9376 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9408 =
        MachineState.readWord mem 9408 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9440 =
        MachineState.readWord mem 9440 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 9472 =
        MachineState.readWord mem 9472 :=
  ⟨monproMem_readWord_high s mem pa pb n pdst 9344 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9376 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9408 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9440 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 9472 hn hn32 hdst (by omega)⟩

/-- Every represented block disjoint from `SUBB`, from the CIOS scratch and
from the destination survives a `MONPRO` call. -/
theorem monproMem_fastRepresents_outside (s : State) (mem : ByteArray)
    (pa pb n pdst ptr cnt v : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hsubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 8192 ∨ 9280 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ pdst ∨ pdst + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (monproMem s mem pa pb n pdst) ptr cnt v := by
  refine (Model.fastRepresents_congr
    (a := mem) (b := monproMem s mem pa pb n pdst) ?_ v).1 hrep
  intro j hj
  exact (monproMem_readWord_outside s mem pa pb n pdst (ptr + 32 * j) hn hn32
    (by omega) (by omega) (by omega)).symm


theorem monproMem_represents (s : State) (mem : ByteArray) (pa pb p pdst : Nat)
    (a b mm : Nat) (hn32 : p+2 ≤ 32)
    (hpa : pa+32*(p+2) ≤ 8192) (hpb : pb+32*(p+2) ≤ 8192)
    (hpd : pdst+32*(p+2) ≤ 8192)
    (ha : Model.FastRepresents mem pa (p+2) a)
    (hb : Model.FastRepresents mem pb (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 9376).toNat + 1) % 2^256 = 0) :
    Model.FastRepresents (monproMem s mem pa pb (p+2) pdst) pdst (p+2)
      (Model.montMul mm (Limbs.radix^(p+2)) a b) := by
  have hrow := selectedRows_agree (mpZeroed s mem (p+2)) pa pb (p+2) (p+2)
    hpa hpb (by omega) hn32 (by omega)
  have htn := Monpro.monpro_tn_le_one s mem pa pb p a b mm hn32 hpa hpb ha hb hm ham (by omega) hminv
  have hres := csResult_agree _ _ hrow (p+2) pdst (by omega) hn32 htn
  have hrep := Monpro.monproMem_represents s mem pa pb p pdst a b mm hn32 hpa hpb ha hb hm hodd ham hminv
  exact (fastRepresents_iff _ _ hres pdst (p+2) _ (Or.inl hpd)).2 hrep

end Challenge.Modexp.Submission.Proofs.Fast.CarryResult

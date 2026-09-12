import Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.CarryResult
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel CarryScratchAgreement StagedOperand

def selectedRows (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  if n = 4 ∨ n = 8 then rowsCarry mem pa pb n i else rowsMem mem pa pb n i

theorem selectedRows_agree (mem : ByteArray) (pa pb n i : Nat)
    (hpa : pa+32*n ≤ 2048) (hpb : pb+32*n ≤ 2048)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hi : i ≤ n) :
    Agree (selectedRows mem pa pb n i) (rowsMem mem pa pb n i) := by
  unfold selectedRows
  split
  · exact rows_agree mem pa pb n i hpa hpb hn hn32 hi
  · exact refl _

theorem selectedRows_readWord_outside (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 8) (hout : addr+32 ≤ 2048 ∨ 2720 ≤ addr) :
    MachineState.readWord (selectedRows mem pa pb n i) addr = MachineState.readWord mem addr := by
  unfold selectedRows
  split
  · exact readWord_rowsCarry mem pa pb n addr hn hout i
  · exact rowsMem_readWord_outside mem pa pb n i addr hn hout

/-- The memory a whole `MonPro(pa, pb) → pd` call leaves behind. -/
def monproMem (s : State) (mem : ByteArray) (pa pb n pdst : Nat) : ByteArray :=
  Csub.csResultMemory (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n pdst

theorem monproMem_def (s : State) (mem : ByteArray) (pa pb n pdst : Nat) :
    monproMem s mem pa pb n pdst =
      Csub.csResultMemory (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n pdst := rfl

/-- `gasSteps_monproFull` ends with exactly this memory. -/
theorem csReturnedState_memory_monproMem (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) :
    (Csub.csReturnedState s (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n n pdst ret
      rest).memory = monproMem s mem pa pb n pdst.toNat := rfl

/-- Every word outside `SUBB`, outside the CIOS scratch `[2048, 2720)` and
outside the destination survives a `MONPRO` call. -/
theorem monproMem_readWord_outside (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr)
    (hscratch : addr + 32 ≤ 2048 ∨ 2720 ≤ addr)
    (hdst : addr + 32 ≤ pdst ∨ pdst + 32 * n ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr := by
  rw [monproMem_def,
    csResultMemory_readWord_outside _ n pdst addr hn hsubb hdst,
    selectedRows_readWord_outside _ pa pb n n addr hn32 hscratch,
    mpZeroed_readWord_outside s (inputMemory mem pa n) n addr (by omega),
    read_inputMemory_outside mem pa n addr hscratch]

/-- Everything at or above `2720` survives, given only that the destination is
one of the named blocks below `T_ = 2048`. -/
theorem monproMem_readWord_high (s : State) (mem : ByteArray)
    (pa pb n pdst addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hdst : pdst + 32 * n ≤ 2048) (haddr : 2720 ≤ addr) :
    MachineState.readWord (monproMem s mem pa pb n pdst) addr =
      MachineState.readWord mem addr :=
  monproMem_readWord_outside s mem pa pb n pdst addr hn hn32 (Or.inr (by omega))
    (Or.inr (by omega)) (Or.inr (by omega))

/-- The five configuration words `V_S32`, `V_MINV`, `V_ML`, `V_TL`, `V_EOFF`
are unchanged by a `MONPRO` call. -/
theorem monproMem_frame (s : State) (mem : ByteArray) (pa pb n pdst : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (hdst : pdst + 32 * n ≤ 2048) :
    MachineState.readWord (monproMem s mem pa pb n pdst) 2784 =
        MachineState.readWord mem 2784 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 2816 =
        MachineState.readWord mem 2816 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 2848 =
        MachineState.readWord mem 2848 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 2880 =
        MachineState.readWord mem 2880 ∧
      MachineState.readWord (monproMem s mem pa pb n pdst) 2912 =
        MachineState.readWord mem 2912 :=
  ⟨monproMem_readWord_high s mem pa pb n pdst 2784 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 2816 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 2848 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 2880 hn hn32 hdst (by omega),
   monproMem_readWord_high s mem pa pb n pdst 2912 hn hn32 hdst (by omega)⟩

/-- Every represented block disjoint from `SUBB`, from the CIOS scratch and
from the destination survives a `MONPRO` call. -/
theorem monproMem_fastRepresents_outside (s : State) (mem : ByteArray)
    (pa pb n pdst ptr cnt v : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hsubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hscratch : ptr + 32 * cnt ≤ 2048 ∨ 2720 ≤ ptr)
    (hdst : ptr + 32 * cnt ≤ pdst ∨ pdst + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (monproMem s mem pa pb n pdst) ptr cnt v := by
  refine (Model.fastRepresents_congr
    (a := mem) (b := monproMem s mem pa pb n pdst) ?_ v).1 hrep
  intro j hj
  exact (monproMem_readWord_outside s mem pa pb n pdst (ptr + 32 * j) hn hn32
    (by omega) (by omega) (by omega)).symm


theorem monproMem_represents (s : State) (mem : ByteArray) (pa pb p pdst : Nat)
    (a b mm : Nat) (hn32 : p+2 ≤ 8)
    (hpa : pa+32*(p+2) ≤ 2048) (hpb : pb+32*(p+2) ≤ 2048)
    (hpd : pdst+32*(p+2) ≤ 2048)
    (ha : Model.FastRepresents mem pa (p+2) a)
    (hb : Model.FastRepresents mem pb (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2816).toNat + 1) % 2^256 = 0) :
    Model.FastRepresents (monproMem s mem pa pb (p+2) pdst) pdst (p+2)
      (Model.montMul mm (Limbs.radix^(p+2)) a b) := by
  let prepared := inputMemory mem pa (p+2)
  have ha' : Model.FastRepresents prepared pa (p+2) a :=
    (fastRepresents_inputMemory mem pa (p+2) pa (p+2) a hpa).2 ha
  have hb' : Model.FastRepresents prepared pb (p+2) b :=
    (fastRepresents_inputMemory mem pa (p+2) pb (p+2) b hpb).2 hb
  have hm' : Model.FastRepresents prepared 0 (p+2) mm :=
    (fastRepresents_inputMemory mem pa (p+2) 0 (p+2) mm (by omega)).2 hm
  have hminv' : ((MachineState.readWord prepared (32*(p+2)-32)).toNat *
      (MachineState.readWord prepared 2816).toNat + 1) % 2^256 = 0 := by
    simpa only [prepared,
      read_inputMemory_outside mem pa (p+2) (32*(p+2)-32) (Or.inl (by omega)),
      read_inputMemory_outside mem pa (p+2) 2816 (Or.inr (by decide))] using hminv
  have hrow := selectedRows_agree (mpZeroed s prepared (p+2)) pa pb (p+2) (p+2)
    hpa hpb (by omega) hn32 (by omega)
  have htn := Monpro.monpro_tn_le_one s prepared pa pb p a b mm hn32 hpa hpb ha' hb' hm' ham (by omega) hminv'
  have hres := csResult_agree _ _ hrow (p+2) pdst (by omega) hn32 htn
  have hrep := Monpro.monproMem_represents s prepared pa pb p pdst a b mm hn32 hpa hpb ha' hb' hm' hodd ham hminv'
  exact (fastRepresents_iff _ _ hres pdst (p+2) _ (Or.inl hpd)).2 hrep

end Challenge.Modexp.Submission.Proofs.Fast.CarryResult

import Challenge.Modexp.Submission.Proofs.Fast.FullBaseLogic
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.FullBase

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

/-- Copying the bounded full-width base preserves the complete fast-path frame. -/
theorem copyBaseMem_frame {memory input : ByteArray} {n bsize minv : Nat}
    (hn32 : n ≤ 8) (hf : Exp.Frame memory n bsize minv) :
    Exp.Frame (copyBaseMem memory input n) n bsize minv := by
  have key : ∀ addr, 512 ≤ addr →
      MachineState.readWord (copyBaseMem memory input n) addr =
        MachineState.readWord memory addr :=
    fun addr haddr => copyBaseMem_readWord_high memory input n addr hn32 haddr
  exact
    ⟨by rw [key 2784 (by omega)]; exact hf.s32,
     by rw [key 2816 (by omega)]; exact hf.minvW,
     by rw [key 2848 (by omega)]; exact hf.ml,
     by rw [key 2880 (by omega)]; exact hf.tl,
     by rw [key 2912 (by omega)]; exact hf.eoff⟩

/-- Copying the full-width base and multiplying RR first converts it directly
to Montgomery form while preserving the unreduced normal-domain accumulator. -/
theorem rawThenMonpro
    {s : State} {n bsize mm minv R rr : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (memory input : ByteArray)
    (hn32 : n ≤ 8) (hmpos : 0 < mm)
    (hcop : Nat.Coprime R mm) (hrr : rr ≡ R * R [MOD mm])
    (hrrlt : rr < mm)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hr1 : Model.FastRepresents memory 1024 n (R % mm))
    (hzero : Model.FastRepresents memory 768 n 0)
    (hrrb : Model.FastRepresents memory 1536 n rr) :
    let copied := copyBaseMem memory input n
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    let converted := sub.mpMem 1536 256 512 copied
    Exp.Frame copied n bsize minv ∧
      Model.FastRepresents copied 0 n mm ∧
      Model.FastRepresents copied 256 n base ∧
      Model.FastRepresents copied 1536 n rr ∧
      Model.FastRepresents converted 512 n (base * R % mm) ∧
      Model.FastRepresents converted 0 n mm ∧
      Model.FastRepresents converted 1536 n rr ∧
      Model.FastRepresents converted 1024 n (R % mm) ∧
      Model.FastRepresents converted 768 n 0 ∧
      Exp.Frame converted n bsize minv ∧
      Model.FastRepresents converted 256 n base := by
  dsimp only
  let copied := copyBaseMem memory input n
  let base := Precompile.bytesToNatPadded input 96 (32 * n)
  let converted := sub.mpMem 1536 256 512 copied
  have hframe0 : Exp.Frame copied n bsize minv :=
    copyBaseMem_frame hn32 hframe
  have hmod0 : Model.FastRepresents copied 0 n mm :=
    copyBaseMem_modulus hn32 hmod
  have hraw0 : Model.FastRepresents copied 256 n base :=
    copyBaseMem_represents memory input n
  have hzero0 : Model.FastRepresents copied 768 n 0 :=
    copyBaseMem_preserves memory input n 768 n 0 (Or.inl (by omega)) hzero
  have hr10 : Model.FastRepresents copied 1024 n (R % mm) :=
    copyBaseMem_preserves memory input n 1024 n (R % mm) (Or.inl (by omega)) hr1
  have hrr0 : Model.FastRepresents copied 1536 n rr :=
    copyBaseMem_preserves memory input n 1536 n rr (Or.inl (by omega)) hrrb
  have hconverted : Model.FastRepresents converted 512 n (base * R % mm) := by
    have hm := spec.mpValueRaw 1536 256 512 copied rr base
      (by omega) (by omega) (by omega) hmod0 hframe0.minvW hrr0 hraw0 hrrlt
    rw [Model.montMul_comm mm R rr base,
      Model.montMul_const_form hmpos hcop hrr base] at hm
    exact hm
  have hmod1 : Model.FastRepresents converted 0 n mm :=
    spec.mpFrame 1536 256 512 0 mm copied (by omega) (Or.inr (by omega)) hmod0
  have hrr1 : Model.FastRepresents converted 1536 n rr :=
    spec.mpFrame 1536 256 512 1536 rr copied (by omega) (Or.inl (by omega)) hrr0
  have hr11 : Model.FastRepresents converted 1024 n (R % mm) :=
    spec.mpFrame 1536 256 512 1024 (R % mm) copied
      (by omega) (Or.inl (by omega)) hr10
  have hzero1 : Model.FastRepresents converted 768 n 0 :=
    spec.mpFrame 1536 256 512 768 0 copied
      (by omega) (Or.inl (by omega)) hzero0
  have hframe1 : Exp.Frame converted n bsize minv :=
    sub.mpFrame 1536 256 512 copied (by omega) hframe0
  have hraw1 : Model.FastRepresents converted 256 n base :=
    spec.mpFrame 1536 256 512 256 base copied
      (by omega) (Or.inr (by omega)) hraw0
  exact ⟨hframe0, hmod0, hraw0, hrr0, hconverted, hmod1, hrr1, hr11,
    hzero1, hframe1, hraw1⟩

end Challenge.Modexp.Submission.Proofs.Fast.FullBase

import Challenge.Modexp.Submission.Proofs.Fast.FullBaseLogic
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.FullBase

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

/-- Copying the bounded full-width base preserves the complete fast-path frame. -/
theorem copyBaseMem_frame {memory input : ByteArray} {n bsize minv : Nat}
    (hn32 : n ≤ 32) (hf : Exp.Frame memory n bsize minv) :
    Exp.Frame (copyBaseMem memory input n) n bsize minv := by
  have key : ∀ addr, 2048 ≤ addr →
      MachineState.readWord (copyBaseMem memory input n) addr =
        MachineState.readWord memory addr :=
    fun addr haddr => copyBaseMem_readWord_high memory input n addr hn32 haddr
  exact
    ⟨by rw [key 9344 (by omega)]; exact hf.s32,
     by rw [key 9376 (by omega)]; exact hf.minvW,
     by rw [key 9408 (by omega)]; exact hf.ml,
     by rw [key 9440 (by omega)]; exact hf.tl,
     by rw [key 9472 (by omega)]; exact hf.eoff⟩

/-- The shortcut copy, reduction, and Montgomery conversion meet the inherited
`bDone` value and frame boundary. -/
theorem reduceThenMonpro
    {s : State} {n bsize mm minv R rr : Nat}
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm R minv)
    (memory input : ByteArray)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm)
    (hodd : mm % 2 = 1)
    (hcop : Nat.Coprime R mm) (hrr : rr ≡ R * R [MOD mm])
    (hrrlt : rr < mm)
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hr1 : Model.FastRepresents memory 4096 n (R % mm))
    (hzero : Model.FastRepresents memory 3072 n 0)
    (hrrb : Model.FastRepresents memory 6144 n rr)
    (htop : R1.TopBitSet memory) :
    let copied := copyBaseMem memory input n
    let reduced := sub.amMem 1024 3072 1024 copied
    let converted := sub.mpMem 1024 6144 2048 reduced
    Model.FastRepresents reduced 1024 n
        (Precompile.bytesToNatPadded input 96 (32 * n) % mm) ∧
      Exp.Frame reduced n bsize minv ∧
      Model.FastRepresents reduced 0 n mm ∧
      Model.FastRepresents reduced 6144 n rr ∧
      Model.FastRepresents converted 2048 n
        (Precompile.bytesToNatPadded input 96 (32 * n) * R % mm) ∧
      Model.FastRepresents converted 0 n mm ∧
      Model.FastRepresents converted 6144 n rr ∧
      Model.FastRepresents converted 4096 n (R % mm) ∧
      Model.FastRepresents converted 3072 n 0 ∧
      Exp.Frame converted n bsize minv := by
  dsimp only
  let copied := copyBaseMem memory input n
  let base := Precompile.bytesToNatPadded input 96 (32 * n)
  let reduced := sub.amMem 1024 3072 1024 copied
  have hframe0 : Exp.Frame copied n bsize minv :=
    copyBaseMem_frame hn32 hframe
  have hmod0 : Model.FastRepresents copied 0 n mm :=
    copyBaseMem_modulus hn32 hmod
  have hbase0 : Model.FastRepresents copied 1024 n base := by
    exact copyBaseMem_represents memory input n
  have hzero0 : Model.FastRepresents copied 3072 n 0 := by
    exact copyBaseMem_preserves memory input n 3072 n 0
      (Or.inl (by omega)) hzero
  have hr10 : Model.FastRepresents copied 4096 n (R % mm) := by
    exact copyBaseMem_preserves memory input n 4096 n (R % mm)
      (Or.inl (by omega)) hr1
  have hrr0 : Model.FastRepresents copied 6144 n rr := by
    exact copyBaseMem_preserves memory input n 6144 n rr
      (Or.inl (by omega)) hrrb
  have hbaseBound : base + 0 < 2 * mm := by
    simpa [base] using
      (baseValue_lt_two_mul (memory := memory) (input := input)
        (n := n) (mm := mm) (by omega) hodd hmod htop)
  have hred : Model.FastRepresents reduced 1024 n (base % mm) := by
    exact spec.amValue 1024 3072 1024 copied base 0
      (by omega) (by omega) (by omega) hmod0 hbase0 hzero0 hbaseBound
  have hframe1 : Exp.Frame reduced n bsize minv :=
    sub.amFrame 1024 3072 1024 copied (by omega) hframe0
  have hmod1 : Model.FastRepresents reduced 0 n mm :=
    spec.amFrame 1024 3072 1024 0 mm copied (by omega)
      (Or.inr (by omega)) hmod0
  have hrr1 : Model.FastRepresents reduced 6144 n rr :=
    spec.amFrame 1024 3072 1024 6144 rr copied (by omega)
      (Or.inl (by omega)) hrr0
  have hr11 : Model.FastRepresents reduced 4096 n (R % mm) :=
    spec.amFrame 1024 3072 1024 4096 (R % mm) copied (by omega)
      (Or.inl (by omega)) hr10
  have hzero1 : Model.FastRepresents reduced 3072 n 0 :=
    spec.amFrame 1024 3072 1024 3072 0 copied (by omega)
      (Or.inl (by omega)) hzero0
  have hconverted : Model.FastRepresents
      (sub.mpMem 1024 6144 2048 reduced) 2048 n (base * R % mm) := by
    exact Exp.blMem_base spec hmpos hn32 hcop hrr hrrlt reduced
      hframe1.minvW hmod1 hred hrr1
  have hmod2 : Model.FastRepresents
      (sub.mpMem 1024 6144 2048 reduced) 0 n mm :=
    spec.mpFrame 1024 6144 2048 0 mm reduced (by omega)
      (Or.inr (by omega)) hmod1
  have hrr2 : Model.FastRepresents
      (sub.mpMem 1024 6144 2048 reduced) 6144 n rr :=
    spec.mpFrame 1024 6144 2048 6144 rr reduced (by omega)
      (Or.inl (by omega)) hrr1
  have hr12 : Model.FastRepresents
      (sub.mpMem 1024 6144 2048 reduced) 4096 n (R % mm) :=
    spec.mpFrame 1024 6144 2048 4096 (R % mm) reduced (by omega)
      (Or.inl (by omega)) hr11
  have hzero2 : Model.FastRepresents
      (sub.mpMem 1024 6144 2048 reduced) 3072 n 0 :=
    spec.mpFrame 1024 6144 2048 3072 0 reduced (by omega)
      (Or.inl (by omega)) hzero1
  have hframe2 : Exp.Frame (sub.mpMem 1024 6144 2048 reduced) n bsize minv :=
    sub.mpFrame 1024 6144 2048 reduced (by omega) hframe1
  exact ⟨hred, hframe1, hmod1, hrr1, hconverted, hmod2, hrr2, hr12, hzero2,
    hframe2⟩

end Challenge.Modexp.Submission.Proofs.Fast.FullBase

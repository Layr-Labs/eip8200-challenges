import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubTrace

set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.Csub
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-- End-to-end: entering `ADDMOD` with `a` at `pa`, `b` at `pb` and `a + b < 2m`
leaves `(a + b) mod m` in the block at `pd`. -/
theorem addmod_csub_correct (memory : ByteArray) (pa pb n a b mm pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpa : pa + 32 * n ≤ 2048) (hpb : pb + 32 * n ≤ 2048)
    (ha : Model.FastRepresents memory pa n a)
    (hb : Model.FastRepresents memory pb n b)
    (hm : Model.FastRepresents memory 0 n mm) (hmpos : 0 < mm)
    (hab : a + b < 2 * mm) :
    Model.FastRepresents (csResultMemory (amResultMemory memory pa pb n) n pdst)
      pdst n ((a + b) % mm) := by
  have hcarry := addmod_carry_le_one memory pa pb n hn (by omega) (by omega)
  have hvalue := addmod_value memory pa pb n a b hn (by omega) (by omega) ha hb
  have hts := addmod_represents memory pa pb n
  have hmblk : Model.FastRepresents (amResultMemory memory pa pb n) 0 n mm :=
    addmod_preserves_region memory pa pb n 0 n mm hn (by omega) hm
  have htn : (MachineState.readWord (amResultMemory memory pa pb n) 2080).toNat =
      (amStep memory pa pb n n).flag.toNat := by
    rw [addmod_tn]
  have hbound : (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n +
      lowValue (amStep memory pa pb n n).memory 2112 n n < 2 * mm := by
    omega
  have h := csub_correct (amResultMemory memory pa pb n) n
    (lowValue (amStep memory pa pb n n).memory 2112 n n) mm
    (amStep memory pa pb n n).flag.toNat pdst hn hn32 hts hmblk htn hcarry hmpos hbound
  rwa [show (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n +
      lowValue (amStep memory pa pb n n).memory 2112 n n = a + b from by omega] at h

/-- Region preservation across the whole `ADDMOD`/`CSUB` pair. -/
theorem addmod_csub_preserves_region (memory : ByteArray) (pa pb n pdst ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisjT : ptr + 32 * cnt ≤ 2080 ∨ 2112 + 32 * n ≤ ptr)
    (hdisjSubb : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hdisjDst : pdst + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pdst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (csResultMemory (amResultMemory memory pa pb n) n pdst)
      ptr cnt v :=
  csub_preserves_region _ n pdst ptr cnt v hn hdisjSubb hdisjDst
    (addmod_preserves_region memory pa pb n ptr cnt v hn hdisjT hrep)

end Challenge.Modexp.Submission.Proofs.Fast.Csub

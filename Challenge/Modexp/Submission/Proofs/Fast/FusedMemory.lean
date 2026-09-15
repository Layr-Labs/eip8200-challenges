import Challenge.Modexp.Submission.Proofs.Fast.R4Loop
import Challenge.Modexp.Submission.Proofs.Fast.LazyMixedProduct
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Fast.FusedMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast SquareLoopMem

def memory (s : State) (n k : Nat) (mem : ByteArray) : ByteArray :=
  StagedProduct.memory s (R4Loop.loopMem s n k mem) n

theorem mont_mul_congr_left (mm R a b c : Nat) (h : a % mm = b % mm) :
    Model.montMul mm R a c = Model.montMul mm R b c := by
  have hc : (a : ZMod mm) = (b : ZMod mm) := (ZMod.natCast_eq_natCast_iff a b mm).2 h
  unfold Model.montMul
  rw [hc]

theorem represents (s : State) (mem : ByteArray) (p a b mm k : Nat)
    (hfast : p+2 = 4 ∨ p+2 = 8) (hn : p+2 ≤ 8) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 512 (p+2) a)
    (hb : Model.FastRepresents mem 256 (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1) (_ham : a < mm) (hbm : b < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    Model.FastRepresents (memory s (p+2) k mem) 256 (p+2)
      (Model.montMul mm (Limbs.radix^(p+2))
        ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) b) := by
  obtain ⟨v, hv, _, hvm⟩ := R4Loop.loopMem_represents s mem p a mm k hfast hn hk
    ha hm hodd ha.1 (by omega) hminv
  have hb' := R4Loop.loopMem_fastRepresents_outside s mem (p+2) k 256 (p+2) b hfast (by omega) hn
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hb
  have hm' := R4Loop.loopMem_fastRepresents_outside s mem (p+2) k 0 (p+2) mm hfast (by omega) hn
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hm
  have hi' : ((MachineState.readWord (R4Loop.loopMem s (p+2) k mem) (32*(p+2)-32)).toNat *
      (MachineState.readWord (R4Loop.loopMem s (p+2) k mem) 2720).toNat + 1) % 2^256 = 0 := by
    rw [R4Loop.loopMem_readWord_outside s mem (p+2) k (32*(p+2)-32) hfast (by omega) hn
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      R4Loop.loopMem_readWord_high s mem (p+2) k 2720 hfast (by omega) hn (by omega)]
    exact hminv
  have hrep := LazyMixedProduct.represents s (R4Loop.loopMem s (p+2) k mem)
    p v b mm hn hv hb' hm' hodd hbm hi'
  have hlt : ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) < mm := by
    cases k with
    | zero => omega
    | succ j =>
        rw [Function.iterate_succ_apply']
        exact Model.montMul_lt (by omega) _ _ _
  have hvv := mont_mul_congr_left mm (Limbs.radix^(p+2)) v
    ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) b
    (hvm.trans (Nat.mod_eq_of_lt hlt).symm)
  rw [hvv] at hrep
  exact hrep

end Challenge.Modexp.Submission.Proofs.Fast.FusedMemory

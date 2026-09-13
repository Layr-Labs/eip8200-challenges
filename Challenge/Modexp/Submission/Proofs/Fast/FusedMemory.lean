import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
import Challenge.Modexp.Submission.Proofs.Fast.StagedProduct
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Fast.FusedMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast SquareLoopMem

def memory (s : State) (n k : Nat) (mem : ByteArray) : ByteArray :=
  StagedProduct.memory s (sqLoopMem s n k mem) n

theorem represents (s : State) (mem : ByteArray) (p a b mm k : Nat)
    (hfast : p+2 = 4 ∨ p+2 = 8) (hn : p+2 ≤ 8) (hk : 1 ≤ k)
    (ha : Model.FastRepresents mem 512 (p+2) a)
    (hb : Model.FastRepresents mem 256 (p+2) b)
    (hm : Model.FastRepresents mem 0 (p+2) mm) (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32*(p+2)-32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0) :
    Model.FastRepresents (memory s (p+2) k mem) 256 (p+2)
      (Model.montMul mm (Limbs.radix^(p+2))
        ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) b) := by
  have ha' := sqLoopMem_represents s mem p a mm k hfast hn hk ha hm hodd ham (by omega) hminv
  have hb' := sqLoopMem_fastRepresents_outside s mem (p+2) k 256 (p+2) b hfast (by omega) hn
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hb
  have hm' := sqLoopMem_fastRepresents_outside s mem (p+2) k 0 (p+2) mm hfast (by omega) hn
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) hm
  have hi' : ((MachineState.readWord (sqLoopMem s (p+2) k mem) (32*(p+2)-32)).toNat *
      (MachineState.readWord (sqLoopMem s (p+2) k mem) 2720).toNat + 1) % 2^256 = 0 := by
    rw [sqLoopMem_readWord_outside s mem (p+2) k (32*(p+2)-32) hfast (by omega) hn
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      sqLoopMem_readWord_high s mem (p+2) k 2720 hfast (by omega) hn (by omega)]
    exact hminv
  have halt : ((fun x => Model.montMul mm (Limbs.radix^(p+2)) x x)^[k] a) < mm := by
    cases k with
    | zero => exact ham
    | succ j =>
      rw [Function.iterate_succ_apply']
      exact Model.montMul_lt (by omega) _ _ _
  exact StagedProduct.represents s (sqLoopMem s (p+2) k mem) p _ b mm hn ha' hb' hm' hodd halt hi'

#print axioms represents
end Challenge.Modexp.Submission.Proofs.Fast.FusedMemory

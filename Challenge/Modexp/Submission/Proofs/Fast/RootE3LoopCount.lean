import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace5
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Shift
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
def gasSteps_shiftLoop_count (s : State) (mem : ByteArray) (n bsize esize msize mm minv r k : Nat)
    (hk32 : k ≤ 32)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (e : Env s) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (inv : StepInv mem n bsize mm minv)
    (hbase : Model.FastRepresents mem 512 n r) (hr : r < mm) :
    Challenge.EvmProof.GasSteps (shiftLoopState s mem n bsize esize msize k)
      (shiftLoopState s (stepMems mem n mm k) n bsize esize msize 0) :=
  Challenge.EvmProof.GasSteps.cast
    (Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun i => shiftLoopState s (stepMems mem n mm i) n bsize esize msize (k - i)) k
      (fun i hi =>
        have invI := stepInv_stepMems (by omega) hn32 inv i
        have hbaseI := stepMems_represents mem n mm r hn hn32 hmpos hmm htop inv.modulus inv.neg
          hbase hr i
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_step s (stepMems mem n mm i) n bsize esize msize (k - i) mm minv
            (by omega) (by omega) hn hn32 e invI
            (repairFacts_of (stepMems mem n mm i) n mm _ hn hn32 hmpos hmm htop invI.modulus
              invI.neg hbaseI (Nat.mod_lt _ hmpos)))
          rfl (by
            show shiftLoopState s (stepMem (stepMems mem n mm i) n mm) n bsize esize msize
              (k - i - 1) = shiftLoopState s (stepMems mem n mm (i + 1)) n bsize esize msize
              (k - (i + 1))
            rw [show k - i - 1 = k - (i + 1) from by omega]
            rfl)))
    (by simp [stepMems]) (by simp)


#print axioms gasSteps_shiftLoop_count
end Challenge.Modexp.Submission.Proofs.Fast.Shift

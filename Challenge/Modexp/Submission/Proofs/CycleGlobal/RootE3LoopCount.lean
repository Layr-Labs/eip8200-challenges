import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace5
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
/-- `k ≥ 1` shift steps from the loop head: the bottom test sends the last step to `SHIFT_DONE`. -/
def gasSteps_shiftLoop_count (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize mm minv r k : Nat)
    (hk32 : k ≤ 32) (hk1 : 1 ≤ k)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hbs : bsize = 32 * n) (e : Env s) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (inv : StepInv mem n bsize mm minv)
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (shiftLoopState z s mem n bsize esize msize k)
      (shiftDoneState z s (stepMems mem n mm k) n bsize esize msize) := by
  have loop : Challenge.EvmProof.GasSteps (shiftLoopState z s mem n bsize esize msize k)
      (shiftLoopState z s (stepMems mem n mm (k - 1)) n bsize esize msize 1) :=
    Challenge.EvmProof.GasSteps.cast
      (Challenge.EvmProof.GasSteps.iterateBounded
        (I := fun i => shiftLoopState z s (stepMems mem n mm i) n bsize esize msize (k - i)) (k - 1)
        (fun i hi =>
          have invI := stepInv_stepMems (by omega) hn32 inv i
          have hbaseI := stepMems_represents mem n mm r hn hn32 hmpos hmm htop inv.modulus inv.neg
            hbase hr inv.pre i
          Challenge.EvmProof.GasSteps.cast
            (gasSteps_step z s (stepMems mem n mm i) n bsize esize msize (k - i) mm minv
              (by omega) (by omega) hn hn32 hbs hmpos hmm htop e invI hbaseI (Nat.mod_lt _ hmpos)
              (repairFacts_of (stepMems mem n mm i) n mm _ hn hn32 hmpos hmm htop invI.modulus
                invI.neg hbaseI (Nat.mod_lt _ hmpos) invI.pre) hfast)
            rfl (by
              show shiftLoopState z s (stepMem (stepMems mem n mm i) n mm) n bsize esize msize
                (k - i - 1) = shiftLoopState z s (stepMems mem n mm (i + 1)) n bsize esize msize
                (k - (i + 1))
              rw [show k - i - 1 = k - (i + 1) from by omega]
              rfl)))
      (by simp [stepMems]) (by rw [show k - (k - 1) = 1 from by omega])
  have invL := stepInv_stepMems (by omega) hn32 inv (k - 1)
  have hbaseL := stepMems_represents mem n mm r hn hn32 hmpos hmm htop inv.modulus inv.neg
    hbase hr inv.pre (k - 1)
  have last := gasSteps_stepLast z s (stepMems mem n mm (k - 1)) n bsize esize msize mm minv
    hn hn32 hbs hmpos hmm htop e invL hbaseL (Nat.mod_lt _ hmpos)
    (repairFacts_of (stepMems mem n mm (k - 1)) n mm _ hn hn32 hmpos hmm htop invL.modulus
      invL.neg hbaseL (Nat.mod_lt _ hmpos) invL.pre) hfast
  have hlast : stepMem (stepMems mem n mm (k - 1)) n mm = stepMems mem n mm k := by
    rw [show stepMems mem n mm k = stepMems mem n mm (k - 1 + 1) from by rw [Nat.sub_add_cancel hk1]]
    rfl
  exact loop.trans (Challenge.EvmProof.GasSteps.cast last rfl (by rw [hlast]))


end CycleSubmission.Global.Fast.Shift

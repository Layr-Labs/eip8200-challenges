import Challenge.Modexp.Submission.Proofs.Fast.RootE3Memory
import Challenge.Modexp.Submission.Proofs.Fast.RootE3LoopCount
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace RootE3Trace
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Shift RootE3Phase

/-- Exact cache/prologue endpoint in v4, before the phase/count guard. -/
def guardEntry (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with
    pc := UInt256.ofNat 3012
    stack := UInt256.ofNat n :: Exp.outer n bsize esize msize
    memory := mem }

def Eligible (input : ByteArray) (n bsize esize : Nat) : Prop :=
  esize = 1 ∧ FixedExponentRoute.exponentValue input bsize 1 = 3 ∧ (n = 4 ∨ n = 8)

/-- All concrete caller obligations are fields. Neither loop trace nor a whole route is assumed.
The named Shift states follow MAIN's relocated PC definitions when instantiated in J. -/
structure TraceBindings (s : State) (mem input : ByteArray) (n bsize esize msize : Nat) where
  prologue : GasSteps (dispState s mem n bsize esize msize)
    (guardEntry s (m2Of mem input n) n bsize esize msize)
  ordinaryGuard : ¬ Eligible input n bsize esize →
    GasSteps (guardEntry s (m2Of mem input n) n bsize esize msize)
      (shiftLoopState s (flagSet (m2Of mem input n) (UInt256.ofNat 0)) n bsize esize msize n)
  e3Guard : Eligible input n bsize esize →
    GasSteps (guardEntry s (m2Of mem input n) n bsize esize msize)
      (shiftLoopState s (e3Prepared mem input n) n bsize esize msize (n / 2))
  phaseSwitch : (n = 4 ∨ n = 8) → ∀ phaseMem : ByteArray,
    MachineState.readWord phaseMem 1760 = UInt256.ofNat 1 →
    GasSteps (shiftLoopState s phaseMem n bsize esize msize 0)
      (shiftLoopState s (RootE3Phase.phaseSwitch phaseMem n) n bsize esize msize (n / 4))
  finalTail : ∀ phaseMem : ByteArray,
    MachineState.readWord phaseMem 1760 = UInt256.ofNat 0 →
    MachineState.readWord phaseMem 2688 = UInt256.ofNat (32 * n) →
    GasSteps (shiftLoopState s phaseMem n bsize esize msize 0)
      (FixedExponentRoute.entryState s (Exp.mcopyMem phaseMem 1024 1280 (32 * n))
        n bsize esize msize)

theorem phaseSwitch_flag_zero (mem : ByteArray) (n : Nat) (hn8 : n ≤ 8) :
    MachineState.readWord (RootE3Phase.phaseSwitch mem n) 1760 = UInt256.ofNat 0 := by
  unfold RootE3Phase.phaseSwitch
  rw [Exp.readWord_mcopyMem_disjoint _ 256 512 (32 * n) 1760 (Or.inr (by omega))]
  exact Challenge.EvmProof.Memory.readWord_writeWord mem 1760 (UInt256.ofNat 0)

theorem flag_after_steps_of_read (mem : ByteArray) (flag : UInt256) (n mm count : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) (hflag : MachineState.readWord mem 1760 = flag) :
    MachineState.readWord (stepMems mem n mm count) 1760 = flag := by
  rw [stepMems_readWord_disjoint mem n mm 1760 hn
    ⟨Or.inr (by omega), Or.inl (by omega), Or.inl (by omega)⟩ count]
  exact hflag

/-- Ordinary route: write flag0, execute exactly n inherited reductions, then the R1 tail. -/
def ordinaryTrace (s : State) (mem input : ByteArray) (n bsize esize msize mm minv : Nat)
    (bindings : TraceBindings s mem input n bsize esize msize)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (e : Env s)
    (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize minv) (hmod : Model.FastRepresents mem 0 n mm)
    (htop : R1.TopBitSet mem) (hmiss : ¬ Eligible input n bsize esize) :
    GasSteps (dispState s mem n bsize esize msize)
      (FixedExponentRoute.entryState s (ordinaryOutput mem input n mm) n bsize esize msize) := by
  have inv0 := m2_stepInv mem input n bsize mm minv hn hn8 hm hframe hmod
  have invPrep := flagSet_inv _ (UInt256.ofNat 0) n bsize mm minv hn8 inv0
  have hbase0 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop
  have hbasePrep := flagSet_preserves _ (UInt256.ofNat 0) 512 n _
    (Or.inl (by omega)) hbase0
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have loop := gasSteps_shiftLoop_count s (flagSet (m2Of mem input n) (UInt256.ofNat 0))
    n bsize esize msize mm minv _ n (by omega) hn hn8 e hm (Model.fastRepresents_lt hmod)
    htwo invPrep hbasePrep (Nat.mod_lt _ hm)
  have invFinal := stepInv_stepMems (by omega) hn8 invPrep n
  have hflag := flag_after_steps (m2Of mem input n) (UInt256.ofNat 0) n mm n (by omega) hn8
  exact ((bindings.prologue.trans (bindings.ordinaryGuard hmiss)).trans loop).trans
    (bindings.finalTail _ hflag invFinal.frame.s32)

/-- E3 route: exactly2k reductions, clear/copy phase change, exactlyk reductions, R1 tail. -/
def e3Trace (s : State) (mem input : ByteArray) (n bsize esize msize mm minv k : Nat)
    (bindings : TraceBindings s mem input n bsize esize msize)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hnk : n = 4 * k) (e : Env s)
    (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize minv) (hmod : Model.FastRepresents mem 0 n mm)
    (htop : R1.TopBitSet mem) (hhit : Eligible input n bsize esize) :
    GasSteps (dispState s mem n bsize esize msize)
      (FixedExponentRoute.entryState s (e3Output mem input n mm k) n bsize esize msize) := by
  have hhalf : n / 2 = 2 * k := by omega
  have hquarter : n / 4 = k := by omega
  have inv0 := m2_stepInv mem input n bsize mm minv hn hn8 hm hframe hmod
  have invPrep := flagSet_inv _ (UInt256.ofNat 1) n bsize mm minv hn8 inv0
  have hbase0 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop
  have hbasePrep := flagSet_preserves _ (UInt256.ofNat 1) 512 n _
    (Or.inl (by omega)) hbase0
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have firstLoop := gasSteps_shiftLoop_count s (e3Prepared mem input n)
    n bsize esize msize mm minv _ (2 * k) (by omega) hn hn8 e hm
    (Model.fastRepresents_lt hmod) htwo invPrep hbasePrep (Nat.mod_lt _ hm)
  have invFirst := stepInv_stepMems (by omega) hn8 invPrep (2 * k)
  have hbaseFirst := stepMems_represents (e3Prepared mem input n) n mm _ hn hn8 hm
    (Model.fastRepresents_lt hmod) htwo invPrep.modulus invPrep.neg hbasePrep
    (Nat.mod_lt _ hm) (2 * k)
  have invSwitch := phaseSwitch_inv _ n bsize mm minv hn8 invFirst
  have hbaseSwitch := phaseSwitch_preserves _ n 512 n _ (Or.inl (by omega))
    (Or.inl (by omega)) hbaseFirst
  have secondLoop := gasSteps_shiftLoop_count s
    (RootE3Phase.phaseSwitch (stepMems (e3Prepared mem input n) n mm (2 * k)) n)
    n bsize esize msize mm minv _ k (by omega) hn hn8 e hm
    (Model.fastRepresents_lt hmod) htwo invSwitch hbaseSwitch (Nat.mod_lt _ hm)
  have invFinal := stepInv_stepMems (by omega) hn8 invSwitch k
  have hflagFirst : MachineState.readWord (stepMems (e3Prepared mem input n) n mm (2 * k)) 1760 =
      UInt256.ofNat 1 := flag_after_steps (m2Of mem input n) _ n mm (2 * k) (by omega) hn8
  have hflagSwitch := phaseSwitch_flag_zero (stepMems (e3Prepared mem input n) n mm (2 * k)) n hn8
  have hflagFinal := flag_after_steps_of_read _ (UInt256.ofNat 0) n mm k (by omega) hn8 hflagSwitch
  have guard := bindings.e3Guard hhit
  rw [hhalf] at guard
  have switch := bindings.phaseSwitch hhit.2.2 _ hflagFirst
  rw [hquarter] at switch
  exact ((((bindings.prologue.trans guard).trans firstLoop).trans switch).trans secondLoop).trans
    (bindings.finalTail _ hflagFinal invFinal.frame.s32)

#print axioms phaseSwitch_flag_zero
#print axioms flag_after_steps_of_read
#print axioms ordinaryTrace
#print axioms e3Trace
end RootE3Trace

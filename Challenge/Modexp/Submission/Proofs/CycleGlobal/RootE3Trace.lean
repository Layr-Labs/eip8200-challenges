import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
import Challenge.Modexp.Submission.Proofs.CycleGlobal.GateRaw
import Challenge.Modexp.Submission.Proofs.CycleGlobal.StackPhaseRun
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.StackPhaseMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RootE3LoopCount
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CycleSubmission.Global.RootE3Trace
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open CycleSubmission.Global.RootE3Trace

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift CycleSubmission.Global.StackPhaseMath

/-- The E3/ordinary guard lives inside `E5` (`blk2764`); the prologue fields
below therefore land directly on the shift loop head. -/

def Eligible (input : ByteArray) (n bsize esize : Nat) : Prop :=
  esize = 1 ∧ FixedExponentRoute.exponentValue input bsize 1 = 3 ∧ (n = 4 ∨ n = 8)

/-- All concrete caller obligations are fields. Neither loop trace nor a whole route is assumed.
The named Shift states follow MAIN's relocated PC definitions when instantiated in J. -/
structure TraceBindings (s : State) (mem input : ByteArray) (n bsize esize msize : Nat) where
  prologueOrdinary : ¬ Eligible input n bsize esize →
    GasSteps (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 2310)
        (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0))
        (prepareMemory (CycleSubmission.Global.Fast.Shift.m2Of mem input n) (UInt256.ofNat 0))
        n bsize esize msize n)
  prologueE3 : Eligible input n bsize esize →
    GasSteps (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 2310)
        (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 1))
        (e3Prepared mem input n) n bsize esize msize (n / 2))
  phaseSwitch : (n = 4 ∨ n = 8) → ∀ isInline : Bool, ∀ phaseMem : ByteArray,
    GasSteps (if isInline then
        CycleSubmission.Global.Fast.Shift.csubExit4State (UInt256.ofNat 2310)
          (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 1)) phaseMem n bsize esize msize
      else CycleSubmission.Global.Fast.Shift.shiftDoneState (UInt256.ofNat 2310)
          (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 1)) phaseMem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 2298)
        (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0))
        (CycleSubmission.Global.StackPhaseMath.phaseSwitch phaseMem n) n bsize esize msize (n / 4))
  finalTail : ∀ isInline : Bool, ∀ phaseMem : ByteArray,
    MachineState.readWord phaseMem 2688 = UInt256.ofNat (32 * n) →
    GasSteps (if isInline then
        CycleSubmission.Global.Fast.Shift.csubExit4State (UInt256.ofNat 2310)
          (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0)) phaseMem n bsize esize msize
      else CycleSubmission.Global.Fast.Shift.shiftDoneState (UInt256.ofNat 2310)
          (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0)) phaseMem n bsize esize msize)
      (CycleSubmission.Global.GateRaw.entryState s phaseMem n bsize esize msize)
  e3Tail : ∀ isInline : Bool, ∀ phaseMem : ByteArray,
    GasSteps (if isInline then
        CycleSubmission.Global.Fast.Shift.csubExit4State (UInt256.ofNat 2298)
          (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0)) phaseMem n bsize esize msize
      else CycleSubmission.Global.Fast.Shift.shiftDoneState (UInt256.ofNat 2298)
          (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0)) phaseMem n bsize esize msize)
      (CycleSubmission.Global.SlimFrames.frameState s phaseMem 2298 n bsize esize msize)

/-- Ordinary route: carry stack tag0, execute exactly n inherited reductions, then the R1 tail. -/
def ordinaryTrace (s : State) (mem input : ByteArray) (n bsize esize msize mm minv : Nat)
    (bindings : TraceBindings s mem input n bsize esize msize)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hbs : bsize = 32 * n) (e : CycleSubmission.Global.Fast.Shift.Env s)
    (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize 0) (hmod : Model.FastRepresents mem 0 n mm)
    (hminvDef : minv = Setup.negWord (Setup.newton8 (mm % Limbs.radix)))
    (htop : R1.TopBitSet mem) (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hmiss : ¬ Eligible input n bsize esize)
    (hfast : n = 4 ∨ n = 8) :
    GasSteps (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize)
      (CycleSubmission.Global.GateRaw.entryState s (ordinaryFinal mem input n mm) n bsize esize msize) := by
  have inv0 := CycleSubmission.Global.Fast.Shift.m2_stepInv mem input n bsize mm minv hn hn8 hm hodd hframe hmod hminvDef
  have invPrep := prepareMemory_inv _ (UInt256.ofNat 0) n bsize mm minv hn8 inv0
  have hbase0 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have hbasePrep := prepareMemory_preserves _ (UInt256.ofNat 0) 2112 n _
    (Or.inr (by omega)) hbase0
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  obtain ⟨isInline, loop⟩ := CycleSubmission.Global.Fast.Shift.gasSteps_shiftLoop_count (UInt256.ofNat 2310) (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0))
    (prepareMemory (CycleSubmission.Global.Fast.Shift.m2Of mem input n) (UInt256.ofNat 0))
    n bsize esize msize mm minv _ n (by omega) (by omega) hn hn8 hbs (e.tagged (UInt256.ofNat 0)) hm (Model.fastRepresents_lt hmod)
    htwo invPrep hbasePrep (Nat.mod_lt _ hm) hfast
  have invFinal := CycleSubmission.Global.Fast.Shift.stepInv_stepMems (by omega) hn8 invPrep n
  exact ((bindings.prologueOrdinary hmiss).trans loop).trans
    (bindings.finalTail isInline _ invFinal.frame.s32)

/-- E3 route: exactly `2k` reductions with stack tag1, the copy phase change
(which sets exit tag12 and stack tag0), exactly `k` reductions, then cleanup
to the exponent-three continuation at2296. -/
def e3Trace (s : State) (mem input : ByteArray) (n bsize esize msize mm minv k : Nat)
    (bindings : TraceBindings s mem input n bsize esize msize)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hbs : bsize = 32 * n) (hnk : n = 4 * k) (e : CycleSubmission.Global.Fast.Shift.Env s)
    (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize 0) (hmod : Model.FastRepresents mem 0 n mm)
    (hminvDef : minv = Setup.negWord (Setup.newton8 (mm % Limbs.radix)))
    (htop : R1.TopBitSet mem) (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hhit : Eligible input n bsize esize) :
    GasSteps (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize)
      (CycleSubmission.Global.SlimFrames.frameState s (e3Final mem input n mm k) 2298 n bsize esize msize) := by
  have hhalf : n / 2 = 2 * k := by omega
  have inv0 := CycleSubmission.Global.Fast.Shift.m2_stepInv mem input n bsize mm minv hn hn8 hm hodd hframe hmod hminvDef
  have hquarter : n / 4 = k := by omega
  have invPrep := prepareMemory_inv _ (UInt256.ofNat 1) n bsize mm minv hn8 inv0
  have hbase0 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have hbasePrep := prepareMemory_preserves _ (UInt256.ofNat 1) 2112 n _
    (Or.inr (by omega)) hbase0
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  obtain ⟨inlineFirst, firstLoop⟩ := CycleSubmission.Global.Fast.Shift.gasSteps_shiftLoop_count (UInt256.ofNat 2310) (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 1)) (e3Prepared mem input n)
    n bsize esize msize mm minv _ (2 * k) (by omega) (by omega) hn hn8 hbs (e.tagged (UInt256.ofNat 1)) hm
    (Model.fastRepresents_lt hmod) htwo invPrep hbasePrep (Nat.mod_lt _ hm) hhit.2.2
  have invFirst := CycleSubmission.Global.Fast.Shift.stepInv_stepMems (by omega) hn8 invPrep (2 * k)
  have hbaseFirst := stepMems_represents (e3Prepared mem input n) n mm _ hn hn8 hm
    (Model.fastRepresents_lt hmod) htwo invPrep.modulus invPrep.neg hbasePrep
    (Nat.mod_lt _ hm) invPrep.pre (2 * k)
  have invSwitch := phaseSwitch_inv _ n bsize mm minv hn8 invFirst
  have hbaseSwitch := phaseSwitch_preserves _ n 2112 n _ (Or.inr (by omega))
    (Or.inl (by omega)) hbaseFirst
  obtain ⟨inlineSecond, secondLoop⟩ := CycleSubmission.Global.Fast.Shift.gasSteps_shiftLoop_count (UInt256.ofNat 2298) (CycleSubmission.Global.Fast.Shift.taggedTemplate s (UInt256.ofNat 0))
    (CycleSubmission.Global.StackPhaseMath.phaseSwitch (stepMems (e3Prepared mem input n) n mm (2 * k)) n)
    n bsize esize msize mm minv _ k (by omega) (by omega) hn hn8 hbs (e.tagged (UInt256.ofNat 0)) hm
    (Model.fastRepresents_lt hmod) htwo invSwitch hbaseSwitch (Nat.mod_lt _ hm) hhit.2.2
  have guard := bindings.prologueE3 hhit
  rw [hhalf] at guard
  have switch := bindings.phaseSwitch hhit.2.2 inlineFirst
    (stepMems (e3Prepared mem input n) n mm (2 * k))
  rw [hquarter] at switch
  exact ((((guard.trans firstLoop).trans switch).trans secondLoop).trans
    (bindings.e3Tail inlineSecond _))

end CycleSubmission.Global.RootE3Trace


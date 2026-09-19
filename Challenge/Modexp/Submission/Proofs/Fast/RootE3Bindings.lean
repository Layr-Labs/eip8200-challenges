import Challenge.Modexp.Submission.Proofs.Fast.RootE3Trace
import Challenge.Modexp.Submission.Proofs.Fast.RootE3Guard
import Challenge.Modexp.Submission.Proofs.Fast.RootE3PhaseRun
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace RootE3Bindings
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding Shift

/-- The twenty new instructions inserted immediately before the relocated loop head. -/
def entryGuard : Block Artifact.submissionArtifact .Osaka 2733 RootE3Guard.program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2210 20 2733 RootE3Guard.program
    (by decide) (by rfl) (by rfl) (by decide)

/-- The phase exit is split where the conditional branch changes control flow. -/
def phases : RootE3PhaseRun.PhaseBlocks Artifact.submissionArtifact .Osaka where
  exitHead := WindowTwentyOneSlice.block Artifact.allWellFormed 2680 2 3337
    RootE3PhaseRun.phaseExitHeadProgram (by decide) (by rfl) (by rfl) (by decide)
  guard := WindowTwentyOneSlice.block Artifact.allWellFormed 2682 5 3339
    RootE3PhaseRun.phaseGuardProgram (by decide) (by rfl) (by rfl) (by decide)
  switch := WindowTwentyOneSlice.block Artifact.allWellFormed 2687 12 3348
    RootE3PhaseRun.phaseSwitchProgram (by decide) (by rfl) (by rfl) (by decide)
  done := WindowTwentyOneSlice.block Artifact.allWellFormed 2699 1 3369
    RootE3PhaseRun.phaseDoneProgram (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest3039 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2760 = true :=
  Artifact.isValidJumpDest_index 2230 (by rfl)

theorem jumpDest3542 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3369 = true :=
  Artifact.isValidJumpDest_index 2699 (by rfl)

/-- The inherited loop guard consumes no memory and reaches the new phase test. -/
def headSteps (s : State) (mem : ByteArray) (n bsize esize msize : Nat) (e : Env s) :
    GasSteps (shiftLoopState s mem n bsize esize msize 0)
      (RootE3PhaseRun.frame s mem 3339 (Exp.outer n bsize esize msize)) := by
  have first := soundEnv blk3013 e (run_shiftHead_done s mem n bsize esize msize e.code e.run)
  have second := phases.exitHead.steps (bindingEnv e) rfl
    (RootE3PhaseRun.run_phaseExitHead s mem (UInt256.ofNat 0)
      (Exp.outer n bsize esize msize) (by simp [Exp.outer]))
  exact first.trans (by
    simpa only [shiftDoneState, kState, pcShiftDone, outer, RootE3PhaseRun.frame] using second)

def switchSteps (s : State) (mem : ByteArray) (n bsize esize msize : Nat) (e : Env s)
    (hn : n = 4 ∨ n = 8)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1) :
    GasSteps (shiftLoopState s mem n bsize esize msize 0)
      (shiftLoopState s (RootE3Phase.phaseSwitch mem n) n bsize esize msize (n / 4)) := by
  have hd3542 : Decode.isValidJumpDest s.executionEnv.code 3369 = true := by
    rw [e.code]; exact jumpDest3542
  have hd3039 : Decode.isValidJumpDest s.executionEnv.code 2760 = true := by
    rw [e.code]; exact jumpDest3039
  have guard := phases.guardOneSteps s mem (Exp.outer n bsize esize msize)
    (by simp [Exp.outer]) e.act hflag hd3542 (bindingEnv e)
  have switch := phases.switchSteps s mem n
    [UInt256.ofNat bsize, UInt256.ofNat esize, UInt256.ofNat msize]
    hn (by simp) e.act hd3039 (bindingEnv e)
  exact (headSteps s mem n bsize esize msize e).trans (guard.trans (by
    simpa only [Exp.outer, List.cons_append, List.nil_append,
      shiftLoopState, kState, pcShiftLoop, outer, RootE3PhaseRun.frame,
      RootE3PhaseRun.phaseSwitchMemory, RootE3Phase.phaseSwitch] using switch))

/-- Flag zero takes the inherited R1 copy after the new phase-done JUMPDEST. -/
def tailSteps (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (e : Env s)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n)) :
    GasSteps (shiftLoopState s mem n bsize esize msize 0)
      (FixedExponentRoute.entryState s
        (Exp.mcopyMem (Exp.mcopyMem mem 512 2112 (32 * n)) 1024 1280 (32 * n))
        n bsize esize msize) := by
  have hd3542 : Decode.isValidJumpDest s.executionEnv.code 3369 = true := by
    rw [e.code]; exact jumpDest3542
  have guard := phases.guardZeroSteps s mem (Exp.outer n bsize esize msize)
    (by simp [Exp.outer]) e.act hflag hd3542 (bindingEnv e)
  have done := phases.done.steps (bindingEnv e) rfl
    (RootE3PhaseRun.run_phaseDone s mem (Exp.outer n bsize esize msize)
      (by simp [Exp.outer]))
  have tail := soundEnv blk3264 e
    (run_shiftDone s mem n bsize esize msize (by omega) hn8 e.act296 hs32 e.code e.run)
  exact (((headSteps s mem n bsize esize msize e).trans guard).trans done).trans (by
    simpa only [RootE3PhaseRun.frame, frameState, outer, FixedExponentRoute.entryState] using tail)

/-- All concrete v4 caller certificates, with no whole-loop or whole-route premise. -/
def build (s : State) (mem input : ByteArray) (n bsize esize msize minv : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (e : Env s) (hdata : s.executionEnv.calldata = input)
    (hframe : Exp.Frame mem n bsize minv) (hmatch : FullBase.Matches mem n bsize)
    (hfast : n = 4 ∨ n = 8) :
    RootE3Trace.TraceBindings s mem input n bsize esize msize := by
  have hm1ml : MachineState.readWord (m1Of mem input n) 2752 = UInt256.ofNat (32 * n - 32) := by
    rw [m1_readWord_disjoint mem input n 2752 (by omega) hn8
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩]
    exact hframe.ml
  have heoff : MachineState.readWord (m2Of mem input n) 2816 = UInt256.ofNat (96 + bsize) := by
    rw [m2_readWord_disjoint mem input n 2816 (by omega) hn8
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by unfold NEG; omega),
        Or.inr (by unfold PRE_DINV; omega), Or.inr (by omega), Or.inr (by omega)⟩]
    exact hframe.eoff
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hdispatch := run_dispatch s mem n bsize esize msize hn8 (by omega) e.act296 e.code e.run
    rw [if_pos hmatch] at hdispatch
    have first := soundEnv blk2862 e hdispatch
    have second := gasSteps_hitCsub s mem input n bsize esize msize hn hn8 e hdata
      hframe.ml hframe.tl hframe.s32 hfast
    have third := gasSteps_prologue s (m1Of mem input n) n bsize esize msize
      (by omega) hn8 e hm1ml
    simpa only [m1Of, m2Of, RootE3Trace.guardEntry, kState, outer] using
      first.trans (second.trans third)
  · intro hmiss
    have hmiss' : ¬ (esize = 1 ∧
        FixedExponentRoute.exponentValue s.executionEnv.calldata bsize 1 = 3 ∧
          (n = 4 ∨ n = 8)) := by
      simpa only [hdata, RootE3Trace.Eligible] using hmiss
    have run := RootE3Guard.run_guard s (m2Of mem input n) n bsize esize msize e.act
    rw [RootE3Guard.result_ordinary s (m2Of mem input n) n bsize esize msize
      hn hn8 hb he heoff hmiss'] at run
    simpa only [RootE3Guard.entry, RootE3Trace.guardEntry, shiftLoopState, kState,
      pcShiftLoop, outer, RootE3Phase.flagSet] using
      entryGuard.steps (bindingEnv e) rfl run
  · intro hhit
    have hhit' : esize = 1 ∧
        FixedExponentRoute.exponentValue s.executionEnv.calldata bsize 1 = 3 ∧
          (n = 4 ∨ n = 8) := by
      simpa only [hdata, RootE3Trace.Eligible] using hhit
    have run := RootE3Guard.run_guard s (m2Of mem input n) n bsize esize msize e.act
    rw [RootE3Guard.result_e3 s (m2Of mem input n) n bsize esize msize
      hn hn8 hb he heoff hhit'] at run
    simpa only [RootE3Guard.entry, RootE3Trace.guardEntry, shiftLoopState, kState,
      pcShiftLoop, outer, RootE3Phase.e3Prepared, RootE3Phase.flagSet] using
      entryGuard.steps (bindingEnv e) rfl run
  · intro hsize phaseMem hflag
    exact switchSteps s phaseMem n bsize esize msize e hsize hflag
  · intro phaseMem hflag hs32
    exact tailSteps s phaseMem n bsize esize msize hn hn8 e hflag hs32

end RootE3Bindings

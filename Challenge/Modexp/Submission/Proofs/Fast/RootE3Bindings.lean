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


/-- The phase exit is split where the conditional branch changes control flow:
exit head at idx 2696 (pc 3346), guard at idx 2698 (pc 3348, `JUMPI` to the
cleanup tail at 5444), switch at idx 2703 (pc 3357, jump back to 2811). -/
def phases : RootE3PhaseRun.PhaseBlocks Artifact.submissionArtifact .Osaka where
  exitHead := WindowTwentyOneSlice.block Artifact.allWellFormed 2696 2 3346
    RootE3PhaseRun.phaseExitHeadProgram (by decide) (by rfl) (by rfl) (by decide)
  guard := WindowTwentyOneSlice.block Artifact.allWellFormed 2698 5 3348
    RootE3PhaseRun.phaseGuardProgram (by decide) (by rfl) (by rfl) (by decide)
  switch := WindowTwentyOneSlice.block Artifact.allWellFormed 2703 12 3357
    RootE3PhaseRun.phaseSwitchProgram (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest2811 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2811 = true :=
  Artifact.isValidJumpDest_index 2260 (by rfl)

/-- The inherited loop guard consumes no memory and reaches the phase-exit head. -/
def headSteps (s : State) (mem : ByteArray) (n bsize esize msize : Nat) (e : Env s) :
    GasSteps (shiftLoopState s mem n bsize esize msize 0)
      (shiftDoneState s mem n bsize esize msize) :=
  soundEnv blk3013 e (run_shiftHead_done s mem n bsize esize msize e.code e.run)

/-! ## Junction lemmas

Each is stated so the switch/tail chains can be composed through
`GasSteps.cast` with syntactically matching intermediate states.  Every proof
is pure delta-reduction: no `entrySlots`/`readWord` application is ever whnf'd
(their two sides are the same folded term), which is what keeps the old
8M-heartbeat unifier bombs away. -/

/-- `shiftDoneState` is the exit head's start frame (pc 3346, counter `0`). -/
theorem shiftDone_eq_exitStart (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    shiftDoneState s mem n bsize esize msize =
      RootE3PhaseRun.frame s mem 3346
        (UInt256.ofNat 0 :: Shift.entrySlots mem n bsize esize ++
          Exp.outer n bsize esize msize) :=
  rfl

/-- The phase switch (clear flag at 1760, copy `32 n` bytes 2112 -> 256)
touches none of the eleven frame words the riding slots read. -/
theorem phaseSwitch_entrySlots (mem : ByteArray) (n bsize esize : Nat) (hn8 : n ≤ 8) :
    Shift.entrySlots (RootE3Phase.phaseSwitch mem n) n bsize esize =
      Shift.entrySlots mem n bsize esize := by
  unfold Shift.entrySlots Shift.rideSlots
  rw [RootE3Phase.phaseSwitch_readWord mem n 1312 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1344 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1376 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1408 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1440 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1472 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1504 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1632 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1664 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1568 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 1536 (Or.inl (by omega)) (Or.inr (by omega))]

/-- The switch's exit frame is the loop head over the switched memory
(`phaseSwitchMemory` and `RootE3Phase.phaseSwitch` are the same function). -/
theorem switchEnd_eq (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    RootE3PhaseRun.frame s (RootE3PhaseRun.phaseSwitchMemory mem n) 2811
        (UInt256.ofNat (n / 4) :: Shift.entrySlots mem n bsize esize ++
          Exp.outer n bsize esize msize) =
      shiftLoopState s (RootE3Phase.phaseSwitch mem n) n bsize esize msize (n / 4) := by
  have hslots := phaseSwitch_entrySlots mem n bsize esize hn8
  unfold Shift.shiftLoopState Shift.slotKState RootE3PhaseRun.frame Shift.pcShiftLoop
  rw [hslots]
  rfl

/-- The done stub lands on the fixed-exponent dispatcher entry. -/
theorem frameState_bdone_eq (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    frameState s mem 2441 n bsize esize msize =
      FixedExponentRoute.entryState s mem n bsize esize msize :=
  rfl

/-! ## The prologue-end spelling bridge -/

/-- The shift entry word and the cache model's entry word agree on the two
widths the dispatcher selects between. -/
theorem shiftEntry_eq_entryWord (n : Nat) (hn : n = 4 ∨ n = 8) :
    Shift.shiftEntry n = ShiftCacheModel.entryWord n := by
  rcases hn with rfl | rfl <;> rfl
/-- The word at 2816 (the exponent offset) survives the cache store at 1698. -/
theorem m2_readWord_2816 (mem input : ByteArray) (n : Nat) :
    MachineState.readWord (preMem (negStep (m1Of mem input n) n n).memory) 2816 =
      MachineState.readWord (m2Of mem input n) 2816 := by
  unfold m2Of
  rw [ShiftCacheModel.read_disjoint _ n 2816 (Or.inr (by omega))]

/-- The E3 prologue's published memory in the cache model's spelling. -/
theorem prologue_e3_end_eq (mem input : ByteArray) (n : Nat) :
    RootE3Phase.e3Prepared mem input n =
      Exp.storeWord (Exp.storeWord (preMem (negStep (m1Of mem input n) n n).memory) 1698
        (ShiftCacheModel.entryWord n)) 1760 (UInt256.ofNat 1) :=
  rfl

/-- The ordinary prologue's published memory in the cache model's spelling. -/
theorem flagSet_m2Of_eq (mem input : ByteArray) (n : Nat) (flag : UInt256) :
    RootE3Phase.flagSet (m2Of mem input n) flag =
      Exp.storeWord (Exp.storeWord (preMem (negStep (m1Of mem input n) n n).memory) 1698
        (ShiftCacheModel.entryWord n)) 1760 flag :=
  rfl

/-- Word-sized naturals are equal when their embedded words are. -/
private theorem nat_eq_of_word {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : UInt256.ofNat a = UInt256.ofNat b) : a = b := by
  have h' := congrArg UInt256.toNat h
  rwa [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- Flag set: the guard falls through into the switch, which publishes the
retained accumulator into `ACC`, halves the loop counter and jumps back to the
shift loop head. -/
def switchSteps (s : State) (mem : ByteArray) (n bsize esize msize : Nat) (e : Env s)
    (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1) :
    GasSteps (shiftLoopState s mem n bsize esize msize 0)
      (shiftLoopState s (RootE3Phase.phaseSwitch mem n) n bsize esize msize (n / 4)) := by
  have hd5444 : Decode.isValidJumpDest s.executionEnv.code 5444 = true := by
    rw [e.code]; exact jumpDest5444
  have hd2811 : Decode.isValidJumpDest s.executionEnv.code 2811 = true := by
    rw [e.code]; exact jumpDest2811
  have hslots : (Shift.entrySlots mem n bsize esize ++ Exp.outer n bsize esize msize).length ≤ 1000 := by
    simp [Shift.entrySlots, Shift.rideSlots, Exp.outer]
  have exit := phases.exitHead.steps (bindingEnv e) rfl
    (RootE3PhaseRun.run_phaseExitHead s mem (UInt256.ofNat 0)
      (Shift.entrySlots mem n bsize esize ++ Exp.outer n bsize esize msize) hslots)
  have guard := phases.guardOneSteps s mem
    (Shift.entrySlots mem n bsize esize ++ Exp.outer n bsize esize msize)
    hslots e.act hflag hd5444 (bindingEnv e)
  have switch := phases.switchSteps s mem n bsize esize msize
    (Shift.entrySlots mem n bsize esize ++ Exp.outer n bsize esize msize)
    hn hbs hslots e.act rfl hd2811 (bindingEnv e)
  exact (((headSteps s mem n bsize esize msize e).cast rfl
      (shiftDone_eq_exitStart s mem n bsize esize msize)).trans exit).trans
    ((guard.trans switch).cast rfl
      (switchEnd_eq s mem n bsize esize msize (by omega) (by omega)))

/-- Flag clear: the guard jumps to the cleanup tail (seventeen `POP`s and the
done stub), which lands on the exponent-phase dispatcher entry at pc 2441 with
the memory unchanged. -/
def tailSteps (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (e : Env s)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n)) :
    GasSteps (shiftLoopState s mem n bsize esize msize 0)
      (FixedExponentRoute.entryState s mem n bsize esize msize) := by
  have check := soundEnv blk3346 e
    (run_shiftDone_check s mem n bsize esize msize e.act hflag e.code e.run)
  have cleanup := soundEnv blk5444 e (run_cleanup s mem n bsize esize msize e.code e.run)
  have stub := soundEnv blk3378 e (run_bdoneStub s mem n bsize esize msize e.code e.run)
  exact (((headSteps s mem n bsize esize msize e).trans check).trans cleanup).trans
    (stub.cast rfl (frameState_bdone_eq s mem n bsize esize msize))

/-- All concrete v4 caller certificates, with no whole-loop or whole-route premise. -/
def build (s : State) (mem input : ByteArray) (n bsize esize msize minv : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (e : Env s) (hdata : s.executionEnv.calldata = input)
    (hframe : Exp.Frame mem n bsize minv)
    (hmatch : FullBase.Matches mem n bsize) (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
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
  have heoff' : MachineState.readWord (preMem (negStep (m1Of mem input n) n n).memory) 2816 =
      UInt256.ofNat (96 + bsize) :=
    (m2_readWord_2816 mem input n).trans heoff
  have hse := shiftEntry_eq_entryWord n hfast
  have hdispatch := run_dispatch s mem n bsize esize msize hn8 (by omega) e.act296 e.code e.run
  rw [if_pos hmatch] at hdispatch
  have first := soundEnv blk2862 e hdispatch
  have second := gasSteps_hitCsub s mem input n bsize esize msize hn hn8 e hdata
    hframe.ml hframe.tl hframe.s32 htn0 hfast
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmiss
    by_cases hes1 : UInt256.ofNat esize = UInt256.ofNat 1
    · have hes : esize = 1 := nat_eq_of_word (by omega) (by decide) hes1
      have evne : FixedExponentRoute.exponentValue input bsize 1 ≠ 3 := by
        intro hv
        exact hmiss ⟨hes, hv, hfast⟩
      have hebne : RootE3Guard.exponentByte
          (preMem (negStep (m1Of mem input n) n n).memory) s.executionEnv.calldata ≠
          UInt256.ofNat 3 := by
        rw [RootE3Guard.exponentByte_spec _ _ bsize hb heoff', hdata]
        intro h
        have hlt := RootE3Guard.exponentValue_one_lt input bsize
        exact evne (nat_eq_of_word (by omega) (by decide) h)
      have third := gasSteps_prologue_slow s (m1Of mem input n) n bsize esize msize
        (by omega) hn8 e hfast hes1 hebne hm1ml
      rw [hse] at third
      exact (first.trans (second.trans third)).cast rfl
        (congrArg (fun m => shiftLoopState s m n bsize esize msize n)
          (flagSet_m2Of_eq mem input n (UInt256.ofNat 0)).symm)
    · have third := gasSteps_prologue s (m1Of mem input n) n bsize esize msize
        (by omega) hn8 e hfast hes1 hm1ml
      rw [hse] at third
      exact (first.trans (second.trans third)).cast rfl
        (congrArg (fun m => shiftLoopState s m n bsize esize msize n)
          (flagSet_m2Of_eq mem input n (UInt256.ofNat 0)).symm)
  · intro hhit
    have hes1 : UInt256.ofNat esize = UInt256.ofNat 1 := by rw [hhit.1]
    have heb : RootE3Guard.exponentByte
        (preMem (negStep (m1Of mem input n) n n).memory) s.executionEnv.calldata =
        UInt256.ofNat 3 := by
      rw [RootE3Guard.exponentByte_spec _ _ bsize hb heoff', hdata]
      exact congrArg UInt256.ofNat hhit.2.1
    have third := gasSteps_prologue_e3 s (m1Of mem input n) n bsize esize msize
      (by omega) hn8 e hfast hes1 heb hm1ml
    rw [hse] at third
    exact (first.trans (second.trans third)).cast rfl
      (congrArg (fun m => shiftLoopState s m n bsize esize msize (n / 2))
        (prologue_e3_end_eq mem input n).symm)
  · intro hsize phaseMem hflag
    exact switchSteps s phaseMem n bsize esize msize e hsize hmatch.1 hflag
  · intro phaseMem hflag hs32
    exact tailSteps s phaseMem n bsize esize msize hn hn8 e hflag hs32

#print axioms build

end RootE3Bindings

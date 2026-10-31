import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RootE3Trace
import Challenge.Modexp.Submission.Proofs.Fast.RootE3Guard
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RootE3PhaseRun
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace CycleSubmission.Global.RootE3Bindings
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open RootE3Bindings

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding Shift


/-- The phase exit is split where the conditional branch changes control flow:
exit head at idx 2597 (pc 3346), guard at idx 2599 (pc 3348, `JUMPI` to the
cleanup tail at 3866), switch at idx 2604 (pc 3357, jump back to the loop head). -/
def phases : RootE3PhaseRun.PhaseBlocks CycleSubmission.Artifact.artifact .Osaka where
  exitHead := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2388 2 3069 RootE3PhaseRun.phaseExitHeadProgram (by decide) (by rfl) (by rfl) (by decide)
  guard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2390 5 3071 RootE3PhaseRun.phaseGuardProgram (by decide) (by rfl) (by rfl) (by decide)
  switch := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2395 14 3080 RootE3PhaseRun.phaseSwitchProgram (by decide) (by rfl) (by rfl) (by decide)


/-! ## Junction lemmas

Each is stated so the switch/tail chains can be composed through
`GasSteps.cast` with syntactically matching intermediate states.  Every proof
is pure delta-reduction: no `CycleSubmission.Global.Fast.Shift.entrySlots`/`readWord` application is ever whnf'd
(their two sides are the same folded term), which is what keeps the old
8M-heartbeat unifier bombs away. -/

/-- `CycleSubmission.Global.Fast.Shift.shiftDoneState` is the exit head's start frame (pc 3346, counter `0`). -/
theorem shiftDone_eq_exitStart (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    CycleSubmission.Global.Fast.Shift.shiftDoneState z s mem n bsize esize msize =
      RootE3PhaseRun.frame s mem 3069
        (UInt256.ofNat 0 :: CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize ++
          Exp.outer n bsize esize msize) :=
  rfl

/-- The phase switch (clear flag at 1760, copy `32 n` bytes 2112 -> 256)
touches none of the eleven frame words the riding slots read. -/
theorem phaseSwitch_entrySlots (z : UInt256) (mem : ByteArray) (n bsize esize : Nat)
    (hn8 : n ≤ 8) :
    CycleSubmission.Global.Fast.Shift.entrySlots z (RootE3Phase.phaseSwitch mem n) n bsize esize =
      CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize := by
  unfold CycleSubmission.Global.Fast.Shift.entrySlots
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
    RootE3Phase.phaseSwitch_readWord mem n 1536 (Or.inl (by omega)) (Or.inr (by omega)),
    RootE3Phase.phaseSwitch_readWord mem n 32 (Or.inl (by omega)) (Or.inl (by omega))]

/-- The switch's exit frame is the loop head over the switched memory
(`phaseSwitchMemory` and `RootE3Phase.phaseSwitch` are the same function). -/
theorem switchEnd_eq (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    RootE3PhaseRun.frame s (RootE3PhaseRun.phaseSwitchMemory mem n) (CycleSubmission.Global.Fast.Shift.headPC n)
        (UInt256.ofNat (n / 4) :: CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 12) mem n bsize esize ++
          Exp.outer n bsize esize msize) =
      CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 12) s (RootE3Phase.phaseSwitch mem n) n bsize esize msize
        (n / 4) := by
  have hslots := phaseSwitch_entrySlots (UInt256.ofNat 12) mem n bsize esize hn8
  unfold CycleSubmission.Global.Fast.Shift.shiftLoopState CycleSubmission.Global.Fast.Shift.slotKState RootE3PhaseRun.frame
  rw [hslots]
  rfl

/-- The done stub lands on the fixed-exponent dispatcher entry. -/
theorem frameState_bdone_eq (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    CycleSubmission.Global.Fast.Shift.frameState s mem 2317 n bsize esize msize =
      FixedExponentRoute.entryState s mem n bsize esize msize :=
  rfl

/-! ## The prologue-end spelling bridge -/

/-- The shift entry word and the cache model's entry word agree on the two
widths the dispatcher selects between. -/
theorem shiftEntry_eq_entryWord (n : Nat) (hn : n = 4 ∨ n = 8) :
    CycleSubmission.Global.Fast.Shift.shiftEntry n = ShiftCacheModel.entryWord n := by
  rcases hn with rfl | rfl <;> rfl
/-- The word at 2656 (the exponent offset) survives the cache store at 1698. -/
theorem m2_readWord_2816 (mem input : ByteArray) (n : Nat) :
    MachineState.readWord (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) 2656 =
      MachineState.readWord (CycleSubmission.Global.Fast.Shift.m2Of mem input n) 2656 := by
  unfold CycleSubmission.Global.Fast.Shift.m2Of
  rw [ShiftCacheModel.read_disjoint _ n 2656 (Or.inr (by omega))]

/-- The E3 prologue's published memory in the cache model's spelling. -/
theorem prologue_e3_end_eq (mem input : ByteArray) (n : Nat) :
    RootE3Phase.e3Prepared mem input n =
      Exp.storeWord (Exp.storeWord (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) 1698
        (ShiftCacheModel.entryWord n)) 1760 (UInt256.ofNat 1) :=
  rfl

/-- The ordinary prologue's published memory in the cache model's spelling. -/
theorem flagSet_m2Of_eq (mem input : ByteArray) (n : Nat) (flag : UInt256) :
    RootE3Phase.flagSet (CycleSubmission.Global.Fast.Shift.m2Of mem input n) flag =
      Exp.storeWord (Exp.storeWord (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) 1698
        (ShiftCacheModel.entryWord n)) 1760 flag :=
  rfl

/-- Word-sized naturals are equal when their embedded words are. -/
private theorem nat_eq_of_word {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : UInt256.ofNat a = UInt256.ofNat b) : a = b := by
  have h' := congrArg UInt256.toNat h
  rwa [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- Flag set: the guard falls through into the switch, which clears the flag, sets the
exit slot to `28`, publishes the retained accumulator into `ACC`, halves the loop counter
and jumps back to the shift loop head. -/
def switchSteps (s : State) (mem : ByteArray) (n bsize esize msize : Nat) (e : CycleSubmission.Global.Fast.Shift.Env s)
    (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1) :
    GasSteps (CycleSubmission.Global.Fast.Shift.shiftDoneState (UInt256.ofNat 0) s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 12) s (RootE3Phase.phaseSwitch mem n) n bsize esize msize
        (n / 4)) := by
  have hd5444 : Decode.isValidJumpDest s.executionEnv.code 3944 = true := by
    rw [e.code]; exact CycleSubmission.Global.Fast.jumpDest5444
  have hd2811 : Decode.isValidJumpDest s.executionEnv.code
      (CycleSubmission.Global.Fast.Shift.headPC n) = true := by
    rw [e.code]; exact CycleSubmission.Global.Fast.Shift.jumpDestHead n
  have hslots : (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize ++
      Exp.outer n bsize esize msize).length ≤ 1000 := by
    simp [CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.rideSlots, Exp.outer]
  have exit := phases.exitHead.steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (RootE3PhaseRun.run_phaseExitHead s mem (UInt256.ofNat 0)
      (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize ++ Exp.outer n bsize esize msize)
      hslots)
  have guard := phases.guardOneSteps s mem
    (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize ++ Exp.outer n bsize esize msize)
    hslots e.act hflag hd5444 (CycleSubmission.Global.Fast.Shift.bindingEnv e)
  have switch := phases.switchSteps s mem n bsize esize msize
    (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize ++ Exp.outer n bsize esize msize)
    hn hbs hslots e.act rfl hd2811 (CycleSubmission.Global.Fast.Shift.bindingEnv e)
  exact (exit.cast (shiftDone_eq_exitStart (UInt256.ofNat 0) s mem n bsize esize msize).symm
      rfl).trans
    ((guard.trans switch).cast rfl
      (switchEnd_eq s mem n bsize esize msize (by omega) (by omega)))

/-- Flag clear, exit slot `d`: the guard jumps to the cleanup tail, whose sixteen `POP`s
and `PUSH2 0989 ADD JUMP` land on `2441 + d` with the memory unchanged. -/
def tailSteps (s : State) (mem : ByteArray) (n bsize esize msize d target : Nat) (e : CycleSubmission.Global.Fast.Shift.Env s)
    (htarget : 2317 + d = target) (hlt : target < 2 ^ 256)
    (hdest : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode target = true)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0) :
    GasSteps (CycleSubmission.Global.Fast.Shift.shiftDoneState (UInt256.ofNat d) s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.frameState s mem target n bsize esize msize) := by
  have check := CycleSubmission.Global.Fast.Shift.soundEnv blk3346 e
    (CycleSubmission.Global.Fast.Shift.run_shiftDone_check (UInt256.ofNat d) s mem n bsize esize msize e.act hflag e.code e.run)
  have cleanup := CycleSubmission.Global.Fast.Shift.soundEnv blk5444 e
    (CycleSubmission.Global.Fast.Shift.run_cleanup s mem n bsize esize msize d target htarget hlt hdest e.code e.run)
  exact check.trans cleanup

/-- All concrete v4 caller certificates, with no whole-loop or whole-route premise. -/
def build (s : State) (mem input : ByteArray) (n bsize esize msize minv : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (e : CycleSubmission.Global.Fast.Shift.Env s) (hdata : s.executionEnv.calldata = input)
    (hframe : Exp.Frame mem n bsize 0)
    (hmatch : FullBase.Matches mem n bsize) (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hfast : n = 4 ∨ n = 8)
    (hn0odd : (MachineState.readWord mem (32 * n - 32)).toNat % 2 = 1) :
    RootE3Trace.TraceBindings s mem input n bsize esize msize := by
  -- the newton-batch tail inverts `dodd * n0`: both factors are odd on the hit arm
  have hm1n0 : (MachineState.readWord (CycleSubmission.Global.Fast.Shift.m1Of mem input n) (32 * n - 32)).toNat % 2 = 1 := by
    rw [CycleSubmission.Global.Fast.Shift.m1_readWord_disjoint mem input n (32 * n - 32) (by omega) hn8
      ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩]
    exact hn0odd
  have hm1d : (preDodd (MachineState.readWord (CycleSubmission.Global.Fast.Shift.m1Of mem input n) 0)).toNat % 2 = 1 := by
    rw [CycleSubmission.Global.Fast.Shift.m1_readWord_disjoint mem input n 0 (by omega) hn8
      ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩]
    apply preDodd_odd
    intro h
    have ht := hmatch.2
    unfold R1.TopBitSet at ht
    rw [h] at ht
    norm_num at ht
  have hm1ml : MachineState.readWord (CycleSubmission.Global.Fast.Shift.m1Of mem input n) 2752 = UInt256.ofNat (32 * n - 32) := by
    rw [CycleSubmission.Global.Fast.Shift.m1_readWord_disjoint mem input n 2752 (by omega) hn8
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩]
    exact hframe.ml
  have heoff : MachineState.readWord (CycleSubmission.Global.Fast.Shift.m2Of mem input n) 2656 = UInt256.ofNat (96 + bsize) := by
    rw [CycleSubmission.Global.Fast.Shift.m2_readWord_disjoint mem input n 2656 (by omega) hn8
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by unfold NEG; omega),
        Or.inr (by unfold PRE_DINV; omega), Or.inr (by omega), Or.inr (by omega)⟩
      (Or.inl (by omega))]
    exact hframe.eoff
  have heoff' : MachineState.readWord (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) 2656 =
      UInt256.ofNat (96 + bsize) :=
    (m2_readWord_2816 mem input n).trans heoff
  have hse := shiftEntry_eq_entryWord n hfast
  have hdispatch := CycleSubmission.Global.Fast.Shift.run_dispatch s mem n bsize esize msize hn8 (by omega) hmatch.2 e.code e.run
  rw [if_pos hmatch] at hdispatch
  have first := CycleSubmission.Global.Fast.Shift.soundEnv blk2862 e hdispatch
  have second := CycleSubmission.Global.Fast.Shift.gasSteps_hitCsub s mem input n bsize esize msize hn hn8 e hdata
    hframe.ml hframe.tl hframe.s32 htn0 hfast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hmiss
    by_cases hes1 : UInt256.ofNat esize = UInt256.ofNat 1
    · have hes : esize = 1 := nat_eq_of_word (by omega) (by decide) hes1
      have evne : FixedExponentRoute.exponentValue input bsize 1 ≠ 3 := by
        intro hv
        exact hmiss ⟨hes, hv, hfast⟩
      have hebne : RootE3Guard.exponentByte
          (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) s.executionEnv.calldata ≠
          UInt256.ofNat 3 := by
        rw [RootE3Guard.exponentByte_spec _ _ bsize hb heoff', hdata]
        intro h
        have hlt := RootE3Guard.exponentValue_one_lt input bsize
        exact evne (nat_eq_of_word (by omega) (by decide) h)
      have third := CycleSubmission.Global.Fast.Shift.gasSteps_prologue_slow s (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n bsize esize msize
        (by omega) hn8 e hfast hes1 hebne hm1ml hm1n0 hm1d
      rw [hse] at third
      exact (first.trans (second.trans third)).cast rfl
        (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 0) s m n bsize esize msize n)
          (flagSet_m2Of_eq mem input n (UInt256.ofNat 0)).symm)
    · have third := CycleSubmission.Global.Fast.Shift.gasSteps_prologue s (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n bsize esize msize
        (by omega) hn8 e hfast hes1 hm1ml hm1n0 hm1d
      rw [hse] at third
      exact (first.trans (second.trans third)).cast rfl
        (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 0) s m n bsize esize msize n)
          (flagSet_m2Of_eq mem input n (UInt256.ofNat 0)).symm)
  · intro hhit
    have hes1 : UInt256.ofNat esize = UInt256.ofNat 1 := by rw [hhit.1]
    have heb : RootE3Guard.exponentByte
        (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) s.executionEnv.calldata =
        UInt256.ofNat 3 := by
      rw [RootE3Guard.exponentByte_spec _ _ bsize hb heoff', hdata]
      exact congrArg UInt256.ofNat hhit.2.1
    have third := CycleSubmission.Global.Fast.Shift.gasSteps_prologue_e3 s (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n bsize esize msize
      (by omega) hn8 e hfast hes1 heb hm1ml hm1n0 hm1d
    rw [hse] at third
    exact (first.trans (second.trans third)).cast rfl
      (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 0) s m n bsize esize msize (n / 2))
        (prologue_e3_end_eq mem input n).symm)
  · intro hsize phaseMem hflag
    exact switchSteps s phaseMem n bsize esize msize e hsize hmatch.1 hflag
  · intro phaseMem hflag _hs32
    exact (tailSteps s phaseMem n bsize esize msize 0 2317 e rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest3412
      hflag).cast rfl (frameState_bdone_eq s phaseMem n bsize esize msize)
  · intro phaseMem hflag
    exact tailSteps s phaseMem n bsize esize msize 12 2329 e rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest2471 hflag


end CycleSubmission.Global.RootE3Bindings

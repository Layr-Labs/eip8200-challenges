import Challenge.Modexp.Submission.Proofs.CycleGlobal.PhaseFallthroughRun
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
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
      RootE3PhaseRun.frame s mem 3035
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
    CycleSubmission.Global.Fast.Shift.frameState s mem 2284 n bsize esize msize =
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
      Exp.storeWord (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) 1760 (UInt256.ofNat 1) :=
  rfl

/-- The ordinary prologue's published memory in the cache model's spelling. -/
theorem flagSet_m2Of_eq (mem input : ByteArray) (n : Nat) (flag : UInt256) :
    RootE3Phase.flagSet (CycleSubmission.Global.Fast.Shift.m2Of mem input n) flag =
      Exp.storeWord (preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory) 1760 flag :=
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
def phaseBlocks : PhaseFallthroughRun.PhaseBlocks CycleSubmission.Artifact.artifact .Osaka where
  exitHead := by
    intro b
    cases b
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2342 2 3035 (PhaseFallthroughRun.exitHeadProgram false)
        (by change 2342 + 2 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 2342 + 2 ≤ 8440 from by decide))
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8400 1 10939 (PhaseFallthroughRun.exitHeadProgram true)
        (by change 8400 + 1 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 8400 + 1 ≤ 8440 from by decide))
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
  guard := by
    intro b
    cases b
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2344 4 3037 (PhaseFallthroughRun.phaseGuardProgram false)
        (by change 2344 + 4 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 2344 + 4 ≤ 8440 from by decide))
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8401 4 10940 (PhaseFallthroughRun.phaseGuardProgram true)
        (by change 8401 + 4 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 8401 + 4 ≤ 8440 from by decide))
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
  cleanup := by
    intro b
    cases b
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2348 19 3046 (PhaseFallthroughRun.cleanupProgram)
        (by change 2348 + 19 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 2348 + 19 ≤ 8440 from by decide))
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8405 19 10948 (PhaseFallthroughRun.cleanupProgram)
        (by change 8405 + 19 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 8405 + 19 ≤ 8440 from by decide))
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
  commonHead := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8425 1 10971 PhaseFallthroughRun.commonHeadProgram
      (by change 8425 + 1 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 8425 + 1 ≤ 8440 from by decide))
      (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
      (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
      (by decide)
  switch := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8426 14 10972 PhaseFallthroughRun.phaseSwitchProgram
      (by change 8426 + 14 ≤ CycleSubmission.Artifact.instructions.length; simpa only [CycleSubmission.Artifact.instructionCount] using (show 8426 + 14 ≤ 8440 from by decide))
      (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
      (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
      (by decide)

theorem jumpDestCommonSwitch : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10971 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8425
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

def doneState (b : Bool) (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  if b then CycleSubmission.Global.Fast.Shift.csubExit4State z s mem n bsize esize msize
  else CycleSubmission.Global.Fast.Shift.shiftDoneState z s mem n bsize esize msize

theorem doneFrame_eq (b : Bool) (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    doneState b z s mem n bsize esize msize =
      PhaseFallthroughRun.frame s mem (PhaseFallthroughRun.exitPC b)
        (UInt256.ofNat 0 :: CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize ++ Exp.outer n bsize esize msize) := by
  cases b <;> rfl

def switchVariant (b : Bool) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (e : CycleSubmission.Global.Fast.Shift.Env s) (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 1) :
    GasSteps (doneState b (UInt256.ofNat 0) s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 12) s (RootE3Phase.phaseSwitch mem n) n bsize esize msize (n / 4)) := by
  have hd : Decode.isValidJumpDest s.executionEnv.code 10971 = true := by
    rw [e.code]; exact jumpDestCommonSwitch
  have hh : Decode.isValidJumpDest s.executionEnv.code (CycleSubmission.Global.Fast.Shift.headPC n) = true := by
    rw [e.code]; exact CycleSubmission.Global.Fast.Shift.jumpDestHead n
  let slots := CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize ++ Exp.outer n bsize esize msize
  have hs : slots.length ≤ 1000 := by simp [slots, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer]
  have hExit := (phaseBlocks.exitHead b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (PhaseFallthroughRun.run_exitHead b s mem (UInt256.ofNat 0) slots hs)
  have hGuard := (phaseBlocks.guard b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (PhaseFallthroughRun.run_phaseGuardOne s mem b (PhaseFallthroughRun.guardPC b) slots hs e.act hflag hd)
  have hHead := phaseBlocks.commonHead.steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (PhaseFallthroughRun.run_commonHead s mem slots hs)
  have hSwitch := phaseBlocks.switch.steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (PhaseFallthroughRun.run_phaseSwitch s mem n bsize esize msize slots hn hbs hs e.act rfl hh)
  exact (hExit.cast (doneFrame_eq b (UInt256.ofNat 0) s mem n bsize esize msize).symm rfl).trans
    ((hGuard.trans (hHead.trans hSwitch)).cast rfl
      (switchEnd_eq s mem n bsize esize msize (by omega) (by omega)))

def tailVariant (b : Bool) (s : State) (mem : ByteArray) (n bsize esize msize d target : Nat)
    (e : CycleSubmission.Global.Fast.Shift.Env s) (htarget : 2284 + d = target) (hlt : target < 2^256)
    (hdest : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode target = true)
    (hflag : MachineState.readWord mem 1760 = UInt256.ofNat 0) :
    GasSteps (doneState b (UInt256.ofNat d) s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.frameState s mem target n bsize esize msize) := by
  have hd : Decode.isValidJumpDest s.executionEnv.code 10971 = true := by
    rw [e.code]; exact jumpDestCommonSwitch
  let slots := CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat d) mem n bsize esize ++ Exp.outer n bsize esize msize
  have hs : slots.length ≤ 1000 := by simp [slots, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer]
  have hExit := (phaseBlocks.exitHead b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (PhaseFallthroughRun.run_exitHead b s mem (UInt256.ofNat 0) slots hs)
  have hc : PhaseFallthroughRun.guardPC b + (PhaseFallthroughRun.guardWidth b).val + 6 = PhaseFallthroughRun.cleanupPC b := by cases b <;> rfl
  have guardRun : WindowNibbleKernel.runInstructions (PhaseFallthroughRun.phaseGuardProgram b)
      (PhaseFallthroughRun.frame s mem (PhaseFallthroughRun.guardPC b) slots) =
      some (PhaseFallthroughRun.frame s mem (PhaseFallthroughRun.cleanupPC b) slots) := by
    simpa only [hc] using PhaseFallthroughRun.run_phaseGuardZero s mem b
      (PhaseFallthroughRun.guardPC b) slots hs e.act hflag hd
  have hGuard := (phaseBlocks.guard b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl guardRun
  let front := (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat d) mem n bsize esize).take 16
  have hlen : front.length = 16 := by simp [front, CycleSubmission.Global.Fast.Shift.entrySlots]
  have hrest : (Exp.outer n bsize esize msize).length ≤ 1000 := by simp [Exp.outer]
  have ht : Decode.isValidJumpDest s.executionEnv.code target = true := by rw [e.code]; exact hdest
  have cleanupRun : WindowNibbleKernel.runInstructions PhaseFallthroughRun.cleanupProgram
      (PhaseFallthroughRun.frame s mem (PhaseFallthroughRun.cleanupPC b) slots) =
      some (PhaseFallthroughRun.frame s mem target (Exp.outer n bsize esize msize)) := by
    change WindowNibbleKernel.runInstructions PhaseFallthroughRun.cleanupProgram
      (PhaseFallthroughRun.frame s mem (PhaseFallthroughRun.cleanupPC b)
        (front ++ UInt256.ofNat d :: Exp.outer n bsize esize msize)) = _
    exact PhaseFallthroughRun.run_cleanup s mem (PhaseFallthroughRun.cleanupPC b) d target
      front (Exp.outer n bsize esize msize) hlen hrest htarget hlt ht
  have hCleanup := (phaseBlocks.cleanup b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl cleanupRun
  exact (hExit.cast (doneFrame_eq b (UInt256.ofNat d) s mem n bsize esize msize).symm rfl).trans
    ((hGuard.trans hCleanup).cast rfl rfl)

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
      exact (first.trans (second.trans third)).cast rfl
        (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 0) s m n bsize esize msize n)
          (flagSet_m2Of_eq mem input n (UInt256.ofNat 0)).symm)
    · have third := CycleSubmission.Global.Fast.Shift.gasSteps_prologue s (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n bsize esize msize
        (by omega) hn8 e hfast hes1 hm1ml hm1n0 hm1d
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
    exact (first.trans (second.trans third)).cast rfl
      (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 0) s m n bsize esize msize (n / 2))
        (prologue_e3_end_eq mem input n).symm)
  · intro hsize isInline phaseMem hflag
    cases isInline
    · exact switchVariant false s phaseMem n bsize esize msize e hsize hmatch.1 hflag
    · exact switchVariant true s phaseMem n bsize esize msize e hsize hmatch.1 hflag
  · intro isInline phaseMem hflag _hs32
    cases isInline
    · exact (tailVariant false s phaseMem n bsize esize msize 0 2284 e rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest3412
        hflag).cast rfl (frameState_bdone_eq s phaseMem n bsize esize msize)
    · exact (tailVariant true s phaseMem n bsize esize msize 0 2284 e rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest3412
        hflag).cast rfl (frameState_bdone_eq s phaseMem n bsize esize msize)
  · intro isInline phaseMem hflag
    cases isInline
    · exact tailVariant false s phaseMem n bsize esize msize 12 2296 e rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest2471 hflag
    · exact tailVariant true s phaseMem n bsize esize msize 12 2296 e rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest2471 hflag


end CycleSubmission.Global.RootE3Bindings

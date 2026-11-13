import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
import Challenge.Modexp.Submission.Proofs.CycleGlobal.GatePrefix
import Challenge.Modexp.Submission.Proofs.CycleGlobal.StackPhaseRun
import Challenge.Modexp.Submission.Proofs.CycleGlobal.StackPhaseMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RootE3Trace
import Challenge.Modexp.Submission.Proofs.Fast.RootE3Guard
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

/-- The phase switch (copy `32 n` bytes 2112 -> 256)
touches none of the eleven frame words the riding slots read. -/
theorem phaseSwitch_entrySlots (z : UInt256) (mem : ByteArray) (n bsize esize : Nat)
    (hn8 : n ≤ 8) :
    CycleSubmission.Global.Fast.Shift.entrySlots z (CycleSubmission.Global.DirectCopy.memory mem n) n bsize esize =
      CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize := by
  unfold CycleSubmission.Global.Fast.Shift.entrySlots CycleSubmission.Global.Fast.Shift.headWord CycleSubmission.Global.Fast.Shift.loopPC
    CycleSubmission.Global.Fast.Shift.aprevSlot CycleSubmission.Global.Fast.Shift.hdSlot
  rw [CycleSubmission.Global.DirectCopy.readWord mem n 1312  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1344  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1376  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1408  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1440  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1472  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1504  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1632  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1664  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1568  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 1536  (Or.inr (by omega)),
    CycleSubmission.Global.DirectCopy.readWord mem n 32  (Or.inl (by omega))]

/-- The done stub lands on the fixed-exponent dispatcher entry. -/
theorem frameState_bdone_eq (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    CycleSubmission.Global.SlimFrames.frameState s mem 2306 n bsize esize msize =
      CycleSubmission.Global.GateRaw.entryState s mem n bsize esize msize :=
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

theorem prologue_e3_end_eq (mem input : ByteArray) (n : Nat) :
    CycleSubmission.Global.StackPhaseMath.e3Prepared mem input n =
      preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory := rfl

theorem m2Of_preMem_eq (mem input : ByteArray) (n : Nat) :
    (CycleSubmission.Global.Fast.Shift.m2Of mem input n) =
      preMem (negStep (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n n).memory := rfl

/-- Word-sized naturals are equal when their embedded words are. -/
private theorem nat_eq_of_word {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : UInt256.ofNat a = UInt256.ofNat b) : a = b := by
  have h' := congrArg UInt256.toNat h
  rwa [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- Bind the direct continuation exits and common copy routine.
The switch installs continuation 2298, copies the accumulator, and resumes the loop. -/
def phaseBlocks : StackPhaseRun.PhaseBlocks CycleSubmission.Artifact.artifact .Osaka where
  exitHead := by
    intro b
    cases b
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2358 2 3048 (StackPhaseRun.headProgram false)
        (by change 2358+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8422 1 10933 (StackPhaseRun.headProgram true)
        (by change 8422+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
  transfer := by
    intro b
    cases b
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2360 2 3050 (StackPhaseRun.transferProgram)
        (by change 2360+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
    · exact WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8423 2 10934 (StackPhaseRun.transferProgram)
        (by change 8423+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
  commonHead := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3024 1 3927 (StackPhaseRun.commonHeadProgram)
        (by change 3024+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)
  switch := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3025 12 3928 (StackPhaseRun.phaseSwitchProgram)
        (by change 3025+12 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount] <;> decide)
        (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
        (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
        (by decide)

theorem jumpDestCommonSwitch : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3927 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 3024
    (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

def doneState (b : Bool) (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  if b then CycleSubmission.Global.Fast.Shift.csubExit4State z s mem n bsize esize msize
  else CycleSubmission.Global.Fast.Shift.shiftDoneState z s mem n bsize esize msize

theorem done_eq (b : Bool) (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) :
    doneState b z s mem n bsize esize msize =
      StackPhaseRun.frame s mem (StackPhaseRun.exitPC b)
        (UInt256.ofNat 0 :: CycleSubmission.Global.Fast.Shift.entrySlots z mem n bsize esize ++
          Exp.outer n bsize esize msize) := by
  cases b <;> rfl

theorem switchEnd_eq (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn8 : n ≤ 8) :
    StackPhaseRun.frame s (StackPhaseRun.phaseSwitchMemory mem n) (CycleSubmission.Global.Fast.Shift.loopPC mem n)
        (UInt256.ofNat (n / 4) :: CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 2298) mem n bsize esize ++
          Exp.outer n bsize esize msize) =
      CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 2298)
        s
        (CycleSubmission.Global.DirectCopy.memory mem n) n bsize esize msize (n / 4) := by
  have hslots := phaseSwitch_entrySlots (UInt256.ofNat 2298) mem n bsize esize hn8
  unfold CycleSubmission.Global.Fast.Shift.shiftLoopState CycleSubmission.Global.Fast.Shift.slotKState StackPhaseRun.frame

  rw [hslots]
  have hpc : CycleSubmission.Global.Fast.Shift.loopPC
      (CycleSubmission.Global.DirectCopy.memory mem n) n =
      CycleSubmission.Global.Fast.Shift.loopPC mem n := by
    unfold CycleSubmission.Global.Fast.Shift.loopPC
    rw [CycleSubmission.Global.DirectCopy.readWord mem n 1536
       (Or.inr (by omega))]
  rw [hpc]
  rfl

def switchVariant (b : Bool) (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (e : CycleSubmission.Global.Fast.Shift.Env s) (hn : n = 4 ∨ n = 8) (hbs : bsize = 32 * n) :
    GasSteps (doneState b (UInt256.ofNat 3927) s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 2298)
        s
        (CycleSubmission.Global.DirectCopy.memory mem n) n bsize esize msize (n / 4)) := by
  have hd : Decode.isValidJumpDest s.executionEnv.code 3927 = true := by
    rw [e.code]; exact jumpDestCommonSwitch
  have hh : Decode.isValidJumpDest s.executionEnv.code (CycleSubmission.Global.Fast.Shift.loopPC mem n) = true := by
    rw [e.code]; exact CycleSubmission.Global.Fast.Shift.jumpDestLoop mem n
  let slots := StackPhaseRun.transferSlots (UInt256.ofNat 3927) mem n bsize esize msize
  have hs : slots.length ≤ 1000 := by simp [slots, StackPhaseRun.transferSlots, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer]
  have hExit := (phaseBlocks.exitHead b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (StackPhaseRun.run_head b s mem (UInt256.ofNat 3927) n bsize esize msize)
  have hTransfer := (phaseBlocks.transfer b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (StackPhaseRun.run_transfer s mem (StackPhaseRun.transferPC b) 3927 (UInt256.ofNat 3927)
      n bsize esize msize (by decide) (by decide) hd)
  have hHead := phaseBlocks.commonHead.steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (StackPhaseRun.run_commonHead s mem slots hs)
  have hSwitch := phaseBlocks.switch.steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (StackPhaseRun.run_phaseSwitch s mem n bsize esize msize hn hbs e.act hh)
  exact (hExit.cast (done_eq b (UInt256.ofNat 3927) s mem n bsize esize msize).symm rfl).trans
    ((hTransfer.trans (hHead.trans hSwitch)).cast rfl (switchEnd_eq s mem n bsize esize msize (by omega)))

def tailVariant (b : Bool) (s : State) (mem : ByteArray) (n bsize esize msize d target : Nat)
    (e : CycleSubmission.Global.Fast.Shift.Env s)
    (hbs : bsize = 32 * n) (hms : msize = 32 * n)
    (hE : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat esize) (htarget : d = target) (hlt : target < 2^256)
    (hdest : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode target = true) :
    GasSteps (doneState b (UInt256.ofNat d)
        s mem n bsize esize msize)
      (CycleSubmission.Global.SlimFrames.frameState s mem target n bsize esize msize) := by
  have ht : Decode.isValidJumpDest s.executionEnv.code target = true := by rw [e.code]; exact hdest
  have hExit := (phaseBlocks.exitHead b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (StackPhaseRun.run_head b s mem (UInt256.ofNat d) n bsize esize msize)
  have hTransfer := (phaseBlocks.transfer b).steps (CycleSubmission.Global.Fast.Shift.bindingEnv e) rfl
    (StackPhaseRun.run_transfer s mem (StackPhaseRun.transferPC b) target (UInt256.ofNat d)
      n bsize esize msize (by rw [htarget]) hlt ht)
  exact (hExit.cast (done_eq b (UInt256.ofNat d) s mem n bsize esize msize).symm rfl).trans
    (hTransfer.cast rfl rfl)

/-- All concrete v4 caller certificates, with no whole-loop or whole-route premise. -/
def build (s : State) (mem input : ByteArray) (n bsize esize msize minv : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (e : CycleSubmission.Global.Fast.Shift.Env s) (hdata : s.executionEnv.calldata = input)
    (hfull : msize = 32 * n) (hesize : esize = Challenge.Modexp.exponentSize input)
    (hframe : Exp.Frame mem n bsize 0)
    (hmatch : FullBase.Matches mem n bsize) (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hfast : n = 4 ∨ n = 8)
    (hn0odd : (MachineState.readWord mem (32 * n - 32)).toNat % 2 = 1) :
    RootE3Trace.TraceBindings s mem input n bsize esize msize := by
  have hE : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat esize := by
    rw [hdata, hesize]
    rfl
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
        (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 2306) s m n bsize esize msize n)
          (m2Of_preMem_eq mem input n).symm)
    · have third := CycleSubmission.Global.Fast.Shift.gasSteps_prologue s (CycleSubmission.Global.Fast.Shift.m1Of mem input n) n bsize esize msize
        (by omega) hn8 e hfast hes1 hm1ml hm1n0 hm1d
      exact (first.trans (second.trans third)).cast rfl
        (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 2306) s m n bsize esize msize n)
          (m2Of_preMem_eq mem input n).symm)
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
      (congrArg (fun m => CycleSubmission.Global.Fast.Shift.shiftLoopState (UInt256.ofNat 3927) s m n bsize esize msize (n / 2))
        (prologue_e3_end_eq mem input n).symm)
  · intro hsize isInline phaseMem
    cases isInline
    · exact switchVariant false s phaseMem n bsize esize msize e hsize hmatch.1
    · exact switchVariant true s phaseMem n bsize esize msize e hsize hmatch.1
  · intro isInline phaseMem _hs32
    cases isInline
    · exact (tailVariant false s phaseMem n bsize esize msize 2306 2306 e hmatch.1 hfull hE rfl (by norm_num) CycleSubmission.Global.GatePrefix.jumpDestGate).cast rfl (frameState_bdone_eq s phaseMem n bsize esize msize)
    · exact (tailVariant true s phaseMem n bsize esize msize 2306 2306 e hmatch.1 hfull hE rfl (by norm_num) CycleSubmission.Global.GatePrefix.jumpDestGate).cast rfl (frameState_bdone_eq s phaseMem n bsize esize msize)
  · intro isInline phaseMem
    cases isInline
    · exact tailVariant false s phaseMem n bsize esize msize 2298 2298 e hmatch.1 hfull hE rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest2471
    · exact tailVariant true s phaseMem n bsize esize msize 2298 2298 e hmatch.1 hfull hE rfl (by norm_num) CycleSubmission.Global.Fast.jumpDest2471


end CycleSubmission.Global.RootE3Bindings

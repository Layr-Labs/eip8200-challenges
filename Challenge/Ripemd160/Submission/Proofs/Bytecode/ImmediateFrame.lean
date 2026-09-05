import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateWrapper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionTailComposition

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# H09 frame proofs

This module proves only the H09 frame around the existing schedule, copy, round,
and combination certificates.  The schedule return address is H09-specific;
its memory and active-word carrier is normalized to the existing compression
trace before the first immediate wrapper.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFrame

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def prologuePath : List Located :=
  [⟨979, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨980, .push ⟨2, by decide⟩ (UInt256.ofNat 0x72f), by rfl, by decide⟩,
   ⟨981, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨982, .push ⟨2, by decide⟩ (UInt256.ofNat 0x236), by rfl, by decide⟩,
   ⟨983, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def prologueCopiesPath : List Located :=
  [⟨984, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨985, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨986, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨987, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨988, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨989, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨990, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨991, .push ⟨2, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨992, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨993, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨994, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨995, .push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨996, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩]

def epiloguePath : List Located :=
  [⟨563, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨564, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem prologuePC (j : Nat)
    (hlo : 979 ≤ j) (hhi : j ≤ 984) :
    Artifact.submissionArtifact.instructionPC j =
      [0x726, 0x727, 0x72a, 0x72b, 0x72e, 0x72f][j - 979]! := by
  interval_cases j <;> rfl

@[simp] private theorem pc979 : Artifact.submissionArtifact.instructionPC 979 = 0x726 := by decide
@[simp] private theorem pc980 : Artifact.submissionArtifact.instructionPC 980 = 0x727 := by decide
@[simp] private theorem pc981 : Artifact.submissionArtifact.instructionPC 981 = 0x72a := by decide
@[simp] private theorem pc982 : Artifact.submissionArtifact.instructionPC 982 = 0x72b := by decide
@[simp] private theorem pc983 : Artifact.submissionArtifact.instructionPC 983 = 0x72e := by decide

@[simp] private theorem copiesPC (j : Nat)
    (hlo : 984 ≤ j) (hhi : j ≤ 997) :
    Artifact.submissionArtifact.instructionPC j =
      [0x72f, 0x730, 0x732, 0x734, 0x736, 0x737, 0x739,
       0x73b, 0x73e, 0x73f, 0x741, 0x743, 0x746, 0x747][j - 984]! := by
  interval_cases j <;> rfl

@[simp] private theorem pc984 : Artifact.submissionArtifact.instructionPC 984 = 0x72f := by decide
@[simp] private theorem pc985 : Artifact.submissionArtifact.instructionPC 985 = 0x730 := by decide
@[simp] private theorem pc986 : Artifact.submissionArtifact.instructionPC 986 = 0x732 := by decide
@[simp] private theorem pc987 : Artifact.submissionArtifact.instructionPC 987 = 0x734 := by decide
@[simp] private theorem pc988 : Artifact.submissionArtifact.instructionPC 988 = 0x736 := by decide
@[simp] private theorem pc989 : Artifact.submissionArtifact.instructionPC 989 = 0x737 := by decide
@[simp] private theorem pc990 : Artifact.submissionArtifact.instructionPC 990 = 0x739 := by decide
@[simp] private theorem pc991 : Artifact.submissionArtifact.instructionPC 991 = 0x73b := by decide
@[simp] private theorem pc992 : Artifact.submissionArtifact.instructionPC 992 = 0x73e := by decide
@[simp] private theorem pc993 : Artifact.submissionArtifact.instructionPC 993 = 0x73f := by decide
@[simp] private theorem pc994 : Artifact.submissionArtifact.instructionPC 994 = 0x741 := by decide
@[simp] private theorem pc995 : Artifact.submissionArtifact.instructionPC 995 = 0x743 := by decide
@[simp] private theorem pc996 : Artifact.submissionArtifact.instructionPC 996 = 0x746 := by decide

@[simp] private theorem epiloguePC (j : Nat)
    (hlo : 563 ≤ j) (hhi : j ≤ 565) :
    Artifact.submissionArtifact.instructionPC j =
      [804, 805, 806][j - 563]! := by
  interval_cases j <;> rfl

@[simp] private theorem pc563 : Artifact.submissionArtifact.instructionPC 563 = 804 := by decide
@[simp] private theorem pc564 : Artifact.submissionArtifact.instructionPC 564 = 805 := by decide

@[simp] private theorem valid236 :
    Decode.isValidJumpDest submissionBytecode 0x236 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 413 (by rfl)

@[simp] private theorem valid72f :
    Decode.isValidJumpDest submissionBytecode 0x72f = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 984 (by rfl)

def prologueEntry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0x726
    stack := [messageOffset, outerReturn] ++ rest }

/-- The H09 schedule carrier.  Only the return destination differs from the
existing `CompressionTrace.scheduledState`; both use the same outer stack. -/
def scheduledStateH09 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  Schedule.loopState s messageOffset (UInt256.ofNat 0x72f)
    (messageOffset :: outerReturn :: rest) 16

def scheduleReturnedH09 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  Schedule.scheduleReturned (scheduledStateH09 s messageOffset outerReturn rest)
    (UInt256.ofNat 0x72f) (messageOffset :: outerReturn :: rest)

def firstWrapperEntry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { CompressionTrace.copiedWorkingState
      (scheduleReturnedH09 s messageOffset outerReturn rest) with
    pc := UInt256.ofNat 0x747
    stack := [messageOffset, outerReturn] ++ rest }

def normalizedLeftInitialState (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) : State :=
  { CompressionTrace.leftInitialState s messageOffset outerReturn rest with
    pc := UInt256.ofNat 0x747
    stack := [messageOffset, outerReturn] ++ rest }

def epilogueEntry (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0x324
    stack := [0, messageOffset, outerReturn] ++ rest }

def epilogueReturned (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  CompressionTailTrace.combinationReturned s messageOffset outerReturn rest

private theorem scheduleLoop_memory_returnDest (s : State)
    (messageOffset returnDest₁ returnDest₂ : UInt256)
    (rest : List UInt256) : ∀ i,
      (Schedule.loopState s messageOffset returnDest₁ rest i).memory =
      (Schedule.loopState s messageOffset returnDest₂ rest i).memory := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [Schedule.loopState, Schedule.afterIteration,
        Schedule.afterStore, Schedule.afterRead,
        State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, ih]

private theorem scheduleLoop_activeWords_returnDest (s : State)
    (messageOffset returnDest₁ returnDest₂ : UInt256)
    (rest : List UInt256) : ∀ i,
      (Schedule.loopState s messageOffset returnDest₁ rest i).activeWords =
      (Schedule.loopState s messageOffset returnDest₂ rest i).activeWords := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [Schedule.loopState, Schedule.afterIteration,
        Schedule.afterStore, Schedule.afterRead,
        State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, ih]

private theorem copiedWorkingState_memory_congr (s t : State)
    (hmem : s.memory = t.memory) :
    (CompressionTrace.copiedWorkingState s).memory =
      (CompressionTrace.copiedWorkingState t).memory := by
  simp [CompressionTrace.copiedWorkingState, CompressionTrace.copyRegion, hmem]

private theorem copiedWorkingState_activeWords_congr (s t : State)
    (hactive : s.activeWords = t.activeWords) :
    (CompressionTrace.copiedWorkingState s).activeWords =
      (CompressionTrace.copiedWorkingState t).activeWords := by
  simp [CompressionTrace.copiedWorkingState, CompressionTrace.copyRegion,
    State.activeWordsAfterUInt256_2, hactive]

theorem scheduledStateH09_memory_eq (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (scheduledStateH09 s messageOffset outerReturn rest).memory =
      (CompressionTrace.scheduledState s messageOffset outerReturn rest).memory := by
  simpa [scheduledStateH09, CompressionTrace.scheduledState] using
    scheduleLoop_memory_returnDest s messageOffset
      (UInt256.ofNat 0x72f) (UInt256.ofNat 0x276)
      (messageOffset :: outerReturn :: rest) 16

theorem scheduledStateH09_activeWords_eq (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (scheduledStateH09 s messageOffset outerReturn rest).activeWords =
      (CompressionTrace.scheduledState s messageOffset outerReturn rest).activeWords := by
  simpa [scheduledStateH09, CompressionTrace.scheduledState] using
    scheduleLoop_activeWords_returnDest s messageOffset
      (UInt256.ofNat 0x72f) (UInt256.ofNat 0x276)
      (messageOffset :: outerReturn :: rest) 16

theorem firstWrapperEntry_memory_eq_leftInitialState (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (firstWrapperEntry s messageOffset outerReturn rest).memory =
      (CompressionTrace.leftInitialState s messageOffset outerReturn rest).memory := by
  have hmem :
      (scheduleReturnedH09 s messageOffset outerReturn rest).memory =
        (CompressionTrace.scheduledState s messageOffset outerReturn rest).memory := by
    exact (show (scheduleReturnedH09 s messageOffset outerReturn rest).memory =
      (scheduledStateH09 s messageOffset outerReturn rest).memory by rfl).trans
      (scheduledStateH09_memory_eq s messageOffset outerReturn rest)
  have hcopy := copiedWorkingState_memory_congr
    (scheduleReturnedH09 s messageOffset outerReturn rest)
    (CompressionTrace.scheduledState s messageOffset outerReturn rest) hmem
  simpa [firstWrapperEntry, CompressionTrace.leftInitialState] using hcopy

theorem firstWrapperEntry_activeWords_eq_leftInitialState (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (firstWrapperEntry s messageOffset outerReturn rest).activeWords =
      (CompressionTrace.leftInitialState s messageOffset outerReturn rest).activeWords := by
  have hactive :
      (scheduleReturnedH09 s messageOffset outerReturn rest).activeWords =
        (CompressionTrace.scheduledState s messageOffset outerReturn rest).activeWords := by
    exact (show (scheduleReturnedH09 s messageOffset outerReturn rest).activeWords =
      (scheduledStateH09 s messageOffset outerReturn rest).activeWords by rfl).trans
      (scheduledStateH09_activeWords_eq s messageOffset outerReturn rest)
  have hcopy := copiedWorkingState_activeWords_congr
    (scheduleReturnedH09 s messageOffset outerReturn rest)
    (CompressionTrace.scheduledState s messageOffset outerReturn rest) hactive
  simpa [firstWrapperEntry, CompressionTrace.leftInitialState] using hcopy

private theorem scheduleLoop_static_returnDest (s : State)
    (messageOffset returnDest₁ returnDest₂ : UInt256)
    (rest : List UInt256) : ∀ i,
      (Schedule.loopState s messageOffset returnDest₁ rest i).gasAvailable =
          (Schedule.loopState s messageOffset returnDest₂ rest i).gasAvailable ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).returnData =
          (Schedule.loopState s messageOffset returnDest₂ rest i).returnData ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).hReturn =
          (Schedule.loopState s messageOffset returnDest₂ rest i).hReturn ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).accountMap =
          (Schedule.loopState s messageOffset returnDest₂ rest i).accountMap ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).substate =
          (Schedule.loopState s messageOffset returnDest₂ rest i).substate ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).executionEnv =
          (Schedule.loopState s messageOffset returnDest₂ rest i).executionEnv ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).execLength =
          (Schedule.loopState s messageOffset returnDest₂ rest i).execLength ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).halt =
          (Schedule.loopState s messageOffset returnDest₂ rest i).halt ∧
      (Schedule.loopState s messageOffset returnDest₁ rest i).callStack =
          (Schedule.loopState s messageOffset returnDest₂ rest i).callStack := by
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ i ih =>
      simpa only [Schedule.loopState, Schedule.afterIteration,
        Schedule.afterStore, Schedule.afterRead] using ih

private theorem copiedWorkingState_static_fields (s : State) :
    (CompressionTrace.copiedWorkingState s).gasAvailable = s.gasAvailable ∧
    (CompressionTrace.copiedWorkingState s).returnData = s.returnData ∧
    (CompressionTrace.copiedWorkingState s).hReturn = s.hReturn ∧
    (CompressionTrace.copiedWorkingState s).accountMap = s.accountMap ∧
    (CompressionTrace.copiedWorkingState s).substate = s.substate ∧
    (CompressionTrace.copiedWorkingState s).executionEnv = s.executionEnv ∧
    (CompressionTrace.copiedWorkingState s).execLength = s.execLength ∧
    (CompressionTrace.copiedWorkingState s).halt = s.halt ∧
    (CompressionTrace.copiedWorkingState s).callStack = s.callStack := by
  simp [CompressionTrace.copiedWorkingState, CompressionTrace.copyRegion]

private theorem sharedState_eq_of_fields {a b : State}
    (hgas : a.gasAvailable = b.gasAvailable)
    (hactive : a.activeWords = b.activeWords)
    (hmem : a.memory = b.memory)
    (hreturnData : a.returnData = b.returnData)
    (hhReturn : a.hReturn = b.hReturn)
    (haccountMap : a.accountMap = b.accountMap)
    (hsubstate : a.substate = b.substate)
    (henv : a.executionEnv = b.executionEnv) :
    a.toSharedState = b.toSharedState := by
  cases a with
  | mk aShared ap ast ae ah ac =>
    cases b with
    | mk bShared bp bst be bh bc =>
      cases aShared with
      | mk aMachine aam ass aenv =>
        cases bShared with
        | mk bMachine bam bss benv =>
          cases aMachine
          cases bMachine
          simp_all only [SharedState.mk.injEq, MachineState.mk.injEq]

private theorem overridePCStack_eq {a b : State} (pc : UInt256)
    (stack : List UInt256) (hshared : a.toSharedState = b.toSharedState)
    (hexecLength : a.execLength = b.execLength)
    (hhalt : a.halt = b.halt) (hcallStack : a.callStack = b.callStack) :
    {a with pc := pc, stack := stack} = {b with pc := pc, stack := stack} := by
  cases a
  cases b
  simp_all only [State.mk.injEq]

theorem firstWrapperEntry_normalized (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    firstWrapperEntry s messageOffset outerReturn rest =
      normalizedLeftInitialState s messageOffset outerReturn rest := by
  let q := scheduleReturnedH09 s messageOffset outerReturn rest
  let t := CompressionTrace.scheduledState s messageOffset outerReturn rest
  have hstatic := scheduleLoop_static_returnDest s messageOffset
    (UInt256.ofNat 0x72f) (UInt256.ofNat 0x276)
    (messageOffset :: outerReturn :: rest) 16
  have hstatic' :
      q.gasAvailable = t.gasAvailable ∧
      q.returnData = t.returnData ∧ q.hReturn = t.hReturn ∧
      q.accountMap = t.accountMap ∧ q.substate = t.substate ∧
      q.executionEnv = t.executionEnv ∧ q.execLength = t.execLength ∧
      q.halt = t.halt ∧ q.callStack = t.callStack := by
    simpa only [q, t, scheduleReturnedH09, Schedule.scheduleReturned,
      scheduledStateH09, CompressionTrace.scheduledState] using hstatic
  have hmem : q.memory = t.memory := by
    exact (show q.memory = (scheduledStateH09 s messageOffset outerReturn rest).memory by
      rfl).trans (scheduledStateH09_memory_eq s messageOffset outerReturn rest)
  have hactive : q.activeWords = t.activeWords := by
    exact (show q.activeWords =
      (scheduledStateH09 s messageOffset outerReturn rest).activeWords by
      rfl).trans (scheduledStateH09_activeWords_eq s messageOffset outerReturn rest)
  have hcopyStaticQ := copiedWorkingState_static_fields q
  have hcopyStaticT := copiedWorkingState_static_fields t
  have hcopyMem := copiedWorkingState_memory_congr q t hmem
  have hcopyActive := copiedWorkingState_activeWords_congr q t hactive
  have hshared :
      (CompressionTrace.copiedWorkingState q).toSharedState =
        (CompressionTrace.copiedWorkingState t).toSharedState := by
    apply sharedState_eq_of_fields
    · exact hcopyStaticQ.1.trans (hstatic'.1.trans hcopyStaticT.1.symm)
    · exact hcopyActive
    · exact hcopyMem
    · exact hcopyStaticQ.2.1.trans (hstatic'.2.1.trans hcopyStaticT.2.1.symm)
    · exact hcopyStaticQ.2.2.1.trans (hstatic'.2.2.1.trans hcopyStaticT.2.2.1.symm)
    · exact hcopyStaticQ.2.2.2.1.trans
        (hstatic'.2.2.2.1.trans hcopyStaticT.2.2.2.1.symm)
    · exact hcopyStaticQ.2.2.2.2.1.trans
        (hstatic'.2.2.2.2.1.trans hcopyStaticT.2.2.2.2.1.symm)
    · exact hcopyStaticQ.2.2.2.2.2.1.trans
        (hstatic'.2.2.2.2.2.1.trans hcopyStaticT.2.2.2.2.2.1.symm)
  have hEq := overridePCStack_eq (a := CompressionTrace.copiedWorkingState q)
    (b := CompressionTrace.copiedWorkingState t) (UInt256.ofNat 0x747)
    ([messageOffset, outerReturn] ++ rest) hshared
    (hcopyStaticQ.2.2.2.2.2.2.1.trans
      (hstatic'.2.2.2.2.2.2.1.trans
        hcopyStaticT.2.2.2.2.2.2.1.symm))
    (hcopyStaticQ.2.2.2.2.2.2.2.1.trans
      (hstatic'.2.2.2.2.2.2.2.1.trans
        hcopyStaticT.2.2.2.2.2.2.2.1.symm))
    (hcopyStaticQ.2.2.2.2.2.2.2.2.trans
      (hstatic'.2.2.2.2.2.2.2.2.trans
        hcopyStaticT.2.2.2.2.2.2.2.2.symm))
  simpa [firstWrapperEntry, normalizedLeftInitialState, q, t,
    CompressionTrace.leftInitialState] using hEq

@[simp] theorem firstWrapperEntry_executionEnv (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (firstWrapperEntry s messageOffset outerReturn rest).executionEnv =
      s.executionEnv := by
  simp [firstWrapperEntry, scheduleReturnedH09, scheduledStateH09,
    Schedule.scheduleReturned,
    CompressionTrace.copiedWorkingState, CompressionTrace.copyRegion]

@[simp] theorem firstWrapperEntry_code (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (firstWrapperEntry s messageOffset outerReturn rest).executionEnv.code =
      s.executionEnv.code := by
  rw [firstWrapperEntry_executionEnv]

@[simp] theorem firstWrapperEntry_fork (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (firstWrapperEntry s messageOffset outerReturn rest).fork = s.fork := by
  rw [State.fork, firstWrapperEntry_executionEnv]

@[simp] theorem firstWrapperEntry_halt (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (firstWrapperEntry s messageOffset outerReturn rest).halt = s.halt := by
  simp [firstWrapperEntry, scheduleReturnedH09, scheduledStateH09,
    Schedule.scheduleReturned,
    CompressionTrace.copiedWorkingState, CompressionTrace.copyRegion]

private theorem scheduleLoop_callStack (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : ∀ i,
      (Schedule.loopState s messageOffset returnDest rest i).callStack = s.callStack := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [Schedule.loopState, Schedule.afterIteration,
        Schedule.afterStore, Schedule.afterRead,
        State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, ih]

@[simp] theorem firstWrapperEntry_callStack (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (firstWrapperEntry s messageOffset outerReturn rest).callStack = s.callStack := by
  simp [firstWrapperEntry, scheduleReturnedH09, scheduledStateH09,
    Schedule.scheduleReturned,
    CompressionTrace.copiedWorkingState, CompressionTrace.copyRegion,
    scheduleLoop_callStack]

@[simp] theorem epilogueEntry_executionEnv (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (epilogueEntry s messageOffset outerReturn rest).executionEnv =
      s.executionEnv := by rfl

@[simp] theorem epilogueReturned_executionEnv (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (epilogueReturned s messageOffset outerReturn rest).executionEnv =
      s.executionEnv := by
  simp [epilogueReturned, CompressionTailTrace.combinationReturned,
    CompressionTailTrace.combinationCleaned,
    CompressionTailTrace.combination4, CompressionTailTrace.touched4,
    CompressionTailTrace.touched3, CompressionTailTrace.touched2,
    CompressionTailTrace.touched1, CompressionTailTrace.touched0,
    CompressionTailTrace.touchWord]

@[simp] theorem epilogueReturned_code (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (epilogueReturned s messageOffset outerReturn rest).executionEnv.code =
      s.executionEnv.code := by
  rw [epilogueReturned_executionEnv]

@[simp] theorem epilogueReturned_fork (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (epilogueReturned s messageOffset outerReturn rest).fork = s.fork := by
  rw [State.fork, epilogueReturned_executionEnv]

@[simp] theorem epilogueReturned_halt (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (epilogueReturned s messageOffset outerReturn rest).halt = s.halt := by
  simp [epilogueReturned, CompressionTailTrace.combinationReturned,
    CompressionTailTrace.combinationCleaned,
    CompressionTailTrace.combination4, CompressionTailTrace.touched4,
    CompressionTailTrace.touched3, CompressionTailTrace.touched2,
    CompressionTailTrace.touched1, CompressionTailTrace.touched0,
    CompressionTailTrace.touchWord]

@[simp] theorem epilogueReturned_callStack (s : State)
    (messageOffset outerReturn : UInt256) (rest : List UInt256) :
    (epilogueReturned s messageOffset outerReturn rest).callStack = s.callStack := by
  simp [epilogueReturned, CompressionTailTrace.combinationReturned,
    CompressionTailTrace.combinationCleaned,
    CompressionTailTrace.combination4, CompressionTailTrace.touched4,
    CompressionTailTrace.touched3, CompressionTailTrace.touched2,
    CompressionTailTrace.touched1, CompressionTailTrace.touched0,
    CompressionTailTrace.touchWord]

set_option linter.unusedSimpArgs false in
theorem run_prologue (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock prologuePath
      (prologueEntry s messageOffset outerReturn rest) =
        some (Schedule.scheduleEntry s messageOffset (UInt256.ofNat 0x72f)
          (messageOffset :: outerReturn :: rest)) := by
  have hc0 : ([messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc1 : ([UInt256.ofNat 0x72f, messageOffset, outerReturn] ++ rest).length <
      1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc2 : ([messageOffset, UInt256.ofNat 0x72f, messageOffset,
      outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc3 : ([UInt256.ofNat 0x236, messageOffset, UInt256.ofNat 0x72f,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hc4 : ([UInt256.ofNat 0x236, messageOffset, UInt256.ofNat 0x72f,
      messageOffset, outerReturn] ++ rest).length < 1024 := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hstack ⊢
    omega
  have hcap (m : Nat) (hm : m ≤ 5) : rest.length + m < 1024 := by omega
  have hpc0 : ([1830, 1831, 1834, 1835, 1838, 1839][0]?).getD 0 =
      (1830 : Nat) := by decide
  have hpc1 : ([1831, 1834, 1835, 1838, 1839][0]?).getD 0 =
      (1831 : Nat) := by decide
  have hpc2 : ([1834, 1835, 1838, 1839][0]?).getD 0 =
      (1834 : Nat) := by decide
  have hpc3 : ([1835, 1838, 1839][0]?).getD 0 =
      (1835 : Nat) := by decide
  have hpc4 : ([1838, 1839][0]?).getD 0 =
      (1838 : Nat) := by decide
  have hdup : (messageOffset :: outerReturn :: rest)[0]? =
      some messageOffset := by rfl
  simp (config := { maxSteps := 100000 }) (discharger := omega)
    [prologuePath, prologueEntry,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hrun, hcode, valid236, prologuePC, pc979, pc980, pc981, pc982, pc983,
      hc0, hc1, hc2, hc3, hc4, hcap, Nat.add_assoc,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      Schedule.scheduleEntry, List.getElem?_eq_getElem,
      hpc0, hpc1, hpc2, hpc3, hpc4, hdup]

set_option linter.unusedSimpArgs false in
theorem run_prologueCopies (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock prologueCopiesPath
      (scheduleReturnedH09 s messageOffset outerReturn rest) =
        some (firstWrapperEntry s messageOffset outerReturn rest) := by
  have hc0 : rest.length + 1 < 1024 := by omega
  have hc1 : rest.length + 2 < 1024 := by omega
  have hc2 : rest.length + 3 < 1024 := by omega
  have hc3 : rest.length + 4 < 1024 := by omega
  have hc4 : rest.length + 5 < 1024 := by omega
  have hcap (m : Nat) (hm : m ≤ 5) : rest.length + m < 1024 := by omega
  have hqrun : (scheduleReturnedH09 s messageOffset outerReturn rest).halt =
      .Running := by
    have hsched : (scheduledStateH09 s messageOffset outerReturn rest).halt = s.halt := by
      simpa only [scheduledStateH09] using
        Schedule.loopState_halt s messageOffset (UInt256.ofNat 0x72f)
          (messageOffset :: outerReturn :: rest) 16
    change (scheduledStateH09 s messageOffset outerReturn rest).halt = .Running
    rw [hsched]
    exact hrun
  have hschedRun : (scheduledStateH09 s messageOffset outerReturn rest).halt =
      .Running := by
    have hsched : (scheduledStateH09 s messageOffset outerReturn rest).halt = s.halt := by
      simpa only [scheduledStateH09] using
        Schedule.loopState_halt s messageOffset (UInt256.ofNat 0x72f)
          (messageOffset :: outerReturn :: rest) 16
    exact hsched.trans hrun
  have hpc0 : ([1839][0]?).getD 0 = (1839 : Nat) := by decide
  have hpc1 :
      ([1840, 1842, 1844, 1846, 1847, 1849, 1851, 1854, 1855,
        1857, 1859, 1862, 1863][0]?).getD 0 = (1840 : Nat) := by decide
  have hpc2 :
      ([1842, 1844, 1846, 1847, 1849, 1851, 1854, 1855,
        1857, 1859, 1862, 1863][0]?).getD 0 = (1842 : Nat) := by decide
  have hpc3 :
      ([1844, 1846, 1847, 1849, 1851, 1854, 1855, 1857,
        1859, 1862, 1863][0]?).getD 0 = (1844 : Nat) := by decide
  have hpc4 :
      ([1846, 1847, 1849, 1851, 1854, 1855, 1857, 1859,
        1862, 1863][0]?).getD 0 = (1846 : Nat) := by decide
  have hpc5 :
      ([1847, 1849, 1851, 1854, 1855, 1857, 1859, 1862, 1863][0]?).getD 0 =
        (1847 : Nat) := by decide
  have hpc6 :
      ([1849, 1851, 1854, 1855, 1857, 1859, 1862, 1863][0]?).getD 0 =
        (1849 : Nat) := by decide
  have hpc7 :
      ([1851, 1854, 1855, 1857, 1859, 1862, 1863][0]?).getD 0 =
        (1851 : Nat) := by decide
  have hpc8 :
      ([1854, 1855, 1857, 1859, 1862, 1863][0]?).getD 0 =
        (1854 : Nat) := by decide
  have hpc9 :
      ([1855, 1857, 1859, 1862, 1863][0]?).getD 0 = (1855 : Nat) := by decide
  have hpc10 :
      ([1857, 1859, 1862, 1863][0]?).getD 0 = (1857 : Nat) := by decide
  have hpc11 :
      ([1859, 1862, 1863][0]?).getD 0 = (1859 : Nat) := by decide
  have hpc12 : ([1862, 1863][0]?).getD 0 = (1862 : Nat) := by decide
  have hpc13 : ([1863][0]?).getD 0 = (1863 : Nat) := by decide
  change Challenge.EvmProof.Stepper.runLocatedBlock prologueCopiesPath
      (scheduleReturnedH09 s messageOffset outerReturn rest) =
    some ({ CompressionTrace.copiedWorkingState
      (scheduleReturnedH09 s messageOffset outerReturn rest) with
      pc := UInt256.ofNat 0x747
      stack := [messageOffset, outerReturn] ++ rest })
  simp (config := { maxSteps := 300000 }) (discharger := omega)
    [prologueCopiesPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hqrun, hschedRun, copiesPC, pc984, pc985, pc986, pc987, pc988, pc989, pc990,
      pc991, pc992, pc993, pc994, pc995, pc996,
      scheduleReturnedH09, Schedule.scheduleReturned,
      hc0, hc1, hc2, hc3, hc4, hcap,
      hpc0, hpc1, hpc2, hpc3, hpc4, hpc5, hpc6, hpc7,
      hpc8, hpc9, hpc10, hpc11, hpc12, hpc13,
      Nat.add_assoc, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      Challenge.EvmProof.Word.ofNat_add_ofNat,
      CompressionTrace.copiedWorkingState, CompressionTrace.copyRegion,
      State.activeWordsAfterUInt256_2, List.getElem?_eq_getElem]

set_option linter.unusedSimpArgs false in
theorem run_epilogue (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock epiloguePath
      (epilogueEntry s messageOffset outerReturn rest) =
        some (CompressionRightTrace.combinationEntry s messageOffset outerReturn rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [epiloguePath, epilogueEntry, CompressionRightTrace.combinationEntry,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hrun, hc3, epiloguePC, pc563, pc564, List.getElem?_eq_getElem]

def gasSteps_prologue (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (prologueEntry s messageOffset outerReturn rest)
      (firstWrapperEntry s messageOffset outerReturn rest) := by
  have gPrologue := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka prologuePath
      (s := prologueEntry s messageOffset outerReturn rest)
      (by simpa [prologueEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [prologueEntry] using hfork)
      (run_prologue s messageOffset outerReturn rest hstack hcode hrun)
      (by simpa [prologueEntry] using hrun)
      (by simpa [prologueEntry] using hnp)
  let tail := messageOffset :: outerReturn :: rest
  have htail : tail.length < 1012 := by
    simp [tail]
    omega
  have hreturn :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 0x72f).toNat = true := by
    exact valid72f
  have gSchedule := Schedule.gasSteps_schedule s messageOffset
    (UInt256.ofNat 0x72f) tail htail hcode hfork hrun hnp hreturn
  have hqcode : (scheduleReturnedH09 s messageOffset outerReturn rest).executionEnv.code =
      submissionBytecode := by
    simpa [scheduleReturnedH09, scheduledStateH09, tail,
      Schedule.scheduleReturned] using hcode
  have hqfork : (scheduleReturnedH09 s messageOffset outerReturn rest).fork =
      .Osaka := by
    simpa [scheduleReturnedH09, scheduledStateH09, tail,
      Schedule.scheduleReturned, State.fork] using hfork
  have hqrun : (scheduleReturnedH09 s messageOffset outerReturn rest).halt =
      .Running := by
    simpa [scheduleReturnedH09, scheduledStateH09, tail,
      Schedule.scheduleReturned] using hrun
  have hqnp : Precompile.isPrecompileWithConfig
      (scheduleReturnedH09 s messageOffset outerReturn rest).executionEnv.precompileConfig
      (scheduleReturnedH09 s messageOffset outerReturn rest).executionEnv.fork
      (scheduleReturnedH09 s messageOffset outerReturn rest).executionEnv.codeAddr = false := by
    simpa [scheduleReturnedH09, scheduledStateH09, tail,
      Schedule.scheduleReturned] using hnp
  have gCopies := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka prologueCopiesPath
      (s := scheduleReturnedH09 s messageOffset outerReturn rest)
      hqcode hqfork
      (run_prologueCopies s messageOffset outerReturn rest hstack hrun)
      hqrun hqnp
  exact gPrologue.trans (gSchedule.trans gCopies)

def gasSteps_epilogue (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 970)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode outerReturn.toNat = true) :
    Challenge.EvmProof.GasSteps
      (epilogueEntry s messageOffset outerReturn rest)
      (epilogueReturned s messageOffset outerReturn rest) := by
  have gFrame := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka epiloguePath
      (s := epilogueEntry s messageOffset outerReturn rest)
      (by simpa [epilogueEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [epilogueEntry] using hfork)
      (run_epilogue s messageOffset outerReturn rest hstack hrun)
      (by simpa [epilogueEntry] using hrun)
      (by simpa [epilogueEntry] using hnp)
  have gCombination := CompressionTailTrace.gasSteps_combination s
    messageOffset outerReturn rest hstack hcode hfork hrun hnp hvalid
  exact gFrame.trans gCombination

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFrame

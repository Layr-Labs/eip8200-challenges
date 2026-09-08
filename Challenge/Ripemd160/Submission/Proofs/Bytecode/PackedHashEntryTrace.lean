import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntryOps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedInitialFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Located packed hash-entry trace

This is the concrete bridge from the preprocessing endpoint at PC `784` to
the first packed round at PC `891`.  The artifact first pushes the eleven
fixed suffix words, then loads `h4, h3, h2, h1, h0` from addresses
`480, 448, 416, 384, 352`.  Each load is followed by
`DUP1; PUSH1 64; SHL; OR`, so the last load leaves `h0` on top and the
resulting nineteen words are exactly `PackedInitialFrame.initialFrame`.

The bit-level duplication is not reproved here: the only arithmetic rewrite
is the proved `PackedHashEntryOps.duplicate_lane`.  The incoming active-word
premise is explicit.  Sixteen words cover the largest load through byte 512,
so none of the five loads changes `activeWords`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntryTrace

open Challenge.Ripemd160 Challenge.EvmProof
open Challenge.EvmProof.Word
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTemplate StackRoundTrace

abbrev A := Artifact.submissionArtifact

def push1 (value : UInt256) : Instr :=
  .push ⟨1, by decide⟩ value

def push2 (value : UInt256) : Instr :=
  .push ⟨2, by decide⟩ value

def push4 (value : UInt256) : Instr :=
  .push ⟨4, by decide⟩ value

def push5 (value : UInt256) : Instr :=
  .push ⟨5, by decide⟩ value

def push12 (value : UInt256) : Instr :=
  .push ⟨12, by decide⟩ value

def op (operation : Operation) : Instr := .op operation

def dup1 : Instr := .op (.Dup ⟨0, by decide⟩)

/-- The eleven fixed words, in the exact order in which the artifact pushes
them.  Because pushes prepend, the resulting stack is `suffixStack` order. -/
def prefixTemplate : List Instr :=
  [push12 (PackedEmit.packedK 0),
   push1 (UInt256.ofNat 22), push1 (UInt256.ofNat 21),
   push1 (UInt256.ofNat 20), push1 (UInt256.ofNat 19),
   push1 (UInt256.ofNat 18), push1 (UInt256.ofNat 17),
   push5 PackedLaneRot.cMul,
   push12 PackedLaneInvariant.maskR,
   push4 PackedLaneInvariant.maskL,
   push12 PackedLaneInvariant.maskLR]

/-- Exact six-instruction duplication of one stored chaining word. -/
def hashLoadStep (address : Nat) : List Instr :=
  [push2 (UInt256.ofNat address), op .MLOAD, dup1,
   push1 (UInt256.ofNat 64), op .SHL, op .OR]

def hashLoadTemplate : List Instr :=
  hashLoadStep 480 ++ hashLoadStep 448 ++ hashLoadStep 416 ++
    hashLoadStep 384 ++ hashLoadStep 352

/-- Artifact instructions `460..500`, PCs `784..890`. -/
def hashEntryTemplate : List Instr := prefixTemplate ++ hashLoadTemplate

@[simp] theorem prefixTemplate_length : prefixTemplate.length = 11 := by
  rfl

@[simp] theorem hashLoadStep_length (address : Nat) :
    (hashLoadStep address).length = 6 := by
  rfl

@[simp] theorem hashLoadTemplate_length : hashLoadTemplate.length = 30 := by
  rfl

@[simp] theorem hashEntryTemplate_length : hashEntryTemplate.length = 41 := by
  rfl

theorem artifact_hashEntry_slice :
    (Artifact.submissionArtifact.instructions.drop 460).take 41 =
      hashEntryTemplate := by
  rfl

/-- The machine-order result of `DUP1; PUSH1 64; SHL; OR`. -/
def duplicateWord (value : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft value (UInt256.ofNat 64)) value

theorem duplicateWord_ofUInt32 (value : UInt32) :
    duplicateWord (Word.ofUInt32 value) =
      PackedHashEntry.packPair value value := by
  unfold duplicateWord
  rw [Word.lor_comm]
  exact PackedHashEntryOps.duplicate_lane value

def loadedRegs (s : State) : List UInt256 :=
  [duplicateWord (MachineState.readWord s.memory 352),
   duplicateWord (MachineState.readWord s.memory 384),
   duplicateWord (MachineState.readWord s.memory 416),
   duplicateWord (MachineState.readWord s.memory 448),
   duplicateWord (MachineState.readWord s.memory 480)]

def entryState (s : State) (startPC ret xoff xend : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := startPC, stack := [ret, xoff, xend] ++ rest }

def prefixReturned (s : State) (endPC ret xoff xend : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := PackedStepFrame.suffixStack
      (PackedInitialFrame.initialSuffix ret xoff xend) ++ rest }

def hashLoadReturned (s : State) (endPC : UInt256) (address : Nat)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := duplicateWord (MachineState.readWord s.memory address) :: rest }

def rawReturned (s : State) (endPC ret xoff xend : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := loadedRegs s ++ PackedStepFrame.suffixStack
      (PackedInitialFrame.initialSuffix ret xoff xend) ++ rest }

def frameReturned (s : State) (endPC : UInt256) (h : Compression.HashState)
    (ret xoff xend : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := PackedStepFrame.frameStack
      (PackedInitialFrame.initialFrame h ret xoff xend) ++ rest }

private theorem activeWordsAfter_eq_of_end_le (curr offset size : Nat)
    (hend : offset + size ≤ curr * 32) :
    MachineState.activeWordsAfter curr offset size = curr := by
  unfold MachineState.activeWordsAfter
  split
  · rfl
  · dsimp only
    apply Nat.max_eq_left
    have hq : (offset + size - 1) / 32 < curr :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega

private theorem activeWordsAfterUInt256_eq (s : State) (offset size : Nat)
    (hend : offset + size ≤ s.activeWords.toNat * 32) :
    s.activeWordsAfterUInt256 offset size = s.activeWords := by
  have hofNat (word : UInt256) : UInt256.ofNat word.toNat = word := by
    cases word with
    | mk value => simp [UInt256.ofNat, UInt256.toNat, UInt256.size]
  rw [State.activeWordsAfterUInt256,
    activeWordsAfter_eq_of_end_le _ _ _ hend, hofNat]

private theorem runInstrSeq_append_running
    {first second : List Instr} {s middle result : State}
    (hfirst : runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hsecond : runInstrSeq second middle = some result) :
    runInstrSeq (first ++ second) s = some result := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, runInstrSeq] at hfirst ⊢
      cases hfirst
      exact hsecond
  | cons instruction tail ih =>
      cases hrun : Stepper.runInstr instruction s with
      | none => simp [runInstrSeq, hrun] at hfirst
      | some next =>
          cases tail with
          | nil =>
              have hnext : next = middle := by
                simpa [runInstrSeq, hrun] using hfirst
              subst middle
              cases second with
              | nil => simpa [runInstrSeq, hrun] using hsecond
              | cons nextInstruction secondTail =>
                  simpa [runInstrSeq, hrun, hmiddle] using hsecond
          | cons nextInstruction tailRest =>
              cases hhalt : next.halt with
              | Running =>
                  have htail : runInstrSeq
                      (nextInstruction :: tailRest) next = some middle := by
                    simpa [runInstrSeq, hrun, hhalt] using hfirst
                  have hjoined := ih (s := next) (middle := middle)
                    htail hmiddle hsecond
                  simpa [runInstrSeq, hrun, hhalt] using hjoined
              | Success => simp [runInstrSeq, hrun, hhalt] at hfirst
              | Returned => simp [runInstrSeq, hrun, hhalt] at hfirst
              | Reverted => simp [runInstrSeq, hrun, hhalt] at hfirst
              | Exception error => simp [runInstrSeq, hrun, hhalt] at hfirst

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_prefix (s : State) (startPC ret xoff xend : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq prefixTemplate (entryState s startPC ret xoff xend rest) =
      some (prefixReturned s (pcAfter startPC prefixTemplate)
        ret xoff xend rest) := by
  have hcap (n : Nat) (hn : n ≤ 14) : rest.length + n < 1024 := by omega
  simp (discharger := omega)
    [prefixTemplate, entryState, prefixReturned,
      PackedInitialFrame.initialSuffix, PackedStepFrame.suffixStack,
      runInstrSeq, Stepper.runInstr, pcAfter, push1, push4, push5, push12,
      hrun, hcap, Nat.add_assoc, Instr.size_push]

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_hashLoadStep (s : State) (startPC : UInt256)
    (address : Nat) (rest : List UInt256)
    (haddress : address < 2 ^ 256)
    (hactive : address + 32 ≤ s.activeWords.toNat * 32)
    (hstack : rest.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq (hashLoadStep address)
      { s with pc := startPC, stack := rest } =
      some (hashLoadReturned s (pcAfter startPC (hashLoadStep address))
        address rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have haddressWord : (UInt256.ofNat address).toNat = address := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt haddress
  have hshift : (UInt256.ofNat 64).toNat = 64 := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by norm_num)
  have hactiveEq : s.activeWordsAfterUInt256 address 32 = s.activeWords :=
    activeWordsAfterUInt256_eq s address 32 hactive
  simp only [State.activeWordsAfterUInt256] at hactiveEq
  simp (discharger := omega)
    [hashLoadStep, hashLoadReturned, duplicateWord, runInstrSeq,
      Stepper.runInstr, pcAfter, push1, push2, op, dup1,
      hrun, hcap0, hcap1, hcap2, hcap3, haddressWord, hshift, hactiveEq,
      State.activeWordsAfterUInt256, List.getElem?_cons_zero,
      UInt256.succ, Instr.size_push, Instr.size_op, Nat.add_assoc]
  rfl

private theorem prefix_endPC :
    pcAfter (UInt256.ofNat 784) prefixTemplate = UInt256.ofNat 846 := by
  decide

private theorem load480_endPC :
    pcAfter (UInt256.ofNat 846) (hashLoadStep 480) = UInt256.ofNat 855 := by
  decide

private theorem load448_endPC :
    pcAfter (UInt256.ofNat 855) (hashLoadStep 448) = UInt256.ofNat 864 := by
  decide

private theorem load416_endPC :
    pcAfter (UInt256.ofNat 864) (hashLoadStep 416) = UInt256.ofNat 873 := by
  decide

private theorem load384_endPC :
    pcAfter (UInt256.ofNat 873) (hashLoadStep 384) = UInt256.ofNat 882 := by
  decide

private theorem load352_endPC :
    pcAfter (UInt256.ofNat 882) (hashLoadStep 352) = UInt256.ofNat 891 := by
  decide

theorem runInstrSeq_hashEntry_raw (s : State) (ret xoff xend : UInt256)
    (rest : List UInt256) (hactive : 16 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1003) (hrun : s.halt = .Running) :
    runInstrSeq hashEntryTemplate
      (entryState s (UInt256.ofNat 784) ret xoff xend rest) =
      some (rawReturned s (UInt256.ofNat 891) ret xoff xend rest) := by
  let suffix := PackedStepFrame.suffixStack
    (PackedInitialFrame.initialSuffix ret xoff xend) ++ rest
  let r480 := duplicateWord (MachineState.readWord s.memory 480) :: suffix
  let r448 := duplicateWord (MachineState.readWord s.memory 448) :: r480
  let r416 := duplicateWord (MachineState.readWord s.memory 416) :: r448
  let r384 := duplicateWord (MachineState.readWord s.memory 384) :: r416
  have hsuffix : suffix.length = rest.length + 14 := by
    simp [suffix, PackedStepFrame.suffixStack_length, Nat.add_comm]
  have hr480 : r480.length = rest.length + 15 := by simp [r480, hsuffix]
  have hr448 : r448.length = rest.length + 16 := by simp [r448, hr480]
  have hr416 : r416.length = rest.length + 17 := by simp [r416, hr448]
  have hr384 : r384.length = rest.length + 18 := by simp [r384, hr416]
  have hp := runInstrSeq_prefix s (UInt256.ofNat 784) ret xoff xend rest
    hstack hrun
  rw [prefix_endPC] at hp
  have h480 := runInstrSeq_hashLoadStep s (UInt256.ofNat 846) 480 suffix
    (by norm_num) (by omega) (by omega) hrun
  rw [load480_endPC] at h480
  have h448 := runInstrSeq_hashLoadStep s (UInt256.ofNat 855) 448 r480
    (by norm_num) (by omega) (by omega) hrun
  rw [load448_endPC] at h448
  have h416 := runInstrSeq_hashLoadStep s (UInt256.ofNat 864) 416 r448
    (by norm_num) (by omega) (by omega) hrun
  rw [load416_endPC] at h416
  have h384 := runInstrSeq_hashLoadStep s (UInt256.ofNat 873) 384 r416
    (by norm_num) (by omega) (by omega) hrun
  rw [load384_endPC] at h384
  have h352 := runInstrSeq_hashLoadStep s (UInt256.ofNat 882) 352 r384
    (by norm_num) (by omega) (by omega) hrun
  rw [load352_endPC] at h352
  have hp480 := runInstrSeq_append_running hp (by simpa [prefixReturned] using hrun) h480
  have hp448 := runInstrSeq_append_running hp480
    (by simpa [hashLoadReturned] using hrun) h448
  have hp416 := runInstrSeq_append_running hp448
    (by simpa [hashLoadReturned] using hrun) h416
  have hp384 := runInstrSeq_append_running hp416
    (by simpa [hashLoadReturned] using hrun) h384
  have hp352 := runInstrSeq_append_running hp384
    (by simpa [hashLoadReturned] using hrun) h352
  simpa [hashEntryTemplate, hashLoadTemplate, rawReturned, loadedRegs,
    prefixReturned, hashLoadReturned, suffix, r480, r448, r416, r384,
    List.append_assoc] using hp352

theorem loadedRegs_eq (s : State) (h : Compression.HashState)
    (hhash : StackMemory.hashAt s.memory = Compression.embedHash h) :
    loadedRegs s = PackedStepFrame.regsStack .even
      (PackedHashEntry.initialRegs h) := by
  have h0 := congrArg (fun value => value.h0) hhash
  have h1 := congrArg (fun value => value.h1) hhash
  have h2 := congrArg (fun value => value.h2) hhash
  have h3 := congrArg (fun value => value.h3) hhash
  have h4 := congrArg (fun value => value.h4) hhash
  simp only [StackMemory.hashAt, Compression.embedHash] at h0 h1 h2 h3 h4
  rw [loadedRegs, h0, h1, h2, h3, h4]
  simp only [PackedStepFrame.regsStack, PackedHashEntry.initialRegs,
    duplicateWord_ofUInt32]

theorem rawReturned_eq_frame (s : State) (endPC : UInt256)
    (h : Compression.HashState) (ret xoff xend : UInt256)
    (rest : List UInt256)
    (hhash : StackMemory.hashAt s.memory = Compression.embedHash h) :
    rawReturned s endPC ret xoff xend rest =
      frameReturned s endPC h ret xoff xend rest := by
  simp only [rawReturned, frameReturned, PackedStepFrame.frameStack,
    PackedInitialFrame.initialFrame]
  rw [loadedRegs_eq s h hhash]

private theorem prefixTemplate_straight :
    ∀ instruction ∈ prefixTemplate, StraightLine instruction := by
  intro instruction hmem
  simp only [prefixTemplate, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor

private theorem hashLoadStep_straight (address : Nat) :
    ∀ instruction ∈ hashLoadStep address, StraightLine instruction := by
  intro instruction hmem
  simp only [hashLoadStep, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor

private theorem straight_append (first second : List Instr)
    (hfirst : ∀ instruction ∈ first, StraightLine instruction)
    (hsecond : ∀ instruction ∈ second, StraightLine instruction) :
    ∀ instruction ∈ first ++ second, StraightLine instruction := by
  intro instruction hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hfirst instruction hmem
  · exact hsecond instruction hmem

private theorem hashLoadTemplate_straight :
    ∀ instruction ∈ hashLoadTemplate, StraightLine instruction := by
  rw [hashLoadTemplate]
  exact straight_append _ _
    (straight_append _ _
      (straight_append _ _
        (straight_append _ _
          (hashLoadStep_straight 480) (hashLoadStep_straight 448))
        (hashLoadStep_straight 416))
      (hashLoadStep_straight 384))
    (hashLoadStep_straight 352)

private theorem hashEntryTemplate_straight :
    ∀ instruction ∈ hashEntryTemplate, StraightLine instruction := by
  intro instruction hmem
  rw [hashEntryTemplate] at hmem
  rcases List.mem_append.mp hmem with hprefix | hloads
  · exact prefixTemplate_straight instruction hprefix
  · exact hashLoadTemplate_straight instruction hloads

private theorem code_bound : A.code.size < UInt256.size := by
  change submissionBytecode.size < UInt256.size
  rw [referenceBytecode_size]
  decide

private theorem hashEntryTemplate_wellFormed :
    ∀ instruction ∈ hashEntryTemplate,
      Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def hashEntrySite : GenericRoundSite A .Osaka hashEntryTemplate :=
  StackSiteBuilder.ofSlice hashEntryTemplate 460 artifact_hashEntry_slice (by
    change 460 + hashEntryTemplate.length ≤ Artifact.submissionInstructions.length
    rw [hashEntryTemplate_length, Artifact.referenceInstructions_count]
    decide) code_bound hashEntryTemplate_wellFormed (by decide)

@[simp] theorem hashEntrySite_startPC :
    hashEntrySite.startPC = UInt256.ofNat 784 := by
  rfl

@[simp] theorem hashEntrySite_endPC :
    hashEntrySite.endPC = UInt256.ofNat 891 := by
  rfl

theorem runLocatedBlock_hashEntry (s : State) (h : Compression.HashState)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hhash : StackMemory.hashAt s.memory = Compression.embedHash h)
    (hactive : 16 ≤ s.activeWords.toNat) (hstack : rest.length < 1003)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock hashEntrySite.path
      (entryState s hashEntrySite.startPC ret xoff xend rest) =
      some (frameReturned s hashEntrySite.endPC h ret xoff xend rest) := by
  have hraw := StackRoundTrace.runLocatedBlock_eq_runInstrSeq_site
    hashEntrySite (entryState s hashEntrySite.startPC ret xoff xend rest) rfl (by
      intro located hmem u v hresult
      apply StackRoundTrace.runInstr_pc_of_straight ?_ hresult
      apply hashEntryTemplate_straight located.located.instruction
      rw [← hashEntrySite.instruction_eq]
      exact List.mem_map_of_mem hmem)
  rw [hraw, hashEntrySite_startPC,
    runInstrSeq_hashEntry_raw s ret xoff xend rest hactive hstack hrun,
    hashEntrySite_endPC]
  exact congrArg some (rawReturned_eq_frame s (UInt256.ofNat 891)
    h ret xoff xend rest hhash)

def gasSteps_hashEntry (s : State) (h : Compression.HashState)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hhash : StackMemory.hashAt s.memory = Compression.embedHash h)
    (hactive : 16 ≤ s.activeWords.toNat) (hstack : rest.length < 1003)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entryState s hashEntrySite.startPC ret xoff xend rest)
      (frameReturned s hashEntrySite.endPC h ret xoff xend rest) := by
  have hartifactCode : s.executionEnv.code = A.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  apply Stepper.runLocatedBlock_sound A .Osaka hashEntrySite.path
  · simpa [entryState] using hartifactCode
  · simpa [entryState] using hfork
  · exact runLocatedBlock_hashEntry s h ret xoff xend rest hhash
      hactive hstack hrun
  · simpa [entryState] using hrun
  · simpa [entryState] using hnp

#print axioms duplicateWord_ofUInt32
#print axioms runInstrSeq_hashEntry_raw
#print axioms loadedRegs_eq
#print axioms gasSteps_hashEntry

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntryTrace

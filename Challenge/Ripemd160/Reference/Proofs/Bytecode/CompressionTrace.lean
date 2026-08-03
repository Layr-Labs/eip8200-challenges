import Challenge.Ripemd160.Reference.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ScheduleCorrect
import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Direct trace skeleton for RIPEMD-160 compression

This module pins the whole `compress` body (artifact indices 451--646) and
exposes its four compositional seams: schedule construction, the left line,
the right line, and the final cross-combination.  Calls to the schedule and
round helpers remain `GasSteps` parameters; their independent direct traces
can therefore be substituted without replaying this control-flow proof.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka

/-- The exact frozen artifact interval occupied by `compress`.  `runBlock`
resolves every index through `referenceArtifact`, so these lists cannot drift
from the compiled bytecode. -/
def compressionPath : List Nat := List.range' 451 196

def scheduleSetupPath : List Nat := [451, 452, 453, 454, 455]
def copyStatePath : List Nat := List.range' 456 13
def leftInitPath : List Nat := [469]
def leftTestPath : List Nat := List.range' 470 7
def leftRoundSetupPath : List Nat := List.range' 477 28
def leftIncrementPath : List Nat := List.range' 505 9
def leftExitPath : List Nat := List.range' 514 2
def rightInitPath : List Nat := [516]
def rightTestPath : List Nat := List.range' 517 7
def rightRoundSetupPath : List Nat := List.range' 524 30
def rightIncrementPath : List Nat := List.range' 554 9
def rightExitPath : List Nat := List.range' 563 2
def combinationPath : List Nat := List.range' 565 82

def scheduleSetupLocated : List Located :=
  [⟨451, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨452, .push ⟨2, by decide⟩ (UInt256.ofNat 630), by rfl, by decide⟩,
   ⟨453, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨454, .push ⟨2, by decide⟩ (UInt256.ofNat 566), by rfl, by decide⟩,
   ⟨455, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem scheduleSetupPC (j : Nat)
    (hlo : 451 ≤ j) (hhi : j ≤ 455) :
    Artifact.referenceArtifact.instructionPC j =
      [621, 622, 625, 626, 629][j - 451]! := by
  interval_cases j <;> rfl

def copyStateLocated : List Located :=
  [⟨456, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨457, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨458, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨459, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨460, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨461, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨462, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨463, .push ⟨2, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨464, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨465, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨466, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨467, .push ⟨2, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨468, .op .MCOPY, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem copyStatePC (j : Nat)
    (hlo : 456 ≤ j) (hhi : j ≤ 468) :
    Artifact.referenceArtifact.instructionPC j =
      [630, 631, 633, 635, 637, 638, 640, 642, 645, 646, 648,
        650, 653][j - 456]! := by
  interval_cases j <;> rfl

def leftTestLocated : List Located :=
  [⟨470, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨471, .push ⟨1, by decide⟩ (UInt256.ofNat 80), by rfl, by decide⟩,
   ⟨472, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨473, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨474, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨475, .push ⟨2, by decide⟩ (UInt256.ofNat 726), by rfl, by decide⟩,
   ⟨476, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem leftTestPC (j : Nat)
    (hlo : 470 ≤ j) (hhi : j ≤ 476) :
    Artifact.referenceArtifact.instructionPC j =
      [655, 656, 658, 659, 660, 661, 664][j - 470]! := by
  interval_cases j <;> rfl

def leftIncrementLocated : List Located :=
  [⟨505, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨506, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨507, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨508, .op (.Dup ⟨1, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨509, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨510, .op (.Swap ⟨0, by decide⟩), by rfl,
      wfOp (by decide) trivial rfl⟩,
   ⟨511, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨512, .push ⟨2, by decide⟩ (UInt256.ofNat 655), by rfl, by decide⟩,
   ⟨513, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem leftIncrementPC (j : Nat)
    (hlo : 505 ≤ j) (hhi : j ≤ 513) :
    Artifact.referenceArtifact.instructionPC j =
      [714, 715, 716, 718, 719, 720, 721, 722, 725][j - 505]! := by
  interval_cases j <;> rfl

def compressEntry (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 621
           stack := [messageOffset, returnDest] ++ rest }

/-- State at the independently verified schedule helper (PC `0x236`). -/
def scheduleEntry (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 566
           stack := [messageOffset, UInt256.ofNat 630,
             messageOffset, returnDest] ++ rest }

/-- Return point supplied to the schedule helper.  Its memory is intentionally
caller-parametric: `ScheduleCorrect` supplies the schedule-memory invariant. -/
def scheduleReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 630
           stack := [messageOffset, returnDest] ++ rest }

def copyRegion (s : State) (dest src size : Nat) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (MachineState.readPadded s.memory src size) dest
    activeWords := s.activeWordsAfterUInt256_2 dest size src size }

def copiedWorkingState (s : State) : State :=
  copyRegion (copyRegion (copyRegion s 192 32 160) 352 32 160) 512 32 160

def copiesReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) : State :=
  let t := copiedWorkingState s
  { t with pc := UInt256.ofNat 654
           stack := [messageOffset, returnDest] ++ rest }

def leftLoopAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 655
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def leftBodyAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 665
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

/-- The round helper returns one disposable Yul expression above the loop
index.  The concrete round trace determines `discard`; loop control does not. -/
def leftRoundReturned (s : State) (messageOffset returnDest discard : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 714
           stack := discard :: UInt256.ofNat i :: messageOffset :: returnDest :: rest }

set_option linter.unusedSimpArgs false in
theorem run_scheduleSetup (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scheduleSetupLocated
      (compressEntry s messageOffset returnDest rest) =
        some (scheduleEntry s messageOffset returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hdest : Decode.isValidJumpDest referenceBytecode 566 = true := by decide
  simp [scheduleSetupLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    compressEntry, scheduleEntry, hrun, hcode,
    hc2, hc3, hc4, hc5, hdest]

def gasSteps_scheduleSetup (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (compressEntry s messageOffset returnDest rest)
      (scheduleEntry s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scheduleSetupLocated
      (s := compressEntry s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_scheduleSetup s messageOffset returnDest rest hstack hcode hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_copyState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyStateLocated
      (scheduleReturned s messageOffset returnDest rest) =
        some (copiesReturned s messageOffset returnDest rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [copyStateLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scheduleReturned, copiesReturned, copiedWorkingState, copyRegion,
    hrun, hc2, hc3, hc4, hc5, State.activeWordsAfterUInt256_2]

def gasSteps_copyState (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scheduleReturned s messageOffset returnDest rest)
      (copiesReturned s messageOffset returnDest rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka copyStateLocated
      (s := scheduleReturned s messageOffset returnDest rest)
  · exact hcode
  · exact hfork
  · exact run_copyState s messageOffset returnDest rest hstack hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_leftTest_continue (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftTestLocated
      (leftLoopAt s messageOffset returnDest rest i) =
        some (leftBodyAt s messageOffset returnDest rest i) := by
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 80) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [leftTestLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    leftLoopAt, leftBodyAt, hrun, hlt, hzero, hfalse,
    hc3, hc4, hc5]

def gasSteps_leftTest_continue (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftLoopAt s messageOffset returnDest rest i)
      (leftBodyAt s messageOffset returnDest rest i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftTestLocated
      (s := leftLoopAt s messageOffset returnDest rest i)
  · exact hcode
  · exact hfork
  · exact run_leftTest_continue s messageOffset returnDest rest i hi hstack hrun
  · exact hrun
  · exact hnp

set_option linter.unusedSimpArgs false in
theorem run_leftIncrement (s : State) (messageOffset returnDest discard : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock leftIncrementLocated
      (leftRoundReturned s messageOffset returnDest discard rest i) =
        some (leftLoopAt s messageOffset returnDest rest (i + 1)) := by
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) := by
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 655 = true := by decide
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [leftIncrementLocated, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    leftRoundReturned, leftLoopAt, hrun, hcode, hadd, hdest,
    hc3, hc4, hc5, List.exchange]

def gasSteps_leftIncrement (s : State)
    (messageOffset returnDest discard : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (leftRoundReturned s messageOffset returnDest discard rest i)
      (leftLoopAt s messageOffset returnDest rest (i + 1)) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka leftIncrementLocated
      (s := leftRoundReturned s messageOffset returnDest discard rest i)
  · exact hcode
  · exact hfork
  · exact run_leftIncrement s messageOffset returnDest discard rest i hi
      hstack hcode hrun
  · exact hrun
  · exact hnp

/-- One complete left-line iteration, parameterized only by the table/round
helper seam.  This is the composition point consumed by the 80-round fold. -/
def gasSteps_leftIteration (s t : State)
    (messageOffset returnDest discard : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80) (hstack : rest.length < 1019)
    (hcodeS : s.executionEnv.code = referenceBytecode)
    (hcodeT : t.executionEnv.code = referenceBytecode)
    (hforkS : s.fork = .Osaka) (hforkT : t.fork = .Osaka)
    (hrunS : s.halt = .Running) (hrunT : t.halt = .Running)
    (hnpS : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hnpT : Precompile.isPrecompile t.executionEnv.fork
      t.executionEnv.codeAddr = false)
    (roundSeam : Challenge.EvmProof.GasSteps
      (leftBodyAt s messageOffset returnDest rest i)
      (leftRoundReturned t messageOffset returnDest discard rest i)) :
    Challenge.EvmProof.GasSteps
      (leftLoopAt s messageOffset returnDest rest i)
      (leftLoopAt t messageOffset returnDest rest (i + 1)) :=
  (gasSteps_leftTest_continue s messageOffset returnDest rest i hi hstack
    hcodeS hforkS hrunS hnpS).trans <|
    roundSeam.trans <|
      gasSteps_leftIncrement t messageOffset returnDest discard rest i hi
        hstack hcodeT hforkT hrunT hnpT

/-- Functional invariant paired with the bytecode loop index. -/
def LeftInvariant (word : Nat → UInt32) (initial : Compression.EvmWorking)
    (i : Nat) (current : Compression.EvmWorking) : Prop :=
  current = CompressionCorrect.evmLeftRounds word i initial

theorem leftInvariant_zero (word : Nat → UInt32)
    (initial : Compression.EvmWorking) :
    LeftInvariant word initial 0 initial := by
  rfl

theorem leftInvariant_step (word : Nat → UInt32)
    (initial current : Compression.EvmWorking) (i : Nat)
    (h : LeftInvariant word initial i current) :
    LeftInvariant word initial (i + 1)
      (CompressionCorrect.evmLeftStep word i current) := by
  subst current
  rfl

theorem leftInvariant_embedded (word : Nat → UInt32)
    (initial : Compression.Working) (i : Nat) (hi : i ≤ 80) :
    LeftInvariant word (Compression.embed initial) i
      (Compression.embed (CompressionCorrect.leftRounds word i initial)) := by
  unfold LeftInvariant
  symm
  exact CompressionCorrect.evmLeftRounds_embed word i initial hi

/-- The fold theorem makes the bytecode's literal 80-iteration bound explicit
while permitting each round trace to update memory. -/
def gasSteps_left80 (I : Nat → State)
    (iteration : ∀ i, i < 80 → Challenge.EvmProof.GasSteps (I i) (I (i + 1))) :
    Challenge.EvmProof.GasSteps (I 0) (I 80) :=
  Challenge.EvmProof.GasSteps.iterateBounded 80 iteration

def rightLoopAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 729
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def rightBodyAt (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 739
           stack := UInt256.ofNat i :: messageOffset :: returnDest :: rest }

def rightRoundReturned (s : State) (messageOffset returnDest discard : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 792
           stack := discard :: UInt256.ofNat i :: messageOffset :: returnDest :: rest }

/-- Right-line loop skeleton.  `iteration` is discharged by composing the
right condition, table/round seam, and increment paths pinned above. -/
def gasSteps_right80 (I : Nat → State)
    (iteration : ∀ i, i < 80 → Challenge.EvmProof.GasSteps (I i) (I (i + 1))) :
    Challenge.EvmProof.GasSteps (I 0) (I 80) :=
  Challenge.EvmProof.GasSteps.iterateBounded 80 iteration

def RightInvariant (word : Nat → UInt32) (initial : Compression.EvmWorking)
    (i : Nat) (current : Compression.EvmWorking) : Prop :=
  current = CompressionCorrect.evmRightRounds word i initial

theorem rightInvariant_zero (word : Nat → UInt32)
    (initial : Compression.EvmWorking) :
    RightInvariant word initial 0 initial := by
  rfl

theorem rightInvariant_step (word : Nat → UInt32)
    (initial current : Compression.EvmWorking) (i : Nat)
    (h : RightInvariant word initial i current) :
    RightInvariant word initial (i + 1)
      (CompressionCorrect.evmRightStep word i current) := by
  subst current
  rfl

theorem rightInvariant_embedded (word : Nat → UInt32)
    (initial : Compression.Working) (i : Nat) (hi : i ≤ 80) :
    RightInvariant word (Compression.embed initial) i
      (Compression.embed (CompressionCorrect.rightRounds word i initial)) := by
  unfold RightInvariant
  symm
  exact CompressionCorrect.evmRightRounds_embed word i initial hi

def wordAt (s : State) (address : Nat) : UInt256 :=
  MachineState.readWord s.memory address

def workingAt (s : State) (base : Nat) : Compression.EvmWorking :=
  { a := wordAt s base
    b := wordAt s (base + 32)
    c := wordAt s (base + 64)
    d := wordAt s (base + 96)
    e := wordAt s (base + 128) }

def savedHashAt512 (s : State) : Compression.EvmHashState :=
  { h0 := wordAt s 512
    h1 := wordAt s 544
    h2 := wordAt s 576
    h3 := wordAt s 608
    h4 := wordAt s 640 }

/-- Values computed by artifact indices 565--639.  The unusual store order
(`64,96,128,160,32`) is the in-place implementation of RIPEMD's cross-line
combination; the old chaining words are read from the saved copy at `0x200`. -/
def tailCombination (s : State) : Compression.EvmHashState :=
  Compression.evmCombine (savedHashAt512 s) (workingAt s 192) (workingAt s 352)

theorem tailCombination_embedded (h : Compression.HashState)
    (left right : Compression.Working) :
    Compression.evmCombine (Compression.embedHash h)
      (Compression.embed left) (Compression.embed right) =
        Compression.embedHash (Compression.combine h left right) :=
  Compression.evmCombine_embed h left right

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTrace

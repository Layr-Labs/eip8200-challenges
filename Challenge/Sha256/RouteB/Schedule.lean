import Challenge.Sha256.RouteB.Functions
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Direct reference-bytecode proof of the SHA message schedule

The two bytecode loops are proved with indexed memory invariants.  The first
loads sixteen big-endian words from the padded message; the second derives the
remaining forty-eight words with the SHA recurrence.
-/

namespace Challenge.Sha256.RouteB.Schedule

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.RouteB.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.RouteB.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.RouteB.Word.ofNat_add_ofNat h

def firstConditionPath :
    List (Challenge.RouteB.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨327, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨328, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨329, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨330, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨331, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨332, .push ⟨2, by decide⟩ (UInt256.ofNat 491), by rfl, by decide⟩,
   ⟨333, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def firstLoadPath :
    List (Challenge.RouteB.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨334, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨335, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨336, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨337, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨338, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨339, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨340, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨341, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩]

def firstStorePath :
    List (Challenge.RouteB.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨342, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨343, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨344, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨345, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨346, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, .push ⟨2, by decide⟩ (UInt256.ofNat 800), by rfl, by decide⟩,
   ⟨348, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨349, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨350, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨351, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

def firstIncrementPath :
    List (Challenge.RouteB.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨352, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨353, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨354, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨355, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨356, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨357, .push ⟨2, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨358, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def loadOffset (msgOff : UInt256) (j : Nat) : Nat :=
  (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) + msgOff).toNat

def initialWord (memory : ByteArray) (msgOff : UInt256) (j : Nat) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord memory (loadOffset msgOff j))
    (UInt256.ofNat 224)

def scheduleSlot (j : Nat) : Nat :=
  Accessors.slotOffset 800 (UInt256.ofNat j)

def firstAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 448
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def afterFirstCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 458
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest }

def afterFirstLoad (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with
    pc := UInt256.ofNat 468
    stack := [initialWord s.memory msgOff j, UInt256.ofNat j,
      msgOff, returnDest] ++ rest
    activeWords := s.activeWordsAfterUInt256 (loadOffset msgOff j) 32 }

def afterFirstStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  let loaded := afterFirstLoad s msgOff returnDest rest j
  { loaded with
    pc := UInt256.ofNat 481
    stack := [UInt256.ofNat j, msgOff, returnDest] ++ rest
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded (initialWord s.memory msgOff j).toNat 32)
      (scheduleSlot j)
    activeWords := loaded.activeWordsAfterUInt256 (scheduleSlot j) 32 }

def afterFirstIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { afterFirstStore s msgOff returnDest rest j with
    pc := UInt256.ofNat 448
    stack := [UInt256.ofNat (j + 1), msgOff, returnDest] ++ rest }

@[simp] private theorem firstPC (i : Nat) (hlo : 327 ≤ i) (hhi : i ≤ 358) :
    Artifact.referenceArtifact.instructionPC i =
      [448, 449, 451, 452, 453, 454, 457, 458, 459, 461, 462,
       463, 464, 465, 467, 468, 469, 470, 471, 473, 474, 477,
       478, 479, 480, 481, 483, 484, 485, 486, 487, 490][i - 327]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
private theorem run_firstCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16)
    (hstack : rest.length < 1019)
    (hrun : s.halt = .Running) :
    Challenge.RouteB.Stepper.runLocatedBlock firstConditionPath
      (firstAt s msgOff returnDest rest j) =
        some (afterFirstCondition s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.RouteB.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat 16) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hjWord, Challenge.RouteB.Word.word_toNat_ofNat, hj]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have htrue : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [firstConditionPath, Challenge.RouteB.Stepper.runLocatedBlock,
    Challenge.RouteB.Stepper.runLocated, Challenge.RouteB.Stepper.runInstr,
    firstAt, afterFirstCondition, hc3, hc4, hc5, hrun, hlt, hzero,
    htrue]

set_option linter.unusedSimpArgs false in
private theorem run_firstLoad (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hstack : rest.length < 1018)
    (hrun : s.halt = .Running) :
    Challenge.RouteB.Stepper.runLocatedBlock firstLoadPath
      (afterFirstCondition s msgOff returnDest rest j) =
        some (afterFirstLoad s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hoff : msgOff + UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) =
      UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) + msgOff :=
    Challenge.RouteB.Word.word_add_comm _ _
  simp [firstLoadPath, Challenge.RouteB.Stepper.runLocatedBlock,
    Challenge.RouteB.Stepper.runLocated, Challenge.RouteB.Stepper.runInstr,
    afterFirstCondition, afterFirstLoad, initialWord, loadOffset, List.exchange,
    hc3, hc4, hc5, hc6, hrun, hoff, State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
private theorem run_firstStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hstack : rest.length < 1016)
    (hrun : s.halt = .Running) :
    Challenge.RouteB.Stepper.runLocatedBlock firstStorePath
      (afterFirstLoad s msgOff returnDest rest j) =
        some (afterFirstStore s msgOff returnDest rest j) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hoff : UInt256.ofNat 800 +
        UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5) =
      UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5) +
        UInt256.ofNat 800 := Challenge.RouteB.Word.word_add_comm _ _
  simp [firstStorePath, Challenge.RouteB.Stepper.runLocatedBlock,
    Challenge.RouteB.Stepper.runLocated, Challenge.RouteB.Stepper.runInstr,
    afterFirstLoad, afterFirstStore, scheduleSlot, Accessors.slotOffset,
    List.exchange, hc4, hc5, hc6, hc7, hc8, hrun, hoff,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
private theorem run_firstIncrement (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.RouteB.Stepper.runLocatedBlock firstIncrementPath
      (afterFirstStore s msgOff returnDest rest j) =
        some (afterFirstIteration s msgOff returnDest rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hadd : UInt256.ofNat j + UInt256.ofNat 1 =
      UInt256.ofNat (j + 1) := Challenge.RouteB.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest referenceBytecode 448 = true := by decide
  simp [firstIncrementPath, Challenge.RouteB.Stepper.runLocatedBlock,
    Challenge.RouteB.Stepper.runLocated, Challenge.RouteB.Stepper.runInstr,
    afterFirstStore, afterFirstIteration, afterFirstLoad, List.exchange,
    hc3, hc4, hc5, hcode, hrun, hadd, hdest]

theorem gasSteps_firstIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j < 16)
    (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.RouteB.GasSteps (firstAt s msgOff returnDest rest j)
      (afterFirstIteration s msgOff returnDest rest j) := by
  have gCondition : Challenge.RouteB.GasSteps
      (firstAt s msgOff returnDest rest j)
      (afterFirstCondition s msgOff returnDest rest j) := by
    apply Challenge.RouteB.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstConditionPath
    · exact hcode
    · exact hfork
    · exact run_firstCondition s msgOff returnDest rest j hj (by omega) hrun
    · exact hrun
    · exact hnp
  have gLoad : Challenge.RouteB.GasSteps
      (afterFirstCondition s msgOff returnDest rest j)
      (afterFirstLoad s msgOff returnDest rest j) := by
    apply Challenge.RouteB.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstLoadPath
    · exact hcode
    · exact hfork
    · exact run_firstLoad s msgOff returnDest rest j (by omega) hrun
    · exact hrun
    · exact hnp
  have gStore : Challenge.RouteB.GasSteps
      (afterFirstLoad s msgOff returnDest rest j)
      (afterFirstStore s msgOff returnDest rest j) := by
    apply Challenge.RouteB.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstStorePath
    · exact hcode
    · exact hfork
    · exact run_firstStore s msgOff returnDest rest j hstack hrun
    · exact hrun
    · exact hnp
  have gIncrement : Challenge.RouteB.GasSteps
      (afterFirstStore s msgOff returnDest rest j)
      (afterFirstIteration s msgOff returnDest rest j) := by
    apply Challenge.RouteB.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka firstIncrementPath
    · exact hcode
    · exact hfork
    · exact run_firstIncrement s msgOff returnDest rest j hj (by omega)
        hcode hrun
    · exact hrun
    · exact hnp
  exact gCondition.trans (gLoad.trans (gStore.trans gIncrement))

def firstLoopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => firstAt s msgOff returnDest rest 0
  | j + 1 => afterFirstIteration
      (firstLoopState s msgOff returnDest rest j) msgOff returnDest rest j

@[simp] theorem firstLoopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff returnDest rest j).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [firstLoopState, afterFirstIteration, afterFirstStore,
        afterFirstLoad, ih]

@[simp] theorem firstLoopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    (firstLoopState s msgOff returnDest rest j).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [firstLoopState, afterFirstIteration, afterFirstStore,
        afterFirstLoad, ih]

@[simp] theorem firstAt_firstLoopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    firstAt (firstLoopState s msgOff returnDest rest j)
      msgOff returnDest rest j = firstLoopState s msgOff returnDest rest j := by
  cases j <;> rfl

theorem gasSteps_firstLoop (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.RouteB.GasSteps (firstLoopState s msgOff returnDest rest 0)
      (firstLoopState s msgOff returnDest rest 16) := by
  apply Challenge.RouteB.GasSteps.iterateBounded (count := 16)
  intro j hj
  let q := firstLoopState s msgOff returnDest rest j
  have hqcode : q.executionEnv.code = referenceBytecode := by
    simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by
    simpa [q] using hrun
  have hqnp : Precompile.isPrecompile q.executionEnv.fork
      q.executionEnv.codeAddr = false := by
    simpa [q] using hnp
  have g := gasSteps_firstIteration q msgOff returnDest rest j hj hstack
    hqcode hqfork hqrun hqnp
  rw [firstAt_firstLoopState] at g
  simpa [firstLoopState, q] using g

def scheduleEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 446
    stack := [msgOff, returnDest] ++ rest }

def scheduleStartPath :
    List (Challenge.RouteB.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨325, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨326, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

@[simp] private theorem pc325 : Artifact.referenceArtifact.instructionPC 325 = 446 := by decide
@[simp] private theorem pc326 : Artifact.referenceArtifact.instructionPC 326 = 447 := by decide

private theorem run_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.RouteB.Stepper.runLocatedBlock scheduleStartPath
      (scheduleEntry s msgOff returnDest rest) =
        some (firstLoopState s msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [scheduleStartPath, Challenge.RouteB.Stepper.runLocatedBlock,
    Challenge.RouteB.Stepper.runLocated, Challenge.RouteB.Stepper.runInstr,
    scheduleEntry, firstLoopState, firstAt, hc2, hrun]
  rfl

theorem gasSteps_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.RouteB.GasSteps (scheduleEntry s msgOff returnDest rest)
      (firstLoopState s msgOff returnDest rest 0) := by
  apply Challenge.RouteB.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka scheduleStartPath
  · exact hcode
  · exact hfork
  · exact run_scheduleStart s msgOff returnDest rest hstack hrun
  · exact hrun
  · exact hnp

end Challenge.Sha256.RouteB.Schedule

import Challenge.Modexp.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# One-word MODEXP loop composition

This module closes the two nested exponent loops and composes their exact
`GasSteps` certificates from the small execution segments proved in `Word`.
Keeping this composition separate also lets later correctness and gas-cost
proofs reuse the cached straight-line certificates.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def bitFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 525 .JUMPDEST, opAt 526 .POP, opAt 527 .POP, opAt 528 .POP,
   pushAt 529 1 1, opAt 530 (.Dup ⟨1, by decide⟩), opAt 531 .ADD,
   opAt 532 (.Swap ⟨0, by decide⟩), opAt 533 .POP,
   pushAt 534 2 589, opAt 535 .JUMP]

def bitFinishDispatchState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 8 byte offset acc base with pc := UInt256.ofNat 655 }

@[simp] private theorem exitPCs (i : Nat) (hi : 525 ≤ i) (hii : i ≤ 549) :
    Artifact.submissionArtifact.instructionPC i =
      [655,656,657,658,659,661,662,663,664,665,668,669,670,671,672,
       673,675,676,678,679,680,683,684,685,688][i - 525]! := by
  interval_cases i <;> decide

@[simp] private theorem jump655 :
    Decode.isValidJumpDest submissionBytecode 655 = true :=
  Artifact.isValidJumpDest_index 525 (by rfl)

@[simp] private theorem jump589 :
    Decode.isValidJumpDest submissionBytecode 589 = true :=
  Artifact.isValidJumpDest_index 469 (by rfl)

def bitFinishGuardHeadPath := bitGuardPath.take 6
def bitFinishGuardJumpPath := bitGuardPath.drop 6

/-- Exponent-bit guard state with the taken `JUMPI` operands on the stack. -/
def bitFinishGuardMidState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 8 byte offset acc base with
    pc := UInt256.ofNat 615
    stack := UInt256.ofNat 655 :: UInt256.ofNat 1 ::
      (bitLoopState input outer 8 byte offset acc base).stack }

set_option linter.unusedSimpArgs false in
theorem run_bitFinishGuardHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishGuardHeadPath
      (bitLoopState input outer 8 byte offset acc base) =
        some (bitFinishGuardMidState input outer byte offset acc base) := by
  have h8 : (8 : UInt256).toNat = 8 := by decide
  have h8mod : 8 % 2 ^ 256 = 8 := by norm_num
  have h655Word : (655 : UInt256) = UInt256.ofNat 655 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hzeroIsZero : (UInt256.ofNat 0).isZero = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 150000 })
    [bitFinishGuardHeadPath, bitGuardPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitLoopState, bitFinishGuardMidState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      h8, h8mod, h655Word, honeWord, hzeroIsZero]

set_option linter.unusedSimpArgs false in
theorem run_bitFinishGuardJump (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishGuardJumpPath
      (bitFinishGuardMidState input outer byte offset acc base) =
        some (bitFinishDispatchState input outer byte offset acc base) := by
  have h655 : (655 : UInt256).toNat = 655 := by decide
  have h655Word : (655 : UInt256) = UInt256.ofNat 655 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  simp (config := { maxSteps := 150000 })
    [bitFinishGuardJumpPath, bitGuardPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishGuardMidState, bitLoopState, bitFinishDispatchState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, Challenge.EvmProof.Word.word_toNat_ofNat,
      htrue, h655, h655Word, jump655]

theorem run_bitFinishGuard (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitGuardPath
      (bitLoopState input outer 8 byte offset acc base) =
        some (bitFinishDispatchState input outer byte offset acc base) := by
  have hsplit : bitGuardPath = bitFinishGuardHeadPath ++ bitFinishGuardJumpPath :=
    (List.take_append_drop 6 bitGuardPath).symm
  have hrunning :
      (bitFinishGuardMidState input outer byte offset acc base).halt = .Running := rfl
  rw [hsplit]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_bitFinishGuardHead input outer byte offset acc base) hrunning
    (run_bitFinishGuardJump input outer byte offset acc base)

def bitFinishTailHeadPath := bitFinishTailPath.take 9
def bitFinishTailJumpPath := bitFinishTailPath.drop 9

/-- Exponent-loop state just before the back edge `PUSH2 589; JUMP`. -/
def bitFinishTailMidState (input : ByteArray) (outer : Nat)
    (acc base : UInt256) : State :=
  { expLoopState input (outer + 1) acc base with pc := UInt256.ofNat 665 }

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailHeadPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (bitFinishTailMidState input outer acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsucc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := outer) (b := 1) (by omega : outer + 1 < 2 ^ 256)
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 175000 })
    [bitFinishTailHeadPath, bitFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitFinishTailMidState, bitLoopState, expLoopState,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, exitPCs, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, hsucc, honeWord]

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailJump (input : ByteArray) (outer : Nat)
    (acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailJumpPath
      (bitFinishTailMidState input outer acc base) =
        some (expLoopState input (outer + 1) acc base) := by
  have h589 : (589 : UInt256).toNat = 589 := by decide
  have h589Word : (589 : UInt256) = UInt256.ofNat 589 := by decide
  simp (config := { maxSteps := 175000 })
    [bitFinishTailJumpPath, bitFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishTailMidState, expLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, exitPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, h589, h589Word, jump589]

theorem run_bitFinishTail (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (expLoopState input (outer + 1) acc base) := by
  have hsplit : bitFinishTailPath =
      bitFinishTailHeadPath ++ bitFinishTailJumpPath :=
    (List.take_append_drop 9 bitFinishTailPath).symm
  have hrunning : (bitFinishTailMidState input outer acc base).halt = .Running := rfl
  rw [hsplit]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_bitFinishTailHead input outer byte offset acc base
      hvalid houter) hrunning
    (run_bitFinishTailJump input outer acc base)

def gasSteps_expEnter (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.GasSteps (expLoopState input i acc base)
      (bitLoopState input i 0 (byteWord input (expOffset input + i))
        (UInt256.ofNat (expOffset input + i)) acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka expGuardPath rfl rfl
        (run_expGuard input i acc base hvalid hi) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka expLoadPath rfl rfl
        (run_expLoad input i acc base hvalid hi) rfl
        deployAddress_not_precompile)

def gasSteps_bitIteration (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer j byte offset acc base)
      (bitLoopState input outer (j + 1) byte offset
        (bitStep input byte j acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitGuardPath rfl rfl
        (run_bitGuard input outer j byte offset acc base hj) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitDecodePath rfl rfl
        (run_bitDecode input outer j byte offset acc base hj) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitSquarePath rfl rfl
        (run_bitSquare input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitMaskPath rfl rfl
        (run_bitMask input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitProductPath rfl rfl
        (run_bitProduct input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitChoosePath rfl rfl
        (run_bitChoose input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitAdvancePath rfl rfl
        (run_bitAdvance input outer j byte offset acc base hj) rfl
        deployAddress_not_precompile

def bitAfter (input : ByteArray) (byte : UInt256) (base : UInt256) :
    Nat → UInt256 → UInt256
  | 0, acc => acc
  | j + 1, acc => bitStep input byte j (bitAfter input byte base j acc) base

def gasSteps_bitLoop (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer 0 byte offset acc base)
      (bitLoopState input outer 8 byte offset (bitAfter input byte base 8 acc) base) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (I := fun j =>
      bitLoopState input outer j byte offset (bitAfter input byte base j acc) base) 8
    (fun j hj => gasSteps_bitIteration input outer j byte offset
      (bitAfter input byte base j acc) base hj)

def gasSteps_bitFinish (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer 8 byte offset acc base)
      (expLoopState input (outer + 1) acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitGuardPath rfl rfl
        (run_bitFinishGuard input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitFinishTailPath rfl rfl
        (run_bitFinishTail input outer byte offset acc base hvalid houter) rfl
        deployAddress_not_precompile)

def expStep (input : ByteArray) (i : Nat) (acc base : UInt256) : UInt256 :=
  bitAfter input (byteWord input (expOffset input + i)) base 8 acc

def expAfter (input : ByteArray) (base : UInt256) : Nat → UInt256 → UInt256
  | 0, acc => acc
  | i + 1, acc => expStep input i (expAfter input base i acc) base

def gasSteps_expIteration (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.GasSteps (expLoopState input i acc base)
      (expLoopState input (i + 1) (expStep input i acc base) base) := by
  let byte := byteWord input (expOffset input + i)
  let offset := UInt256.ofNat (expOffset input + i)
  exact (gasSteps_expEnter input i acc base hvalid hi).trans <|
    (gasSteps_bitLoop input i byte offset acc base).trans
      (gasSteps_bitFinish input i byte offset (bitAfter input byte base 8 acc)
        base hvalid hi)

def gasSteps_expLoop (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (expLoopState input 0 acc base)
      (expLoopState input (exponentSize input)
        (expAfter input base (exponentSize input) acc) base) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (I := fun i =>
      expLoopState input i (expAfter input base i acc) base) (exponentSize input)
    (fun i hi => gasSteps_expIteration input i
      (expAfter input base i acc) base hvalid hi)

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

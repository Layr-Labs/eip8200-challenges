import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll0
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll2
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
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
   pushAt 529 1 1, opAt 530 .ADD, pushAt 531 2 589, opAt 532 .JUMP]

def bitFinishDispatchState (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) : State :=
  { bitLoopState input outer 8 byte offset acc base with pc := UInt256.ofNat 655 }

@[simp] private theorem exitPCs (i : Nat) (hi : 525 ≤ i) (hii : i ≤ 549) :
    Artifact.submissionArtifact.instructionPC i =
      [655,656,657,658,659,661,662,665,666,667,668,669,670,671,672,
       673,675,676,678,679,680,683,684,685,688][i - 525]! := by
  interval_cases i <;> decide

@[simp] private theorem jump655 :
    Decode.isValidJumpDest submissionBytecode 655 = true :=
  Artifact.isValidJumpDest_index 525 (by rfl)

@[simp] private theorem jump589 :
    Decode.isValidJumpDest submissionBytecode 589 = true :=
  Artifact.isValidJumpDest_index 469 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_bitExit (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitExitPath
      (bitUnrollState input outer 8 byte offset acc base) =
        some (bitFinishDispatchState input outer byte offset acc base) := by
  have h655 : (655 : UInt256).toNat = 655 := by decide
  have h655Word : (655 : UInt256) = UInt256.ofNat 655 := by decide
  simp (config := { maxSteps := 150000 })
    [bitExitPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitUnrollState, bitLoopState, bitPC, bitFinishDispatchState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      UnrollPCs.exitPC, Challenge.EvmProof.Word.word_toNat_ofNat,
      h655, h655Word, jump655]

set_option linter.unusedSimpArgs false in
theorem run_bitFinishTail (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailPath
      (bitFinishDispatchState input outer byte offset acc base) =
        some (expLoopState input (outer + 1) acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsucc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := outer) (b := 1) (by omega : outer + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat outer =
      UInt256.ofNat (outer + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h589 : (589 : UInt256).toNat = 589 := by decide
  have h589Word : (589 : UInt256) = UInt256.ofNat 589 := by decide
  simp (config := { maxSteps := 175000 })
    [bitFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bitFinishDispatchState, bitLoopState, expLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      exitPCs, List.exchange, Challenge.EvmProof.Word.word_toNat_ofNat,
      hsucc, hincLeft, honeWord, h589, h589Word, jump589]

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

def gasSteps_bitCopy0 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 0 byte offset acc base)
      (bitUnrollState input outer 1 byte offset
        (bitStep input byte 0 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll0.bitDecodePath0 rfl rfl
        (Unroll0.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll0.bitSquarePath0 rfl rfl
        (Unroll0.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll0.bitMaskPath0 rfl rfl
        (Unroll0.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll0.bitProductPath0 rfl rfl
        (Unroll0.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll0.bitChoosePath0 rfl rfl
        (Unroll0.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll0.bitAdvancePath0 rfl rfl
        (Unroll0.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy1 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 1 byte offset acc base)
      (bitUnrollState input outer 2 byte offset
        (bitStep input byte 1 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll1.bitDecodePath1 rfl rfl
        (Unroll1.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll1.bitSquarePath1 rfl rfl
        (Unroll1.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll1.bitMaskPath1 rfl rfl
        (Unroll1.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll1.bitProductPath1 rfl rfl
        (Unroll1.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll1.bitChoosePath1 rfl rfl
        (Unroll1.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll1.bitAdvancePath1 rfl rfl
        (Unroll1.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy2 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 2 byte offset acc base)
      (bitUnrollState input outer 3 byte offset
        (bitStep input byte 2 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll2.bitDecodePath2 rfl rfl
        (Unroll2.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll2.bitSquarePath2 rfl rfl
        (Unroll2.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll2.bitMaskPath2 rfl rfl
        (Unroll2.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll2.bitProductPath2 rfl rfl
        (Unroll2.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll2.bitChoosePath2 rfl rfl
        (Unroll2.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll2.bitAdvancePath2 rfl rfl
        (Unroll2.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy3 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 3 byte offset acc base)
      (bitUnrollState input outer 4 byte offset
        (bitStep input byte 3 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll3.bitDecodePath3 rfl rfl
        (Unroll3.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll3.bitSquarePath3 rfl rfl
        (Unroll3.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll3.bitMaskPath3 rfl rfl
        (Unroll3.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll3.bitProductPath3 rfl rfl
        (Unroll3.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll3.bitChoosePath3 rfl rfl
        (Unroll3.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll3.bitAdvancePath3 rfl rfl
        (Unroll3.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy4 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 4 byte offset acc base)
      (bitUnrollState input outer 5 byte offset
        (bitStep input byte 4 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll4.bitDecodePath4 rfl rfl
        (Unroll4.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll4.bitSquarePath4 rfl rfl
        (Unroll4.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll4.bitMaskPath4 rfl rfl
        (Unroll4.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll4.bitProductPath4 rfl rfl
        (Unroll4.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll4.bitChoosePath4 rfl rfl
        (Unroll4.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll4.bitAdvancePath4 rfl rfl
        (Unroll4.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy5 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 5 byte offset acc base)
      (bitUnrollState input outer 6 byte offset
        (bitStep input byte 5 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll5.bitDecodePath5 rfl rfl
        (Unroll5.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll5.bitSquarePath5 rfl rfl
        (Unroll5.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll5.bitMaskPath5 rfl rfl
        (Unroll5.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll5.bitProductPath5 rfl rfl
        (Unroll5.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll5.bitChoosePath5 rfl rfl
        (Unroll5.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll5.bitAdvancePath5 rfl rfl
        (Unroll5.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy6 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 6 byte offset acc base)
      (bitUnrollState input outer 7 byte offset
        (bitStep input byte 6 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll6.bitDecodePath6 rfl rfl
        (Unroll6.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll6.bitSquarePath6 rfl rfl
        (Unroll6.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll6.bitMaskPath6 rfl rfl
        (Unroll6.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll6.bitProductPath6 rfl rfl
        (Unroll6.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll6.bitChoosePath6 rfl rfl
        (Unroll6.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll6.bitAdvancePath6 rfl rfl
        (Unroll6.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy7 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 7 byte offset acc base)
      (bitUnrollState input outer 8 byte offset
        (bitStep input byte 7 acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll7.bitDecodePath7 rfl rfl
        (Unroll7.run_bitDecode input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll7.bitSquarePath7 rfl rfl
        (Unroll7.run_bitSquare input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll7.bitMaskPath7 rfl rfl
        (Unroll7.run_bitMask input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll7.bitProductPath7 rfl rfl
        (Unroll7.run_bitProduct input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll7.bitChoosePath7 rfl rfl
        (Unroll7.run_bitChoose input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka Unroll7.bitAdvancePath7 rfl rfl
        (Unroll7.run_bitAdvance input outer byte offset acc base) rfl
        deployAddress_not_precompile)

def bitAfter (input : ByteArray) (byte : UInt256) (base : UInt256) :
    Nat → UInt256 → UInt256
  | 0, acc => acc
  | j + 1, acc => bitStep input byte j (bitAfter input byte base j acc) base

def gasSteps_bitLoop (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer 0 byte offset acc base)
      (bitUnrollState input outer 8 byte offset
        (bitAfter input byte base 8 acc) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitEntryPath rfl rfl
        (run_bitEntry input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitJumpPath rfl rfl
        (run_bitJump input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitHeadPath rfl rfl
        (run_bitHead input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (gasSteps_bitCopy0 input outer byte offset
      (bitAfter input byte base 0 acc) base).trans <|
    (gasSteps_bitCopy1 input outer byte offset
      (bitAfter input byte base 1 acc) base).trans <|
    (gasSteps_bitCopy2 input outer byte offset
      (bitAfter input byte base 2 acc) base).trans <|
    (gasSteps_bitCopy3 input outer byte offset
      (bitAfter input byte base 3 acc) base).trans <|
    (gasSteps_bitCopy4 input outer byte offset
      (bitAfter input byte base 4 acc) base).trans <|
    (gasSteps_bitCopy5 input outer byte offset
      (bitAfter input byte base 5 acc) base).trans <|
    (gasSteps_bitCopy6 input outer byte offset
      (bitAfter input byte base 6 acc) base).trans <|
    gasSteps_bitCopy7 input outer byte offset
      (bitAfter input byte base 7 acc) base

def gasSteps_bitFinish (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 8 byte offset acc base)
      (expLoopState input (outer + 1) acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitExitPath rfl rfl
        (run_bitExit input outer byte offset acc base) rfl
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

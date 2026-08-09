import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# One-word MODEXP exit

The completed residue is left-padded into one EVM word, stored at `0x1800`,
and returned with the declared modulus width.  This block is byte-identical to
the baseline (instruction indices 536–549 are inside the unchanged
`[536, 1286)` range); only the incoming state changed, because the window table
leaves memory non-empty and sixteen words active.

The `RETURN` here is the sole normal exit of the word path.  Together with the
zero-modulus `RETURN` at `0x0219` it is what makes the window table's use of
`[0x0000, 0x0200)` invisible to the big path (constraint C1).
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordExit

open EvmSemantics
open EvmSemantics.EVM
open Word
open WordLoops

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

def expFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 536 .JUMPDEST, opAt 537 .POP, opAt 538 (.Dup ⟨0, by decide⟩),
   opAt 539 (.Dup ⟨6, by decide⟩), pushAt 540 1 32, opAt 541 .SUB,
   pushAt 542 1 3, opAt 543 .SHL, opAt 544 .SHL, pushAt 545 2 6144,
   opAt 546 .MSTORE, opAt 547 (.Dup ⟨5, by decide⟩), pushAt 548 2 6144,
   opAt 549 .RETURN]

def outputShift (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft
    ((32 : UInt256) - UInt256.ofNat (modulusSize input)) (UInt256.ofNat 3)

def outputWord (input : ByteArray) (acc : UInt256) : UInt256 :=
  UInt256.shiftLeft acc (outputShift input)

/-- The return buffer sits on top of the window table, not on empty memory. -/
def outputMemory (input : ByteArray) (base acc : UInt256) : ByteArray :=
  MachineState.writeBytes (tableMem input base 16)
    (Data.Bytes.natToBytesPadded (outputWord input acc).toNat 32) 6144

def wordFinalState (input : ByteArray) (base acc : UInt256) : State :=
  let start := wordExitState input base acc
  let storedWords := start.activeWordsAfterUInt256 6144 32
  { start with
    pc := UInt256.ofNat 688
    stack := [acc, base] ++ wordFrame input
    memory := outputMemory input base acc
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter storedWords.toNat
      6144 (modulusSize input))
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory input base acc) 6144
      (modulusSize input) }

@[simp] private theorem exitPCs (i : Nat) (hi : 536 ≤ i) (hii : i ≤ 549) :
    Artifact.submissionArtifact.instructionPC i =
      ([669,670,671,672,673,675,676,678,679,680,683,684,685,688])[i - 536]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run_expFinishTail (input : ByteArray) (base acc : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock expFinishTailPath
      (wordExitState input base acc) = some (wordFinalState input base acc) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have h6144 : (6144 : UInt256).toNat = 6144 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have h3Word : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have hm256 : modulusSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm256
  have hmmodLiteral : modulusSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        modulusSize input := by
    norm_num at hmmod ⊢
    exact hmmod
  simp (config := { maxSteps := 400000 })
    [expFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      wordExitState, wordFinalState, outputMemory, outputWord, outputShift,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, exitPCs,
      List.exchange, hsub, hshift, h6144, h32, h3Word, hm256, hmmod,
      hmmodLiteral, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

def gasSteps_expFinish (input : ByteArray) (base acc : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (wordExitState input base acc)
      (wordFinalState input base acc) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka expFinishTailPath rfl rfl
      (run_expFinishTail input base acc hvalid hword) rfl
      deployAddress_not_precompile

@[simp] theorem wordFinalState_isDone (input : ByteArray) (base acc : UInt256) :
    (wordFinalState input base acc).isDone = true := by
  rfl

/-- The whole non-zero-modulus word path, entry to `RETURN`. -/
def gasSteps_wordTotal (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (wordFinalState input (wordBase input) (wordResult input)) :=
  (gasSteps_wordEntry input hvalid hmsize hword hmodpos).trans
    (gasSteps_expFinish input (wordBase input) (wordResult input) hvalid hword)

end Challenge.Modexp.Submission.Proofs.Bytecode.WordExit

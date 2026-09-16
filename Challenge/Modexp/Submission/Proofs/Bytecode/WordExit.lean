import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# One-word MODEXP exit

The completed exponent residue is left-padded into one EVM word, stored at
memory `0x1800`, and returned with the declared modulus width.  This module
certifies that final control-flow and memory transition.
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
  [opAt 151 .JUMPDEST,
   opAt 152 .POP,
   pushAt 153 0 0,
   opAt 154 .MSTORE,
   opAt 155 (.Dup ⟨4, by decide⟩),
   opAt 156 (.Dup ⟨0, by decide⟩),
   pushAt 157 2 32,
   opAt 158 .SUB,
   opAt 159 .RETURN]

def expFinishDispatchState (input : ByteArray) (acc base : UInt256) : State :=
  { expLoopState input (exponentSize input) acc base with pc := UInt256.ofNat 222 }

def outputShift (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft
    ((32 : UInt256) - UInt256.ofNat (modulusSize input)) (UInt256.ofNat 3)

def outputWord (input : ByteArray) (acc : UInt256) : UInt256 :=
  UInt256.shiftLeft acc (outputShift input)

def outputOffset (input : ByteArray) : Nat :=
  32 - modulusSize input

def outputMemory (_input : ByteArray) (acc : UInt256) : ByteArray :=
  MachineState.writeBytes ByteArray.empty
    (Data.Bytes.natToBytesPadded acc.toNat 32) 0

def wordFinalState (input : ByteArray) (acc base : UInt256) : State :=
  let start := expLoopState input (exponentSize input) acc base
  let storedWords := start.activeWordsAfterUInt256 0 32
  { start with
    pc := UInt256.ofNat 232
    stack := [base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input
    memory := outputMemory input acc
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter storedWords.toNat
      (outputOffset input) (modulusSize input))
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory input acc) (outputOffset input)
      (modulusSize input) }

@[simp] private theorem exitPCs (i : Nat)
    (hi : 151 ≤ i) (hii : i ≤ 164) :
    Artifact.submissionArtifact.instructionPC i =
      ([222,223,224,225,226,227,228,231,232,233,234,235,236,237] : List Nat)[i - 151]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] private theorem jump669 :
    Decode.isValidJumpDest submissionBytecode 222 = true :=
  Artifact.isValidJumpDest_index 151 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_expFinishGuard (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expGuardPath
      (expLoopState input (exponentSize input) acc base) =
        some (expFinishDispatchState input acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have he256 : exponentSize input < 2 ^ 256 := by omega
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he256
  have heq : UInt256.eq (UInt256.ofNat (exponentSize input))
      (UInt256.ofNat (exponentSize input)) = UInt256.ofNat 1 := by
    simp [UInt256.eq]
  have h669 : (222 : UInt256).toNat = 222 := by decide
  have h669Word : (222 : UInt256) = UInt256.ofNat 222 := by decide
  simp (config := { maxSteps := 150000 })
    [expGuardPath, Word.opAt, Word.pushAt, Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expLoopState, expFinishDispatchState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
      he256, hemod, heq, h669, h669Word, jump669]

set_option linter.unusedSimpArgs false in
theorem run_expFinishTail (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock expFinishTailPath
      (expFinishDispatchState input acc base) =
        some (wordFinalState input acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroRawNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hm256 : modulusSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm256
  have hmmodLiteral : modulusSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        modulusSize input := by
    norm_num at hmmod ⊢
    exact hmmod
  have hoff256 : outputOffset input < 2 ^ 256 := by
    unfold outputOffset
    omega
  have hoffmod : outputOffset input % 2 ^ 256 = outputOffset input :=
    Nat.mod_eq_of_lt hoff256
  have hwrappedOffset :
      (2 ^ 256 + 32 - modulusSize input) % 2 ^ 256 =
        outputOffset input := by
    have hsum :
        2 ^ 256 + 32 - modulusSize input =
          2 ^ 256 + outputOffset input := by
      unfold outputOffset
      omega
    rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_mod, hoffmod]
  have hwrappedOffsetLiteral :
      (115792089237316195423570985008687907853269984665640564039457584007913129639968 -
          modulusSize input) %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      outputOffset input := by
    norm_num at hwrappedOffset ⊢
    exact hwrappedOffset
  have hstored : MachineState.activeWordsAfter 0 0 32 = 1 := by decide
  have hreturned : MachineState.activeWordsAfter 1
      (outputOffset input) (modulusSize input) = 1 := by
    unfold outputOffset MachineState.activeWordsAfter
    split
    · rfl
    · next hnonzero =>
      have hdiv : (32 - modulusSize input + modulusSize input - 1) / 32 = 0 := by
        omega
      dsimp
      rw [hdiv]
      decide
  simp (config := { maxSteps := 350000 })
    [expFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expFinishDispatchState, expLoopState, wordFinalState, outputMemory,
      outputOffset, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, exitPCs,
      List.exchange, hsub, h0, hzeroRawNat, h32, hm256, hmmod,
      hmmodLiteral, hwrappedOffsetLiteral, hoffmod, hstored, hreturned,
      State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

def gasSteps_expFinish (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps
      (expLoopState input (exponentSize input) acc base)
      (wordFinalState input acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka expGuardPath rfl rfl
        (run_expFinishGuard input acc base hvalid) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka expFinishTailPath rfl rfl
        (run_expFinishTail input acc base hvalid hword) rfl
        deployAddress_not_precompile)

@[simp] theorem wordFinalState_isDone (input : ByteArray) (acc base : UInt256) :
    (wordFinalState input acc base).isDone = true := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WordExit

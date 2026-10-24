import Challenge.Modexp.Submission.Proofs.Bytecode.WordExitGuard
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 40000
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
open YulEvmCompiler WindowNibbleKernel WindowTwentyOneBinding

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def expFinishTailProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .push 1 32, .op .SUB,
   .push 1 3, .op .SHL, .op .SHL, .push 0 0, .op .MSTORE,
   .op (.Dup ⟨5, by decide⟩), .push 0 0, .op .RETURN]

def expFinishTailBlock : Block Artifact.submissionArtifact .Osaka 5554 expFinishTailProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 4439 14 5554 expFinishTailProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

def expFinishDispatchState (input : ByteArray) (acc base : UInt256) : State :=
  { expLoopState input (exponentSize input) acc base with pc := UInt256.ofNat 5554 }

def outputShift (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft
    ((32 : UInt256) - UInt256.ofNat (modulusSize input)) (UInt256.ofNat 3)

def outputWord (input : ByteArray) (acc : UInt256) : UInt256 :=
  UInt256.shiftLeft acc (outputShift input)

def outputMemory (input : ByteArray) (acc : UInt256) : ByteArray :=
  MachineState.writeBytes ByteArray.empty
    (Data.Bytes.natToBytesPadded (outputWord input acc).toNat 32) 0

def wordFinalState (input : ByteArray) (acc base : UInt256) : State :=
  let start := expLoopState input (exponentSize input) acc base
  let storedWords := start.activeWordsAfterUInt256 0 32
  { start with
    pc := UInt256.ofNat 5569
    stack := [acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input
    memory := outputMemory input acc
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter storedWords.toNat
      0 (modulusSize input))
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory input acc) 0
      (modulusSize input) }

@[simp] private theorem jump669 :
    Decode.isValidJumpDest submissionBytecode 5554 = true := Word.jump669

def expFinishGuardBlock : Block Artifact.submissionArtifact .Osaka 194 WordExitGuard.program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 125 6 194 WordExitGuard.program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

theorem run_expFinishGuard (input : ByteArray) (acc base : UInt256)
    (_hvalid : ValidInput input) :
    runInstructions WordExitGuard.program
      (expLoopState input (exponentSize input) acc base) =
        some (expFinishDispatchState input acc base) := by
  have h := WordExitGuard.run (nonzeroState input)
    (UInt256.ofNat (exponentSize input)) acc base
    (UInt256.ofNat (modulusValue input)) (UInt256.ofNat (baseSize input))
    ([UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input)
    (by simp [callerRest]) Word.jump669
  simpa only [WordExitGuard.frame, expLoopState, expFinishDispatchState,
    List.cons_append, List.nil_append] using h

set_option linter.unusedSimpArgs false in
theorem run_expFinishTail (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    runInstructions expFinishTailProgram
      (expFinishDispatchState input acc base) =
        some (wordFinalState input acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroRawNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
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
  have hactiveMax : max 1 ((modulusSize input - 1) / 32 + 1) =
      (modulusSize input - 1) / 32 + 1 := Nat.max_eq_right (by omega)
  simp (config := { maxSteps := 350000 })
    [expFinishTailProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      expFinishDispatchState, expLoopState, wordFinalState, outputMemory,
      outputWord, outputShift, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, hsub, hshift, h0, hzeroRawNat, h32, h3Word, hm256, hmmod,
      hmmodLiteral, hactiveMax, State.activeWordsAfterUInt256,
      MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

def gasSteps_expFinish (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps
      (expLoopState input (exponentSize input) acc base)
      (wordFinalState input acc base) := by
  let env : Environment Artifact.submissionArtifact .Osaka
      (expFinishDispatchState input acc base) :=
    { sizeBound := by
        change submissionBytecode.size < 2 ^ 256
        rw [submissionBytecode_size]
        decide
      code := rfl
      forkEq := rfl
      running := rfl
      noPrecompile := deployAddress_not_precompile }
  exact (expFinishGuardBlock.steps (s := expLoopState input (exponentSize input) acc base)
      (env.transfer rfl rfl) rfl
      (run_expFinishGuard input acc base hvalid)).trans
    (expFinishTailBlock.steps env rfl (run_expFinishTail input acc base hvalid hword))

@[simp] theorem wordFinalState_isDone (input : ByteArray) (acc base : UInt256) :
    (wordFinalState input acc base).isDone = true := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WordExit

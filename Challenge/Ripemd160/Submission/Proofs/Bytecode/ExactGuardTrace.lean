import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardPaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardTrace
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160 Challenge.EvmProof
open ExactGuardData ExactGuardLogic ExactGuardState ExactGuardPaths

private theorem loopDest_valid :
    Decode.isValidJumpDest submissionBytecode 5336 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 2934 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 2934 = 5336 := by
    rw [StackPC.instructionPC_eq_byteLength]
    decide
  rw [hp] at h
  exact h

theorem run_prelude (input : ByteArray) :
    Stepper.runLocatedBlock preludePath (entryState input) = some (loopState input 0 (acc input 0)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [preludePath, entryState, atPC, loopState, acc, acc0, fullWord,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check0 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 0 (acc input 0)) =
      some (loopState input 32 (acc input 1)) := by
  have hacc : acc input 1 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 0) fullWord)
        (acc input 0) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check1 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 32 (acc input 1)) =
      some (loopState input 64 (acc input 2)) := by
  have hacc : acc input 2 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 32) fullWord)
        (acc input 1) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check2 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 64 (acc input 2)) =
      some (loopState input 96 (acc input 3)) := by
  have hacc : acc input 3 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 64) fullWord)
        (acc input 2) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check3 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 96 (acc input 3)) =
      some (loopState input 128 (acc input 4)) := by
  have hacc : acc input 4 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 96) fullWord)
        (acc input 3) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check4 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 128 (acc input 4)) =
      some (loopState input 160 (acc input 5)) := by
  have hacc : acc input 5 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 128) fullWord)
        (acc input 4) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check5 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 160 (acc input 5)) =
      some (loopState input 192 (acc input 6)) := by
  have hacc : acc input 6 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 160) fullWord)
        (acc input 5) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check6 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 192 (acc input 6)) =
      some (loopState input 224 (acc input 7)) := by
  have hacc : acc input 7 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 192) fullWord)
        (acc input 6) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check7 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 224 (acc input 7)) =
      some (loopState input 256 (acc input 8)) := by
  have hacc : acc input 8 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 224) fullWord)
        (acc input 7) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check8 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 256 (acc input 8)) =
      some (loopState input 288 (acc input 9)) := by
  have hacc : acc input 9 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 256) fullWord)
        (acc input 8) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check9 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 288 (acc input 9)) =
      some (loopState input 320 (acc input 10)) := by
  have hacc : acc input 10 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 288) fullWord)
        (acc input 9) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check10 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 320 (acc input 10)) =
      some (loopState input 352 (acc input 11)) := by
  have hacc : acc input 11 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 320) fullWord)
        (acc input 10) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check11 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 352 (acc input 11)) =
      some (loopState input 384 (acc input 12)) := by
  have hacc : acc input 12 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 352) fullWord)
        (acc input 11) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check12 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 384 (acc input 12)) =
      some (loopState input 416 (acc input 13)) := by
  have hacc : acc input 13 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 384) fullWord)
        (acc input 12) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check13 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 416 (acc input 13)) =
      some (loopState input 448 (acc input 14)) := by
  have hacc : acc input 14 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 416) fullWord)
        (acc input 13) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check14 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 448 (acc input 14)) =
      some (loopState input 480 (acc input 15)) := by
  have hacc : acc input 15 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 448) fullWord)
        (acc input 14) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check15 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 480 (acc input 15)) =
      some (loopState input 512 (acc input 16)) := by
  have hacc : acc input 16 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 480) fullWord)
        (acc input 15) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check16 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 512 (acc input 16)) =
      some (loopState input 544 (acc input 17)) := by
  have hacc : acc input 17 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 512) fullWord)
        (acc input 16) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check17 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 544 (acc input 17)) =
      some (loopState input 576 (acc input 18)) := by
  have hacc : acc input 18 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 544) fullWord)
        (acc input 17) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check18 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 576 (acc input 18)) =
      some (loopState input 608 (acc input 19)) := by
  have hacc : acc input 19 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 576) fullWord)
        (acc input 18) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check19 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 608 (acc input 19)) =
      some (loopState input 640 (acc input 20)) := by
  have hacc : acc input 20 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 608) fullWord)
        (acc input 19) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check20 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 640 (acc input 20)) =
      some (loopState input 672 (acc input 21)) := by
  have hacc : acc input 21 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 640) fullWord)
        (acc input 20) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check21 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 672 (acc input 21)) =
      some (loopState input 704 (acc input 22)) := by
  have hacc : acc input 22 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 672) fullWord)
        (acc input 21) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check22 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 704 (acc input 22)) =
      some (loopState input 736 (acc input 23)) := by
  have hacc : acc input 23 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 704) fullWord)
        (acc input 22) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check23 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 736 (acc input 23)) =
      some (loopState input 768 (acc input 24)) := by
  have hacc : acc input 24 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 736) fullWord)
        (acc input 23) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check24 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 768 (acc input 24)) =
      some (loopState input 800 (acc input 25)) := by
  have hacc : acc input 25 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 768) fullWord)
        (acc input 24) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check25 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 800 (acc input 25)) =
      some (loopState input 832 (acc input 26)) := by
  have hacc : acc input 26 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 800) fullWord)
        (acc input 25) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check26 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 832 (acc input 26)) =
      some (loopState input 864 (acc input 27)) := by
  have hacc : acc input 27 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 832) fullWord)
        (acc input 26) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check27 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 864 (acc input 27)) =
      some (loopState input 896 (acc input 28)) := by
  have hacc : acc input 28 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 864) fullWord)
        (acc input 27) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check28 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 896 (acc input 28)) =
      some (loopState input 928 (acc input 29)) := by
  have hacc : acc input 29 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 896) fullWord)
        (acc input 28) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check29 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 928 (acc input 29)) =
      some (loopState input 960 (acc input 30)) := by
  have hacc : acc input 30 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 928) fullWord)
        (acc input 29) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_check30 (input : ByteArray) :
    Stepper.runLocatedBlock loopPath (loopState input 960 (acc input 30)) =
      some (loopExitState input 992 (acc input 31)) := by
  have hacc : acc input 31 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 960) fullWord)
        (acc input 30) := rfl
  rw [hacc]
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [loopPath, loopState, loopExitState,
    fullWord, loopDest_valid, UInt256.isTrue, UInt256.isZero, UInt256.eq,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_exit (input : ByteArray) :
    Stepper.runLocatedBlock exitPath (loopExitState input 992 (acc input 31)) = some (accState input 5360 (acc input 31)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [exitPath, loopExitState, accState,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_tail (input : ByteArray) :
    Stepper.runLocatedBlock tailPath (accState input 5360 (acc input 31)) = some (accState input 5399 (tailAcc input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [tailPath, accState, tailAcc, fullWord, tailWord,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_cleanup (input : ByteArray) :
    Stepper.runLocatedBlock cleanupPath (accState input 5399 (tailAcc input)) = some (diffState input 5401 (guardDiff input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [cleanupPath, accState, diffState, ← tailAcc_eq_guardDiff input,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

private def sound {s t : State}
    (path : List (Stepper.Located Artifact.submissionArtifact .Osaka))
    (h : Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path
    hcode hfork h hrun hnp

def gasSteps_scan (input : ByteArray) :
    GasSteps (entryState input) (diffState input 5401 (guardDiff input)) :=
  (sound preludePath (run_prelude input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check0 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check1 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check2 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check3 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check4 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check5 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check6 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check7 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check8 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check9 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check10 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check11 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check12 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check13 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check14 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check15 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check16 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check17 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check18 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check19 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check20 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check21 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check22 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check23 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check24 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check25 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check26 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check27 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check28 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check29 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound loopPath (run_check30 input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound exitPath (run_exit input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound tailPath (run_tail input) rfl rfl rfl deployAddress_not_precompile).trans
    ((sound cleanupPath (run_cleanup input) rfl rfl rfl deployAddress_not_precompile)))))))))))))))))))))))))))))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardTrace

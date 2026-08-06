import Challenge.Blake2f.Reference.Proofs.Bytecode.Artifact
import Challenge.Blake2f.ProofSupport.InitialState
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Direct trace of the compiled `loadLE64` helper

The trace is parameterized by calldata offset, return destination, and stack
tail, so the two main decoding loops and the two counter loads can reuse it.
-/

namespace Challenge.Blake2f.Reference.Proofs.Bytecode.LoadLE64

open Challenge.Blake2f
open EvmSemantics
open EvmSemantics.EVM

def initPath := Artifact.locatedPath [2, 3, 4, 5]
def testPath := Artifact.locatedPath [6, 7, 8, 9, 10, 11, 12]
def bodyPath := Artifact.locatedPath
  [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
   24, 25, 26, 27, 28, 29, 30]
def exitPath := Artifact.locatedPath [31, 32, 33, 34, 35, 36]

/-- Exact EVM accumulator after `i` little-endian bytes. -/
def accumulator (inputWord : UInt256) : Nat → UInt256
  | 0 => ⟨0⟩
  | i + 1 =>
      UInt256.lor (accumulator inputWord i)
        (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat i) inputWord)
          (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 3)))

def loopState (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 8
    stack := [UInt256.ofNat i,
      MachineState.readWord s.executionEnv.calldata offset.toNat,
      offset,
      accumulator (MachineState.readWord s.executionEnv.calldata offset.toNat) i,
      returnDest] ++ tail }

def finalState (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := accumulator
      (MachineState.readWord s.executionEnv.calldata offset.toNat) 8 :: tail }

theorem run_init (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock initPath
      ({ s with
        pc := UInt256.ofNat 4
        stack := [offset, ⟨0⟩, returnDest] ++ tail }) =
        some (loopState s offset returnDest tail 0) := by
  have hcap3 : tail.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : tail.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hzeroStruct : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      initPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, accumulator, htail, hcap3, hcap4, hzeroStruct, hrun,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat]

theorem run_test_continue (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock testPath
        (loopState s offset returnDest tail i) =
      some { loopState s offset returnDest tail i with
        pc := UInt256.ofNat 18 } := by
  have hcap5 : tail.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap6 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap7 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hito : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpc11 : UInt256.ofNat 9 + UInt256.ofNat 2 = UInt256.ofNat 11 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 9) (b := 2) (by norm_num)
  have hpc17 : UInt256.ofNat 14 + UInt256.ofNat 3 = UInt256.ofNat 17 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 14) (b := 3) (by norm_num)
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      testPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, htail, hcap5, hcap6, hcap7, hi, hito, hrun, hpc11, hpc17,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_test_exit (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock testPath
        (loopState s offset returnDest tail 8) =
      some { loopState s offset returnDest tail 8 with
        pc := UInt256.ofNat 40 } := by
  have hcap5 : tail.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap6 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap7 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h40 := Artifact.referenceArtifact.isValidJumpDest_index 31 (by rfl)
  have h40' : Decode.isValidJumpDest referenceBytecode 40 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h40
  have hpc11 : UInt256.ofNat 9 + UInt256.ofNat 2 = UInt256.ofNat 11 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 9) (b := 2) (by norm_num)
  have hpc17 : UInt256.ofNat 14 + UInt256.ofNat 3 = UInt256.ofNat 17 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 14) (b := 3) (by norm_num)
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      testPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, htail, hcap5, hcap6, hcap7, hrun, hcode, h40', hpc11, hpc17,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.lt, UInt256.isZero, UInt256.isTrue]

theorem run_body (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock bodyPath
        { loopState s offset returnDest tail i with pc := UInt256.ofNat 18 } =
      some (loopState s offset returnDest tail (i + 1)) := by
  have h8 := Artifact.referenceArtifact.isValidJumpDest_index 6 (by rfl)
  have h8' : Decode.isValidJumpDest referenceBytecode 8 = true := by
    simpa [Artifact.referenceArtifact, Challenge.EvmProof.ProgramArtifact.instructionPC,
      Artifact.referenceInstructions] using h8
  have hcap5 : tail.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap6 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap7 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap8 : tail.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hito : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hi1 : i + 1 < 2 ^ 256 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hi1
  have hpc24 : UInt256.ofNat 22 + UInt256.ofNat 2 = UInt256.ofNat 24 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 22) (b := 2) (by norm_num)
  have hpc32 : UInt256.ofNat 30 + UInt256.ofNat 2 = UInt256.ofNat 32 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 30) (b := 2) (by norm_num)
  have hpc39 : UInt256.ofNat 36 + UInt256.ofNat 3 = UInt256.ofNat 39 := by
    simpa using Challenge.EvmProof.Word.ofNat_add_ofNat
      (a := 36) (b := 3) (by norm_num)
  let inputWord := MachineState.readWord s.executionEnv.calldata offset.toNat
  let old := accumulator inputWord i
  let next := UInt256.lor old
    (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat i) inputWord)
      (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 3)))
  have hexchange :
      (next :: UInt256.ofNat i :: inputWord :: offset :: old :: returnDest :: tail).exchange
          0 4 =
        some (old :: UInt256.ofNat i :: inputWord :: offset :: next :: returnDest :: tail) := by
    rfl
  have hswapIncrement :
      (UInt256.ofNat (i + 1) :: UInt256.ofNat i :: inputWord :: offset ::
          next :: returnDest :: tail).exchange 0 1 =
        some (UInt256.ofNat i :: UInt256.ofNat (i + 1) :: inputWord :: offset ::
          next :: returnDest :: tail) := by
    rfl
  simp (config := { maxSteps := 300000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      bodyPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, accumulator, htail, hcap5, hcap6, hcap7, hcap8,
      hi, hito, hadd, hpc24, hpc32, hpc39, inputWord, old, next,
      hexchange, hswapIncrement, hrun, hcode, h8',
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

theorem run_exit (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock exitPath
        { loopState s offset returnDest tail 8 with pc := UInt256.ofNat 40 } =
      some (finalState s offset returnDest tail) := by
  have hcap5 : tail.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : tail.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap3 : tail.length + 1 + 1 + 1 < 1024 := by omega
  have hcap2 : tail.length + 1 + 1 < 1024 := by omega
  let value := accumulator
    (MachineState.readWord s.executionEnv.calldata offset.toNat) 8
  have hexchange : (value :: returnDest :: tail).exchange 0 1 =
      some (returnDest :: value :: tail) := by rfl
  simp (config := { maxSteps := 200000 })
    [Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      exitPath, Artifact.locatedPath, Artifact.located,
      Challenge.EvmProof.Stepper.Located.ofIndex,
      Artifact.referenceArtifact, Artifact.referenceInstructions,
      Challenge.EvmProof.ProgramArtifact.instructionPC,
      loopState, finalState, htail, hcap2, hcap3, hcap4, hcap5, value, hexchange,
      hrun, hcode, hreturn,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat,
      UInt256.isTrue]

private def gasSteps_block
    (path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka))
    {a b : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path a = some b)
    (hcode : a.executionEnv.code = referenceBytecode)
    (hfork : a.fork = .Osaka) (hrun : a.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig a.executionEnv.precompileConfig
      a.executionEnv.fork a.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps a b := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path
  · exact hcode
  · exact hfork
  · exact hresult
  · exact hrun
  · exact hnp

private def gasSteps_iteration (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (i : Nat) (hi : i < 8)
    (htail : tail.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (loopState s offset returnDest tail i)
      (loopState s offset returnDest tail (i + 1)) := by
  have gtest := gasSteps_block testPath
    (run_test_continue s offset returnDest tail i hi htail hrun)
    (by simpa [loopState] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (by simpa [loopState] using hrun)
    (by simpa [loopState] using hnp)
  have gbody := gasSteps_block bodyPath
    (run_body s offset returnDest tail i hi htail hrun hcode)
    (by simpa [loopState] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (by simpa [loopState] using hrun)
    (by simpa [loopState] using hnp)
  exact gtest.trans gbody

def gasSteps (s : State) (offset returnDest : UInt256)
    (tail : List UInt256) (htail : tail.length < 1016)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest referenceBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      { s with
        pc := UInt256.ofNat 4
        stack := [offset, ⟨0⟩, returnDest] ++ tail }
      (finalState s offset returnDest tail) := by
  let entry : State :=
    { s with
      pc := UInt256.ofNat 4
      stack := [offset, ⟨0⟩, returnDest] ++ tail }
  have ginit := gasSteps_block initPath
    (run_init s offset returnDest tail htail hrun)
    (by simpa [entry] using hcode)
    (by simpa [entry, State.fork] using hfork)
    (by simpa [entry] using hrun)
    (by simpa [entry] using hnp)
  have gloop : Challenge.EvmProof.GasSteps
      (loopState s offset returnDest tail 0)
      (loopState s offset returnDest tail 8) :=
    Challenge.EvmProof.GasSteps.iterateBounded (count := 8)
      (I := loopState s offset returnDest tail)
      (fun i hi => gasSteps_iteration s offset returnDest tail i hi htail
        hcode hfork hrun hnp)
  have gtest := gasSteps_block testPath
    (run_test_exit s offset returnDest tail htail hrun hcode)
    (by simpa [loopState] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (by simpa [loopState] using hrun)
    (by simpa [loopState] using hnp)
  have gexit := gasSteps_block exitPath
    (run_exit s offset returnDest tail htail hrun hcode hreturn)
    (by simpa [loopState] using hcode)
    (by simpa [loopState, State.fork] using hfork)
    (by simpa [loopState] using hrun)
    (by simpa [loopState] using hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (ginit.trans (gloop.trans (gtest.trans gexit))) rfl rfl

end Challenge.Blake2f.Reference.Proofs.Bytecode.LoadLE64

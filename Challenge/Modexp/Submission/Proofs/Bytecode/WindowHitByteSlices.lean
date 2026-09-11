import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowForwardDefs

set_option warningAsError true
set_option maxRecDepth 40000

/-!
# Generated-artifact byte slices

This is the only module that binds the reusable four-byte loop model to the
generated instruction list.  The first three paths have forty-eight instructions; the final path has
forty-seven and consumes the word before the loop-advance boundary.  Keeping the four equalities separate bounds regeneration
failures to one concrete slice.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices

open Challenge.EvmProof.Stepper
open EvmSemantics
open EvmSemantics.EVM
open WindowByteKernel
open WindowNibbleKernel
open WindowNibbleForward

def locatedSlice (start count : Nat)
    (hbound : start + count ≤ Artifact.submissionInstructions.length) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  List.ofFn fun offset : Fin count =>
    Located.ofIndex Artifact.allWellFormed
      ⟨start + offset.val, by
        change start + count ≤ Artifact.submissionArtifact.instructions.length at hbound
        omega⟩

def byte0Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 1977 48 (by rw [Artifact.submissionInstructions_count]; omega)

def byte1Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2025 48 (by rw [Artifact.submissionInstructions_count]; omega)

def byte2Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2073 48 (by rw [Artifact.submissionInstructions_count]; omega)

def byte3Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2121 47 (by rw [Artifact.submissionInstructions_count]; omega)

def byteStartIndex (byte : Fin 4) : Nat := 1975 + 48 * byte.val

def byteStartPC (byte : Fin 4) : Nat :=
  [2819, 2871, 2924, 2977][byte.val]!

def highPrepPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte) (if byte.val = 3 then 5 else 6) (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    split <;> omega)

def highSquareLookupPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + if byte.val = 3 then 5 else 6) 19 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    split <;> omega)

def lowPrepPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + if byte.val = 3 then 24 else 25) 0 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    split <;> omega)

def lowSquareLookupPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + if byte.val = 3 then 24 else 25) 23 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    split <;> omega)

def finishPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + if byte.val = 3 then 47 else 48) 0 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    split <;> omega)

def segmentedBytePath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  highPrepPath byte ++ highSquareLookupPath byte ++
    lowPrepPath byte ++ lowSquareLookupPath byte ++ finishPath byte

/-! These are the four regeneration-sensitive obligations. -/

theorem byte0_instructions :
    byte0Path.map (fun located => located.instruction) = forwardByteProgram 0 := by
  rfl

theorem byte1_instructions :
    byte1Path.map (fun located => located.instruction) = forwardByteProgram 1 := by
  rfl

theorem byte2_instructions :
    byte2Path.map (fun located => located.instruction) = forwardByteProgram 2 := by
  rfl

theorem byte3_instructions :
    byte3Path.map (fun located => located.instruction) = forwardFinalByteProgram := by
  rfl

theorem highPrep_instructions (byte : Fin 4) :
    (highPrepPath byte).map (fun located => located.instruction) =
      (if byte.val = 3 then finalHighPrepProgram else highPrepProgram byte.val) := by
  fin_cases byte <;> rfl

theorem highSquareLookup0_instructions :
    (highSquareLookupPath 0).map (fun located => located.instruction) =
      forwardHighSquareLookupProgram := by
  rfl

theorem highSquareLookup1_instructions :
    (highSquareLookupPath 1).map (fun located => located.instruction) =
      forwardHighSquareLookupProgram := by
  rfl

theorem highSquareLookup2_instructions :
    (highSquareLookupPath 2).map (fun located => located.instruction) =
      forwardHighSquareLookupProgram := by
  rfl

theorem highSquareLookup3_instructions :
    (highSquareLookupPath 3).map (fun located => located.instruction) =
      forwardFinalHighSquareLookupProgram := by
  rfl

theorem highSquareLookup_instructions (byte : Fin 4) :
    (highSquareLookupPath byte).map (fun located => located.instruction) =
      (if byte.val = 3 then forwardFinalHighSquareLookupProgram else forwardHighSquareLookupProgram) := by
  fin_cases byte
  · exact highSquareLookup0_instructions
  · exact highSquareLookup1_instructions
  · exact highSquareLookup2_instructions
  · exact highSquareLookup3_instructions

theorem lowPrep_instructions (byte : Fin 4) :
    (lowPrepPath byte).map (fun located => located.instruction) =
      forwardLowPrepProgram := by
  fin_cases byte <;> rfl

theorem lowSquareLookup0_instructions :
    (lowSquareLookupPath 0).map (fun located => located.instruction) =
      forwardLowSquareLookupProgram := by
  rfl

theorem lowSquareLookup1_instructions :
    (lowSquareLookupPath 1).map (fun located => located.instruction) =
      forwardLowSquareLookupProgram := by
  rfl

theorem lowSquareLookup2_instructions :
    (lowSquareLookupPath 2).map (fun located => located.instruction) =
      forwardLowSquareLookupProgram := by
  rfl

theorem lowSquareLookup3_instructions :
    (lowSquareLookupPath 3).map (fun located => located.instruction) =
      forwardFinalLowSquareLookupProgram := by
  rfl

theorem lowSquareLookup_instructions (byte : Fin 4) :
    (lowSquareLookupPath byte).map (fun located => located.instruction) =
      (if byte.val = 3 then forwardFinalLowSquareLookupProgram else forwardLowSquareLookupProgram) := by
  fin_cases byte
  · exact lowSquareLookup0_instructions
  · exact lowSquareLookup1_instructions
  · exact lowSquareLookup2_instructions
  · exact lowSquareLookup3_instructions

theorem finish_instructions (byte : Fin 4) :
    (finishPath byte).map (fun located => located.instruction) =
      finishProgram := by
  fin_cases byte <;> rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices

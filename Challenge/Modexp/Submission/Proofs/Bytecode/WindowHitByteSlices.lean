import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteDefs

set_option warningAsError true
set_option maxRecDepth 40000

/-!
# Generated-artifact byte slices

This is the only module that binds the reusable four-byte loop model to the
generated instruction list.  Each path has exactly sixty-two instruction
certificates.  Keeping the four equalities separate bounds regeneration
failures to one concrete slice.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices

open Challenge.EvmProof.Stepper
open EvmSemantics
open EvmSemantics.EVM
open WindowByteKernel
open WindowNibbleKernel

def locatedSlice (start count : Nat)
    (hbound : start + count ≤ Artifact.submissionInstructions.length) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  List.ofFn fun offset : Fin count =>
    Located.ofIndex Artifact.allWellFormed
      ⟨start + offset.val, by
        change start + count ≤ Artifact.submissionArtifact.instructions.length at hbound
        omega⟩

def byte0Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 1936 62 (by rw [Artifact.submissionInstructions_count]; omega)

def byte1Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 1998 62 (by rw [Artifact.submissionInstructions_count]; omega)

def byte2Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2060 62 (by rw [Artifact.submissionInstructions_count]; omega)

def byte3Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2122 62 (by rw [Artifact.submissionInstructions_count]; omega)

def byteStartIndex (byte : Fin 4) : Nat := 1963 + 62 * byte.val

def byteStartPC (byte : Fin 4) : Nat :=
  [3203, 3287, 3372, 3457][byte.val]!

def highPrepPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte) 6 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def highSquareLookupPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 6) 25 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def lowPrepPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 31) 4 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def lowSquareLookupPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 35) 25 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def finishPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 60) 2 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def segmentedBytePath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  highPrepPath byte ++ highSquareLookupPath byte ++
    lowPrepPath byte ++ lowSquareLookupPath byte ++ finishPath byte

/-! These are the four regeneration-sensitive obligations. -/

theorem byte0_instructions :
    byte0Path.map (fun located => located.instruction) = byteProgram 0 := by
  rfl

theorem byte1_instructions :
    byte1Path.map (fun located => located.instruction) = byteProgram 1 := by
  rfl

theorem byte2_instructions :
    byte2Path.map (fun located => located.instruction) = byteProgram 2 := by
  rfl

theorem byte3_instructions :
    byte3Path.map (fun located => located.instruction) = byteProgram 3 := by
  rfl

theorem highPrep_instructions (byte : Fin 4) :
    (highPrepPath byte).map (fun located => located.instruction) =
      highPrepProgram byte.val := by
  fin_cases byte <;> rfl

theorem highSquareLookup0_instructions :
    (highSquareLookupPath 0).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem highSquareLookup1_instructions :
    (highSquareLookupPath 1).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem highSquareLookup2_instructions :
    (highSquareLookupPath 2).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem highSquareLookup3_instructions :
    (highSquareLookupPath 3).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem highSquareLookup_instructions (byte : Fin 4) :
    (highSquareLookupPath byte).map (fun located => located.instruction) =
      squareLookupProgram := by
  fin_cases byte
  · exact highSquareLookup0_instructions
  · exact highSquareLookup1_instructions
  · exact highSquareLookup2_instructions
  · exact highSquareLookup3_instructions

theorem lowPrep_instructions (byte : Fin 4) :
    (lowPrepPath byte).map (fun located => located.instruction) =
      lowPrepProgram := by
  fin_cases byte <;> rfl

theorem lowSquareLookup0_instructions :
    (lowSquareLookupPath 0).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem lowSquareLookup1_instructions :
    (lowSquareLookupPath 1).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem lowSquareLookup2_instructions :
    (lowSquareLookupPath 2).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem lowSquareLookup3_instructions :
    (lowSquareLookupPath 3).map (fun located => located.instruction) =
      squareLookupProgram := by
  rfl

theorem lowSquareLookup_instructions (byte : Fin 4) :
    (lowSquareLookupPath byte).map (fun located => located.instruction) =
      squareLookupProgram := by
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

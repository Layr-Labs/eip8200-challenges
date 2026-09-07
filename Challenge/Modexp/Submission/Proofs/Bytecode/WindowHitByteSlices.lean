import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteDefs

set_option warningAsError true
set_option maxRecDepth 40000

/-!
# Generated-artifact byte slices

This is the only module that binds the reusable four-byte loop model to the
generated instruction list.  Each path has exactly eighty instruction
certificates.  Keeping the four equalities separate bounds regeneration
failures to one concrete slice.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices

open Challenge.EvmProof.Stepper
open EvmSemantics
open EvmSemantics.EVM
open WindowByteKernel

def locatedSlice (start count : Nat)
    (hbound : start + count ≤ Artifact.submissionInstructions.length) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  List.ofFn fun offset : Fin count =>
    Located.ofIndex Artifact.allWellFormed
      ⟨start + offset.val, by
        change start + count ≤ Artifact.submissionArtifact.instructions.length at hbound
        omega⟩

def byte0Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 1999 80 (by rw [Artifact.submissionInstructions_count]; omega)

def byte1Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2079 80 (by rw [Artifact.submissionInstructions_count]; omega)

def byte2Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2159 80 (by rw [Artifact.submissionInstructions_count]; omega)

def byte3Path : List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice 2239 80 (by rw [Artifact.submissionInstructions_count]; omega)

def byteStartIndex (byte : Fin 4) : Nat := 1999 + 80 * byte.val

def byteStartPC (byte : Fin 4) : Nat :=
  [3208, 3292, 3377, 3462][byte.val]!

def highPrepPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte) 6 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def highSquarePath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 6) 24 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def highLookupPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 30) 10 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def lowPrepPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 40) 4 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def lowSquarePath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 44) 24 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def lowLookupPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 68) 10 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def finishPath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  locatedSlice (byteStartIndex byte + 78) 2 (by
    rw [Artifact.submissionInstructions_count]
    unfold byteStartIndex
    omega)

def segmentedBytePath (byte : Fin 4) :
    List (Located Artifact.submissionArtifact .Osaka) :=
  highPrepPath byte ++ highSquarePath byte ++ highLookupPath byte ++
    lowPrepPath byte ++ lowSquarePath byte ++ lowLookupPath byte ++
      finishPath byte

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

theorem lowPrep_instructions (byte : Fin 4) :
    (lowPrepPath byte).map (fun located => located.instruction) =
      lowPrepProgram := by
  fin_cases byte <;> rfl

theorem finish_instructions (byte : Fin 4) :
    (finishPath byte).map (fun located => located.instruction) =
      finishProgram := by
  fin_cases byte <;> rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteSlices

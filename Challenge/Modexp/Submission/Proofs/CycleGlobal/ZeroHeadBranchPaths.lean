import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2060 1 32,
   opAt 2061 .MLOAD,
   pushAt 2062 1 128,
   opAt 2063 .SHR,
   opAt 2064 (.Swap ⟨12,by decide⟩),
   opAt 2065 .POP,
   opAt 2066 (.Dup ⟨15,by decide⟩),
   pushAt 2067 1 1,
   opAt 2068 .AND,
   opAt 2069 .SHR,
   opAt 2070 (.Dup ⟨11,by decide⟩),
   opAt 2071 .ISZERO,
   pushAt 2072 2 2672,
   opAt 2073 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2074 (.Dup ⟨13,by decide⟩),
   pushAt 2075 2 2002,
   opAt 2076 .MUL,
   pushAt 2077 2 18700,
   opAt 2078 .SUB,
   opAt 2079 (.Swap ⟨0,by decide⟩),
   opAt 2080 (.Dup ⟨1,by decide⟩),
   opAt 2081 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2082 .JUMPDEST,
   opAt 2083 (.Dup ⟨13,by decide⟩),
   pushAt 2084 1 42,
   opAt 2085 .MUL,
   pushAt 2086 2 4047,
   opAt 2087 .SUB,
   opAt 2088 (.Swap ⟨0,by decide⟩),
   opAt 2089 (.Dup ⟨1,by decide⟩),
   opAt 2090 .JUMP]
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose ++ if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem directCachePC2060 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2061 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2062 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2063 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2064 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2065 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2648 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2066 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2067 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2068 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2069 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2070 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2071 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2655 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2072 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2073 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2074 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2075 : CycleSubmission.Artifact.artifact.instructionPC 2075 = 2661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2076 : CycleSubmission.Artifact.artifact.instructionPC 2076 = 2664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2077 : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2665 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2078 : CycleSubmission.Artifact.artifact.instructionPC 2078 = 2668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2079 : CycleSubmission.Artifact.artifact.instructionPC 2079 = 2669 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2080 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2670 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2081 : CycleSubmission.Artifact.artifact.instructionPC 2081 = 2671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2082 : CycleSubmission.Artifact.artifact.instructionPC 2082 = 2672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2083 : CycleSubmission.Artifact.artifact.instructionPC 2083 = 2673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2084 : CycleSubmission.Artifact.artifact.instructionPC 2084 = 2674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2085 : CycleSubmission.Artifact.artifact.instructionPC 2085 = 2676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2086 : CycleSubmission.Artifact.artifact.instructionPC 2086 = 2677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2087 : CycleSubmission.Artifact.artifact.instructionPC 2087 = 2680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2088 : CycleSubmission.Artifact.artifact.instructionPC 2088 = 2681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2089 : CycleSubmission.Artifact.artifact.instructionPC 2089 = 2682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directCachePC2090 : CycleSubmission.Artifact.artifact.instructionPC 2090 = 2683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheZero : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2672 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2082 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast.Shift

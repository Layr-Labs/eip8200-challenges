import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2057 1 32,
   opAt 2058 .MLOAD,
   pushAt 2059 1 128,
   opAt 2060 .SHR,
   opAt 2061 (.Swap ⟨12,by decide⟩),
   opAt 2062 .POP,
   opAt 2063 (.Dup ⟨15,by decide⟩),
   opAt 2064 .SHR,
   opAt 2065 (.Dup ⟨11,by decide⟩),
   opAt 2066 .ISZERO,
   pushAt 2067 2 2666,
   opAt 2068 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2069 (.Dup ⟨13,by decide⟩),
   pushAt 2070 2 2002,
   opAt 2071 .MUL,
   pushAt 2072 2 18700,
   opAt 2073 .SUB,
   opAt 2074 (.Swap ⟨0,by decide⟩),
   opAt 2075 (.Dup ⟨1,by decide⟩),
   opAt 2076 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2077 .JUMPDEST,
   opAt 2078 (.Dup ⟨13,by decide⟩),
   pushAt 2079 2 42,
   opAt 2080 .MUL,
   pushAt 2081 2 4047,
   opAt 2082 .SUB,
   opAt 2083 (.Swap ⟨0,by decide⟩),
   opAt 2084 (.Dup ⟨1,by decide⟩),
   opAt 2085 .JUMP]
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose ++ if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem branchCachePC2057 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2638 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2058 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2059 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2060 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2061 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2062 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2063 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2064 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2065 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2648 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2066 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2067 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2068 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2069 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2070 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2655 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2071 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2072 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2073 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2074 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2075 : CycleSubmission.Artifact.artifact.instructionPC 2075 = 2664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2076 : CycleSubmission.Artifact.artifact.instructionPC 2076 = 2665 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2077 : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2666 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2078 : CycleSubmission.Artifact.artifact.instructionPC 2078 = 2667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2079 : CycleSubmission.Artifact.artifact.instructionPC 2079 = 2668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2080 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2081 : CycleSubmission.Artifact.artifact.instructionPC 2081 = 2672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2082 : CycleSubmission.Artifact.artifact.instructionPC 2082 = 2675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2083 : CycleSubmission.Artifact.artifact.instructionPC 2083 = 2676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2084 : CycleSubmission.Artifact.artifact.instructionPC 2084 = 2677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem branchCachePC2085 : CycleSubmission.Artifact.artifact.instructionPC 2085 = 2678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheZero : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2666 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2077 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2666 := branchCachePC2077
  simpa only [hp] using h
end CycleSubmission.Global.Fast.Shift

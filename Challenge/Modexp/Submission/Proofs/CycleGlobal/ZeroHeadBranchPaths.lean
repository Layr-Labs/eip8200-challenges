import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2063 1 32,
   opAt 2064 .MLOAD,
   pushAt 2065 1 128,
   opAt 2066 .SHR,
   opAt 2067 (.Swap ⟨12,by decide⟩),
   opAt 2068 .POP,
   opAt 2069 (.Dup ⟨15,by decide⟩),
   pushAt 2070 1 1,
   opAt 2071 .AND,
   opAt 2072 .SHR,
   opAt 2073 (.Dup ⟨11,by decide⟩),
   opAt 2074 .ISZERO,
   pushAt 2075 2 2680,
   opAt 2076 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2077 (.Dup ⟨13,by decide⟩),
   pushAt 2078 2 2000,
   opAt 2079 .MUL,
   pushAt 2080 2 18692,
   opAt 2081 .SUB,
   opAt 2082 (.Swap ⟨0,by decide⟩),
   opAt 2083 (.Dup ⟨1,by decide⟩),
   opAt 2084 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2085 .JUMPDEST,
   opAt 2086 (.Dup ⟨13,by decide⟩),
   pushAt 2087 1 42,
   opAt 2088 .MUL,
   pushAt 2089 2 4047,
   opAt 2090 .SUB,
   opAt 2091 (.Swap ⟨0,by decide⟩),
   opAt 2092 (.Dup ⟨1,by decide⟩),
   opAt 2093 .JUMP]
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose ++ if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem directWordPC2009 : CycleSubmission.Artifact.artifact.instructionPC 2009 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2010 : CycleSubmission.Artifact.artifact.instructionPC 2010 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2011 : CycleSubmission.Artifact.artifact.instructionPC 2011 = 2558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2012 : CycleSubmission.Artifact.artifact.instructionPC 2012 = 2559 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2013 : CycleSubmission.Artifact.artifact.instructionPC 2013 = 2562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2014 : CycleSubmission.Artifact.artifact.instructionPC 2014 = 2563 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2015 : CycleSubmission.Artifact.artifact.instructionPC 2015 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2016 : CycleSubmission.Artifact.artifact.instructionPC 2016 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2017 : CycleSubmission.Artifact.artifact.instructionPC 2017 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2018 : CycleSubmission.Artifact.artifact.instructionPC 2018 = 2569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2019 : CycleSubmission.Artifact.artifact.instructionPC 2019 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2020 : CycleSubmission.Artifact.artifact.instructionPC 2020 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2021 : CycleSubmission.Artifact.artifact.instructionPC 2021 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2022 : CycleSubmission.Artifact.artifact.instructionPC 2022 = 2579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2023 : CycleSubmission.Artifact.artifact.instructionPC 2023 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2024 : CycleSubmission.Artifact.artifact.instructionPC 2024 = 2581 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2025 : CycleSubmission.Artifact.artifact.instructionPC 2025 = 2584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2026 : CycleSubmission.Artifact.artifact.instructionPC 2026 = 2585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2027 : CycleSubmission.Artifact.artifact.instructionPC 2027 = 2588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2028 : CycleSubmission.Artifact.artifact.instructionPC 2028 = 2589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2029 : CycleSubmission.Artifact.artifact.instructionPC 2029 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2030 : CycleSubmission.Artifact.artifact.instructionPC 2030 = 2591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2031 : CycleSubmission.Artifact.artifact.instructionPC 2031 = 2592 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2032 : CycleSubmission.Artifact.artifact.instructionPC 2032 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2033 : CycleSubmission.Artifact.artifact.instructionPC 2033 = 2595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2034 : CycleSubmission.Artifact.artifact.instructionPC 2034 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2035 : CycleSubmission.Artifact.artifact.instructionPC 2035 = 2599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2036 : CycleSubmission.Artifact.artifact.instructionPC 2036 = 2600 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2037 : CycleSubmission.Artifact.artifact.instructionPC 2037 = 2601 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2038 : CycleSubmission.Artifact.artifact.instructionPC 2038 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2039 : CycleSubmission.Artifact.artifact.instructionPC 2039 = 2603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2040 : CycleSubmission.Artifact.artifact.instructionPC 2040 = 2604 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2041 : CycleSubmission.Artifact.artifact.instructionPC 2041 = 2607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2042 : CycleSubmission.Artifact.artifact.instructionPC 2042 = 2608 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2043 : CycleSubmission.Artifact.artifact.instructionPC 2043 = 2611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2044 : CycleSubmission.Artifact.artifact.instructionPC 2044 = 2612 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2045 : CycleSubmission.Artifact.artifact.instructionPC 2045 = 2615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2046 : CycleSubmission.Artifact.artifact.instructionPC 2046 = 2616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2047 : CycleSubmission.Artifact.artifact.instructionPC 2047 = 2619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2048 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2620 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2049 : CycleSubmission.Artifact.artifact.instructionPC 2049 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2050 : CycleSubmission.Artifact.artifact.instructionPC 2050 = 2624 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2051 : CycleSubmission.Artifact.artifact.instructionPC 2051 = 2627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2052 : CycleSubmission.Artifact.artifact.instructionPC 2052 = 2628 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2053 : CycleSubmission.Artifact.artifact.instructionPC 2053 = 2631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2054 : CycleSubmission.Artifact.artifact.instructionPC 2054 = 2632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2055 : CycleSubmission.Artifact.artifact.instructionPC 2055 = 2635 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2056 : CycleSubmission.Artifact.artifact.instructionPC 2056 = 2636 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2057 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2058 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2059 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2060 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2061 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2062 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2648 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2063 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2064 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2065 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2066 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2067 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2655 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2068 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2069 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2070 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2071 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2072 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2073 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2074 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2075 : CycleSubmission.Artifact.artifact.instructionPC 2075 = 2664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2076 : CycleSubmission.Artifact.artifact.instructionPC 2076 = 2667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2077 : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2078 : CycleSubmission.Artifact.artifact.instructionPC 2078 = 2669 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2079 : CycleSubmission.Artifact.artifact.instructionPC 2079 = 2672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2080 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2081 : CycleSubmission.Artifact.artifact.instructionPC 2081 = 2676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2082 : CycleSubmission.Artifact.artifact.instructionPC 2082 = 2677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2083 : CycleSubmission.Artifact.artifact.instructionPC 2083 = 2678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2084 : CycleSubmission.Artifact.artifact.instructionPC 2084 = 2679 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2085 : CycleSubmission.Artifact.artifact.instructionPC 2085 = 2680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2086 : CycleSubmission.Artifact.artifact.instructionPC 2086 = 2681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2087 : CycleSubmission.Artifact.artifact.instructionPC 2087 = 2682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2088 : CycleSubmission.Artifact.artifact.instructionPC 2088 = 2684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2089 : CycleSubmission.Artifact.artifact.instructionPC 2089 = 2685 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2090 : CycleSubmission.Artifact.artifact.instructionPC 2090 = 2688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2091 : CycleSubmission.Artifact.artifact.instructionPC 2091 = 2689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2092 : CycleSubmission.Artifact.artifact.instructionPC 2092 = 2690 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordPC2093 : CycleSubmission.Artifact.artifact.instructionPC 2093 = 2691 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheZero : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2680 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2085 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast.Shift

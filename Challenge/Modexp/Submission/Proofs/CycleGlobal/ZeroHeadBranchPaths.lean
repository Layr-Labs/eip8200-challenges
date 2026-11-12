import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2063 (.Dup ⟨11,by decide⟩),
   opAt 2064 .ISZERO,
   pushAt 2065 2 2679,
   opAt 2066 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2067 (.Dup ⟨0,by decide⟩),
   pushAt 2068 2 2006,
   opAt 2069 .MUL,
   pushAt 2070 2 18744,
   opAt 2071 .SUB,
   opAt 2072 (.Swap ⟨0,by decide⟩),
   opAt 2073 (.Dup ⟨14,by decide⟩),
   pushAt 2074 1 1,
   opAt 2075 .AND,
   opAt 2076 .SHR,
   opAt 2077 (.Dup ⟨1,by decide⟩),
   opAt 2078 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2079 .JUMPDEST,
   opAt 2080 (.Dup ⟨0,by decide⟩),
   pushAt 2081 1 45,
   opAt 2082 .MUL,
   pushAt 2083 2 4075,
   opAt 2084 .SUB,
   opAt 2085 (.Swap ⟨0,by decide⟩),
   opAt 2086 (.Dup ⟨14,by decide⟩),
   pushAt 2087 1 1,
   opAt 2088 .AND,
   opAt 2089 .SHR,
   opAt 2090 (.Dup ⟨1,by decide⟩),
   opAt 2091 .JUMP]
@[simp] theorem rhoCachePC2065 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2066 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2067 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2068 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2069 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2070 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2071 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2666 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2072 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2073 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2670 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2074 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2075 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2076 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2077 : CycleSubmission.Artifact.artifact.instructionPC 2075 = 2675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2078 : CycleSubmission.Artifact.artifact.instructionPC 2076 = 2676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2079 : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2080 : CycleSubmission.Artifact.artifact.instructionPC 2078 = 2678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2081 : CycleSubmission.Artifact.artifact.instructionPC 2079 = 2679 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2082 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2083 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2084 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2085 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2086 : CycleSubmission.Artifact.artifact.instructionPC 2081 = 2681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2087 : CycleSubmission.Artifact.artifact.instructionPC 2082 = 2683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2088 : CycleSubmission.Artifact.artifact.instructionPC 2083 = 2684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2089 : CycleSubmission.Artifact.artifact.instructionPC 2084 = 2687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2090 : CycleSubmission.Artifact.artifact.instructionPC 2085 = 2688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2091 : CycleSubmission.Artifact.artifact.instructionPC 2086 = 2689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2092 : CycleSubmission.Artifact.artifact.instructionPC 2087 = 2690 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2093 : CycleSubmission.Artifact.artifact.instructionPC 2088 = 2692 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2094 : CycleSubmission.Artifact.artifact.instructionPC 2089 = 2693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2095 : CycleSubmission.Artifact.artifact.instructionPC 2090 = 2694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2096 : CycleSubmission.Artifact.artifact.instructionPC 2091 = 2695 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose ++ if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem readyPC2009 : CycleSubmission.Artifact.artifact.instructionPC 2009 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2010 : CycleSubmission.Artifact.artifact.instructionPC 2010 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2011 : CycleSubmission.Artifact.artifact.instructionPC 2011 = 2558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2012 : CycleSubmission.Artifact.artifact.instructionPC 2012 = 2559 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2013 : CycleSubmission.Artifact.artifact.instructionPC 2013 = 2562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2014 : CycleSubmission.Artifact.artifact.instructionPC 2014 = 2563 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2015 : CycleSubmission.Artifact.artifact.instructionPC 2015 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2016 : CycleSubmission.Artifact.artifact.instructionPC 2016 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2017 : CycleSubmission.Artifact.artifact.instructionPC 2017 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2018 : CycleSubmission.Artifact.artifact.instructionPC 2018 = 2569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2019 : CycleSubmission.Artifact.artifact.instructionPC 2019 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2020 : CycleSubmission.Artifact.artifact.instructionPC 2020 = 2581 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2021 : CycleSubmission.Artifact.artifact.instructionPC 2021 = 2582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2022 : CycleSubmission.Artifact.artifact.instructionPC 2022 = 2584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2023 : CycleSubmission.Artifact.artifact.instructionPC 2023 = 2585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2024 : CycleSubmission.Artifact.artifact.instructionPC 2023 = 2585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2025 : CycleSubmission.Artifact.artifact.instructionPC 2024 = 2588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2026 : CycleSubmission.Artifact.artifact.instructionPC 2025 = 2589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2027 : CycleSubmission.Artifact.artifact.instructionPC 2026 = 2592 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2028 : CycleSubmission.Artifact.artifact.instructionPC 2027 = 2593 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2029 : CycleSubmission.Artifact.artifact.instructionPC 2028 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2030 : CycleSubmission.Artifact.artifact.instructionPC 2029 = 2595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2031 : CycleSubmission.Artifact.artifact.instructionPC 2030 = 2596 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2032 : CycleSubmission.Artifact.artifact.instructionPC 2031 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2033 : CycleSubmission.Artifact.artifact.instructionPC 2032 = 2599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2034 : CycleSubmission.Artifact.artifact.instructionPC 2033 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2035 : CycleSubmission.Artifact.artifact.instructionPC 2034 = 2603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2036 : CycleSubmission.Artifact.artifact.instructionPC 2035 = 2604 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2037 : CycleSubmission.Artifact.artifact.instructionPC 2036 = 2605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2038 : CycleSubmission.Artifact.artifact.instructionPC 2036 = 2605 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2039 : CycleSubmission.Artifact.artifact.instructionPC 2037 = 2607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2040 : CycleSubmission.Artifact.artifact.instructionPC 2038 = 2608 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2041 : CycleSubmission.Artifact.artifact.instructionPC 2039 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2042 : CycleSubmission.Artifact.artifact.instructionPC 2040 = 2611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2043 : CycleSubmission.Artifact.artifact.instructionPC 2041 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2044 : CycleSubmission.Artifact.artifact.instructionPC 2042 = 2615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2045 : CycleSubmission.Artifact.artifact.instructionPC 2043 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2046 : CycleSubmission.Artifact.artifact.instructionPC 2044 = 2619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2047 : CycleSubmission.Artifact.artifact.instructionPC 2045 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2048 : CycleSubmission.Artifact.artifact.instructionPC 2046 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2049 : CycleSubmission.Artifact.artifact.instructionPC 2047 = 2626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2050 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2051 : CycleSubmission.Artifact.artifact.instructionPC 2049 = 2630 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2052 : CycleSubmission.Artifact.artifact.instructionPC 2050 = 2631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2053 : CycleSubmission.Artifact.artifact.instructionPC 2051 = 2634 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2054 : CycleSubmission.Artifact.artifact.instructionPC 2052 = 2635 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2055 : CycleSubmission.Artifact.artifact.instructionPC 2053 = 2638 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2056 : CycleSubmission.Artifact.artifact.instructionPC 2054 = 2639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2057 : CycleSubmission.Artifact.artifact.instructionPC 2055 = 2642 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2058 : CycleSubmission.Artifact.artifact.instructionPC 2056 = 2643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2059 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2060 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2061 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2062 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2063 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2064 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2655 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2065 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2066 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2067 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2068 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2069 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2070 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2071 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2666 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2072 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2073 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2670 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2074 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2075 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2076 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2077 : CycleSubmission.Artifact.artifact.instructionPC 2075 = 2675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2078 : CycleSubmission.Artifact.artifact.instructionPC 2076 = 2676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2079 : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2080 : CycleSubmission.Artifact.artifact.instructionPC 2078 = 2678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2081 : CycleSubmission.Artifact.artifact.instructionPC 2079 = 2679 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2082 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2680 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2083 : CycleSubmission.Artifact.artifact.instructionPC 2081 = 2681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2084 : CycleSubmission.Artifact.artifact.instructionPC 2082 = 2683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2085 : CycleSubmission.Artifact.artifact.instructionPC 2083 = 2684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2086 : CycleSubmission.Artifact.artifact.instructionPC 2084 = 2687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2087 : CycleSubmission.Artifact.artifact.instructionPC 2085 = 2688 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2088 : CycleSubmission.Artifact.artifact.instructionPC 2086 = 2689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2089 : CycleSubmission.Artifact.artifact.instructionPC 2087 = 2690 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2090 : CycleSubmission.Artifact.artifact.instructionPC 2088 = 2692 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2091 : CycleSubmission.Artifact.artifact.instructionPC 2089 = 2693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2092 : CycleSubmission.Artifact.artifact.instructionPC 2090 = 2694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2093 : CycleSubmission.Artifact.artifact.instructionPC 2091 = 2695 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheZero : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2679 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2079 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast.Shift

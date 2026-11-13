import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2047 (.Dup ⟨11,by decide⟩),
   pushAt 2048 3 2662,
   opAt 2049 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2062 .JUMPDEST,
   opAt 2063 (.Dup ⟨0,by decide⟩),
   pushAt 2064 2 2004,
   opAt 2065 .MUL,
   pushAt 2066 2 18712,
   opAt 2067 .SUB,
   opAt 2068 (.Swap ⟨0,by decide⟩),
   opAt 2069 (.Dup ⟨14,by decide⟩),
   pushAt 2070 1 1,
   opAt 2071 .AND,
   opAt 2072 .SHR,
   opAt 2073 (.Dup ⟨1,by decide⟩),
   opAt 2074 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2050 (.Dup ⟨0,by decide⟩),
   pushAt 2051 1 45,
   opAt 2052 .MUL,
   pushAt 2053 2 4059,
   opAt 2054 .SUB,
   opAt 2055 (.Swap ⟨0,by decide⟩),
   opAt 2056 (.Dup ⟨14,by decide⟩),
   pushAt 2057 1 1,
   opAt 2058 .AND,
   opAt 2059 .SHR,
   opAt 2060 (.Dup ⟨1,by decide⟩),
   opAt 2061 .JUMP]
@[simp] theorem rhoCachePC2065 : CycleSubmission.Artifact.artifact.instructionPC 2047 = 2640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2066 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2067 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2068 : CycleSubmission.Artifact.artifact.instructionPC 2049 = 2645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2069 : CycleSubmission.Artifact.artifact.instructionPC 2050 = 2646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2070 : CycleSubmission.Artifact.artifact.instructionPC 2051 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2071 : CycleSubmission.Artifact.artifact.instructionPC 2052 = 2649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2072 : CycleSubmission.Artifact.artifact.instructionPC 2053 = 2650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2073 : CycleSubmission.Artifact.artifact.instructionPC 2054 = 2653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2074 : CycleSubmission.Artifact.artifact.instructionPC 2055 = 2654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2075 : CycleSubmission.Artifact.artifact.instructionPC 2056 = 2655 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2076 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2077 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2078 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2079 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2080 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2081 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2082 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2083 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2084 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2085 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2086 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2087 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2088 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2089 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2090 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2091 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2092 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2093 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2094 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2095 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2096 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2679 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose ++ if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem readyPC2009 : CycleSubmission.Artifact.artifact.instructionPC 1993 = 2548 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2010 : CycleSubmission.Artifact.artifact.instructionPC 1994 = 2549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2011 : CycleSubmission.Artifact.artifact.instructionPC 1995 = 2550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2012 : CycleSubmission.Artifact.artifact.instructionPC 1996 = 2551 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2013 : CycleSubmission.Artifact.artifact.instructionPC 1997 = 2554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2014 : CycleSubmission.Artifact.artifact.instructionPC 1998 = 2555 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2015 : CycleSubmission.Artifact.artifact.instructionPC 1999 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2016 : CycleSubmission.Artifact.artifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2017 : CycleSubmission.Artifact.artifact.instructionPC 2001 = 2558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2018 : CycleSubmission.Artifact.artifact.instructionPC 2002 = 2561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2019 : CycleSubmission.Artifact.artifact.instructionPC 2003 = 2562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2020 : CycleSubmission.Artifact.artifact.instructionPC 2004 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2021 : CycleSubmission.Artifact.artifact.instructionPC 2005 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2022 : CycleSubmission.Artifact.artifact.instructionPC 2006 = 2568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2023 : CycleSubmission.Artifact.artifact.instructionPC 2007 = 2569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2024 : CycleSubmission.Artifact.artifact.instructionPC 2007 = 2569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2025 : CycleSubmission.Artifact.artifact.instructionPC 2008 = 2572 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2026 : CycleSubmission.Artifact.artifact.instructionPC 2009 = 2573 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2027 : CycleSubmission.Artifact.artifact.instructionPC 2010 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2028 : CycleSubmission.Artifact.artifact.instructionPC 2011 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2029 : CycleSubmission.Artifact.artifact.instructionPC 2012 = 2578 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2030 : CycleSubmission.Artifact.artifact.instructionPC 2013 = 2579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2031 : CycleSubmission.Artifact.artifact.instructionPC 2014 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2032 : CycleSubmission.Artifact.artifact.instructionPC 2015 = 2582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2033 : CycleSubmission.Artifact.artifact.instructionPC 2016 = 2583 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2034 : CycleSubmission.Artifact.artifact.instructionPC 2017 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2035 : CycleSubmission.Artifact.artifact.instructionPC 2018 = 2587 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2036 : CycleSubmission.Artifact.artifact.instructionPC 2019 = 2588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2037 : CycleSubmission.Artifact.artifact.instructionPC 2020 = 2589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2038 : CycleSubmission.Artifact.artifact.instructionPC 2020 = 2589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2039 : CycleSubmission.Artifact.artifact.instructionPC 2021 = 2591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2040 : CycleSubmission.Artifact.artifact.instructionPC 2022 = 2592 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2041 : CycleSubmission.Artifact.artifact.instructionPC 2023 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2042 : CycleSubmission.Artifact.artifact.instructionPC 2024 = 2595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2043 : CycleSubmission.Artifact.artifact.instructionPC 2025 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2044 : CycleSubmission.Artifact.artifact.instructionPC 2026 = 2599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2045 : CycleSubmission.Artifact.artifact.instructionPC 2027 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2046 : CycleSubmission.Artifact.artifact.instructionPC 2028 = 2603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2047 : CycleSubmission.Artifact.artifact.instructionPC 2029 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2048 : CycleSubmission.Artifact.artifact.instructionPC 2030 = 2607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2049 : CycleSubmission.Artifact.artifact.instructionPC 2031 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2050 : CycleSubmission.Artifact.artifact.instructionPC 2032 = 2611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2051 : CycleSubmission.Artifact.artifact.instructionPC 2033 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2052 : CycleSubmission.Artifact.artifact.instructionPC 2034 = 2615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2053 : CycleSubmission.Artifact.artifact.instructionPC 2035 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2054 : CycleSubmission.Artifact.artifact.instructionPC 2036 = 2619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2055 : CycleSubmission.Artifact.artifact.instructionPC 2037 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2056 : CycleSubmission.Artifact.artifact.instructionPC 2038 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2057 : CycleSubmission.Artifact.artifact.instructionPC 2039 = 2626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2058 : CycleSubmission.Artifact.artifact.instructionPC 2040 = 2627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2059 : CycleSubmission.Artifact.artifact.instructionPC 2041 = 2630 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2060 : CycleSubmission.Artifact.artifact.instructionPC 2042 = 2631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2061 : CycleSubmission.Artifact.artifact.instructionPC 2043 = 2634 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2062 : CycleSubmission.Artifact.artifact.instructionPC 2044 = 2635 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2063 : CycleSubmission.Artifact.artifact.instructionPC 2045 = 2638 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2064 : CycleSubmission.Artifact.artifact.instructionPC 2046 = 2639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2065 : CycleSubmission.Artifact.artifact.instructionPC 2047 = 2640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2066 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2067 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2641 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2068 : CycleSubmission.Artifact.artifact.instructionPC 2049 = 2645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2069 : CycleSubmission.Artifact.artifact.instructionPC 2050 = 2646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2070 : CycleSubmission.Artifact.artifact.instructionPC 2051 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2071 : CycleSubmission.Artifact.artifact.instructionPC 2052 = 2649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2072 : CycleSubmission.Artifact.artifact.instructionPC 2053 = 2650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2073 : CycleSubmission.Artifact.artifact.instructionPC 2054 = 2653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2074 : CycleSubmission.Artifact.artifact.instructionPC 2055 = 2654 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2075 : CycleSubmission.Artifact.artifact.instructionPC 2056 = 2655 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2076 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2077 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2658 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2078 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2659 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2079 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2080 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2081 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2662 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2082 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2083 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2084 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2085 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2086 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2087 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2088 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2089 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2090 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2676 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2091 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2092 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2093 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2679 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheNormal : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2662 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2062 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast.Shift

import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2176 (.Dup ⟨11,by decide⟩),
   pushAt 2177 2 2844,
   opAt 2178 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2191 .JUMPDEST,
   pushAt 2192 2 4192,
   opAt 2193 (.Dup ⟨1,by decide⟩),
   opAt 2194 .SHR,
   pushAt 2195 2 3124,
   opAt 2196 .SUB,
   opAt 2197 (.Swap ⟨0,by decide⟩),
   opAt 2198 (.Dup ⟨14,by decide⟩),
   pushAt 2199 1 1,
   opAt 2200 .AND,
   opAt 2201 .SHR,
   opAt 2202 (.Dup ⟨1,by decide⟩),
   opAt 2203 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2179 3 736,
   opAt 2180 (.Dup ⟨1,by decide⟩),
   opAt 2181 .SHR,
   pushAt 2182 2 10574,
   opAt 2183 .ADD,
   opAt 2184 (.Swap ⟨0,by decide⟩),
   opAt 2185 (.Dup ⟨14,by decide⟩),
   pushAt 2186 1 1,
   opAt 2187 .AND,
   opAt 2188 .SHR,
   opAt 2189 (.Dup ⟨1,by decide⟩),
   opAt 2190 .JUMP]
@[simp] theorem rhoCachePC2065 : CycleSubmission.Artifact.artifact.instructionPC 2176 = 2821 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2066 : CycleSubmission.Artifact.artifact.instructionPC 2177 = 2822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2067 : CycleSubmission.Artifact.artifact.instructionPC 2177 = 2822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2068 : CycleSubmission.Artifact.artifact.instructionPC 2178 = 2825 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2069 : CycleSubmission.Artifact.artifact.instructionPC 2179 = 2826 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2070 : CycleSubmission.Artifact.artifact.instructionPC 2180 = 2830 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2071 : CycleSubmission.Artifact.artifact.instructionPC 2181 = 2831 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2072 : CycleSubmission.Artifact.artifact.instructionPC 2182 = 2832 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2073 : CycleSubmission.Artifact.artifact.instructionPC 2183 = 2835 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2074 : CycleSubmission.Artifact.artifact.instructionPC 2184 = 2836 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2075 : CycleSubmission.Artifact.artifact.instructionPC 2185 = 2837 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2076 : CycleSubmission.Artifact.artifact.instructionPC 2186 = 2838 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2077 : CycleSubmission.Artifact.artifact.instructionPC 2187 = 2840 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2078 : CycleSubmission.Artifact.artifact.instructionPC 2188 = 2841 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2079 : CycleSubmission.Artifact.artifact.instructionPC 2189 = 2842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2080 : CycleSubmission.Artifact.artifact.instructionPC 2190 = 2843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2081 : CycleSubmission.Artifact.artifact.instructionPC 2191 = 2844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2082 : CycleSubmission.Artifact.artifact.instructionPC 2192 = 2845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2083 : CycleSubmission.Artifact.artifact.instructionPC 2192 = 2845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2084 : CycleSubmission.Artifact.artifact.instructionPC 2192 = 2845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2085 : CycleSubmission.Artifact.artifact.instructionPC 2192 = 2845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2086 : CycleSubmission.Artifact.artifact.instructionPC 2193 = 2848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2087 : CycleSubmission.Artifact.artifact.instructionPC 2194 = 2849 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2088 : CycleSubmission.Artifact.artifact.instructionPC 2195 = 2850 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2089 : CycleSubmission.Artifact.artifact.instructionPC 2196 = 2853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2090 : CycleSubmission.Artifact.artifact.instructionPC 2197 = 2854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2091 : CycleSubmission.Artifact.artifact.instructionPC 2198 = 2855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2092 : CycleSubmission.Artifact.artifact.instructionPC 2199 = 2856 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2093 : CycleSubmission.Artifact.artifact.instructionPC 2200 = 2858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2094 : CycleSubmission.Artifact.artifact.instructionPC 2201 = 2859 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2095 : CycleSubmission.Artifact.artifact.instructionPC 2202 = 2860 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2096 : CycleSubmission.Artifact.artifact.instructionPC 2203 = 2861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose++if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem readyPC2009 : CycleSubmission.Artifact.artifact.instructionPC 2122 = 2729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2010 : CycleSubmission.Artifact.artifact.instructionPC 2123 = 2730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2011 : CycleSubmission.Artifact.artifact.instructionPC 2124 = 2731 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2012 : CycleSubmission.Artifact.artifact.instructionPC 2125 = 2732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2013 : CycleSubmission.Artifact.artifact.instructionPC 2126 = 2735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2014 : CycleSubmission.Artifact.artifact.instructionPC 2127 = 2736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2015 : CycleSubmission.Artifact.artifact.instructionPC 2128 = 2737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2016 : CycleSubmission.Artifact.artifact.instructionPC 2129 = 2738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2017 : CycleSubmission.Artifact.artifact.instructionPC 2130 = 2739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2018 : CycleSubmission.Artifact.artifact.instructionPC 2131 = 2742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2019 : CycleSubmission.Artifact.artifact.instructionPC 2132 = 2743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2020 : CycleSubmission.Artifact.artifact.instructionPC 2133 = 2746 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2021 : CycleSubmission.Artifact.artifact.instructionPC 2134 = 2747 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2022 : CycleSubmission.Artifact.artifact.instructionPC 2135 = 2749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2023 : CycleSubmission.Artifact.artifact.instructionPC 2136 = 2750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2024 : CycleSubmission.Artifact.artifact.instructionPC 2136 = 2750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2025 : CycleSubmission.Artifact.artifact.instructionPC 2137 = 2753 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2026 : CycleSubmission.Artifact.artifact.instructionPC 2138 = 2754 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2027 : CycleSubmission.Artifact.artifact.instructionPC 2139 = 2757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2028 : CycleSubmission.Artifact.artifact.instructionPC 2140 = 2758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2029 : CycleSubmission.Artifact.artifact.instructionPC 2141 = 2759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2030 : CycleSubmission.Artifact.artifact.instructionPC 2142 = 2760 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2031 : CycleSubmission.Artifact.artifact.instructionPC 2143 = 2761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2032 : CycleSubmission.Artifact.artifact.instructionPC 2144 = 2763 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2033 : CycleSubmission.Artifact.artifact.instructionPC 2145 = 2764 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2034 : CycleSubmission.Artifact.artifact.instructionPC 2146 = 2767 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2035 : CycleSubmission.Artifact.artifact.instructionPC 2147 = 2768 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2036 : CycleSubmission.Artifact.artifact.instructionPC 2148 = 2769 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2037 : CycleSubmission.Artifact.artifact.instructionPC 2149 = 2770 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2038 : CycleSubmission.Artifact.artifact.instructionPC 2149 = 2770 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2039 : CycleSubmission.Artifact.artifact.instructionPC 2150 = 2772 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2040 : CycleSubmission.Artifact.artifact.instructionPC 2151 = 2773 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2041 : CycleSubmission.Artifact.artifact.instructionPC 2152 = 2775 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2042 : CycleSubmission.Artifact.artifact.instructionPC 2153 = 2776 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2043 : CycleSubmission.Artifact.artifact.instructionPC 2154 = 2779 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2044 : CycleSubmission.Artifact.artifact.instructionPC 2155 = 2780 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2045 : CycleSubmission.Artifact.artifact.instructionPC 2156 = 2783 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2046 : CycleSubmission.Artifact.artifact.instructionPC 2157 = 2784 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2047 : CycleSubmission.Artifact.artifact.instructionPC 2158 = 2787 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2048 : CycleSubmission.Artifact.artifact.instructionPC 2159 = 2788 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2049 : CycleSubmission.Artifact.artifact.instructionPC 2160 = 2791 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2050 : CycleSubmission.Artifact.artifact.instructionPC 2161 = 2792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2051 : CycleSubmission.Artifact.artifact.instructionPC 2162 = 2795 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2052 : CycleSubmission.Artifact.artifact.instructionPC 2163 = 2796 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2053 : CycleSubmission.Artifact.artifact.instructionPC 2164 = 2799 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2054 : CycleSubmission.Artifact.artifact.instructionPC 2165 = 2800 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2055 : CycleSubmission.Artifact.artifact.instructionPC 2166 = 2803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2056 : CycleSubmission.Artifact.artifact.instructionPC 2167 = 2804 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2057 : CycleSubmission.Artifact.artifact.instructionPC 2168 = 2807 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2058 : CycleSubmission.Artifact.artifact.instructionPC 2169 = 2808 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2059 : CycleSubmission.Artifact.artifact.instructionPC 2170 = 2811 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2060 : CycleSubmission.Artifact.artifact.instructionPC 2171 = 2812 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2061 : CycleSubmission.Artifact.artifact.instructionPC 2172 = 2815 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2062 : CycleSubmission.Artifact.artifact.instructionPC 2173 = 2816 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2063 : CycleSubmission.Artifact.artifact.instructionPC 2174 = 2819 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2064 : CycleSubmission.Artifact.artifact.instructionPC 2175 = 2820 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2065 : CycleSubmission.Artifact.artifact.instructionPC 2176 = 2821 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2066 : CycleSubmission.Artifact.artifact.instructionPC 2177 = 2822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2067 : CycleSubmission.Artifact.artifact.instructionPC 2177 = 2822 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2068 : CycleSubmission.Artifact.artifact.instructionPC 2178 = 2825 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2069 : CycleSubmission.Artifact.artifact.instructionPC 2179 = 2826 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2070 : CycleSubmission.Artifact.artifact.instructionPC 2180 = 2830 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2071 : CycleSubmission.Artifact.artifact.instructionPC 2181 = 2831 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2072 : CycleSubmission.Artifact.artifact.instructionPC 2182 = 2832 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2073 : CycleSubmission.Artifact.artifact.instructionPC 2183 = 2835 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2074 : CycleSubmission.Artifact.artifact.instructionPC 2184 = 2836 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2075 : CycleSubmission.Artifact.artifact.instructionPC 2185 = 2837 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2076 : CycleSubmission.Artifact.artifact.instructionPC 2186 = 2838 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2077 : CycleSubmission.Artifact.artifact.instructionPC 2187 = 2840 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2078 : CycleSubmission.Artifact.artifact.instructionPC 2188 = 2841 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2079 : CycleSubmission.Artifact.artifact.instructionPC 2189 = 2842 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2080 : CycleSubmission.Artifact.artifact.instructionPC 2190 = 2843 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2081 : CycleSubmission.Artifact.artifact.instructionPC 2191 = 2844 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2082 : CycleSubmission.Artifact.artifact.instructionPC 2192 = 2845 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2083 : CycleSubmission.Artifact.artifact.instructionPC 2193 = 2848 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2084 : CycleSubmission.Artifact.artifact.instructionPC 2194 = 2849 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2085 : CycleSubmission.Artifact.artifact.instructionPC 2195 = 2850 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2086 : CycleSubmission.Artifact.artifact.instructionPC 2196 = 2853 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2087 : CycleSubmission.Artifact.artifact.instructionPC 2197 = 2854 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2088 : CycleSubmission.Artifact.artifact.instructionPC 2198 = 2855 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2089 : CycleSubmission.Artifact.artifact.instructionPC 2199 = 2856 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2090 : CycleSubmission.Artifact.artifact.instructionPC 2200 = 2858 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2091 : CycleSubmission.Artifact.artifact.instructionPC 2201 = 2859 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2092 : CycleSubmission.Artifact.artifact.instructionPC 2202 = 2860 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2093 : CycleSubmission.Artifact.artifact.instructionPC 2203 = 2861 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheNormal : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2844 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2191 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast.Shift

import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
def blkCacheChoose : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2353 (.Dup ⟨11,by decide⟩),
   pushAt 2354 2 3090,
   opAt 2355 .JUMPI]
def blkCacheNormal : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2368 .JUMPDEST,
   pushAt 2369 1 33,
   opAt 2370 (.Dup ⟨1,by decide⟩),
   opAt 2371 .SHL,
   opAt 2372 (.Swap ⟨0,by decide⟩),
   opAt 2373 (.Dup ⟨14,by decide⟩),
   pushAt 2374 1 1,
   opAt 2375 .AND,
   opAt 2376 .SHR,
   opAt 2377 (.Dup ⟨1,by decide⟩),
   opAt 2378 .JUMP]
def blkCacheZero : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2356 3 736,
   opAt 2357 (.Dup ⟨1,by decide⟩),
   opAt 2358 .SHR,
   pushAt 2359 2 10569,
   opAt 2360 .ADD,
   opAt 2361 (.Swap ⟨0,by decide⟩),
   opAt 2362 (.Dup ⟨14,by decide⟩),
   pushAt 2363 1 1,
   opAt 2364 .AND,
   opAt 2365 .SHR,
   opAt 2366 (.Dup ⟨1,by decide⟩),
   opAt 2367 .JUMP]
@[simp] theorem rhoCachePC2065 : CycleSubmission.Artifact.artifact.instructionPC 2353 = 3067 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2066 : CycleSubmission.Artifact.artifact.instructionPC 2354 = 3068 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2067 : CycleSubmission.Artifact.artifact.instructionPC 2354 = 3068 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2068 : CycleSubmission.Artifact.artifact.instructionPC 2355 = 3071 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2069 : CycleSubmission.Artifact.artifact.instructionPC 2356 = 3072 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2070 : CycleSubmission.Artifact.artifact.instructionPC 2357 = 3076 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2071 : CycleSubmission.Artifact.artifact.instructionPC 2358 = 3077 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2072 : CycleSubmission.Artifact.artifact.instructionPC 2359 = 3078 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2073 : CycleSubmission.Artifact.artifact.instructionPC 2360 = 3081 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2074 : CycleSubmission.Artifact.artifact.instructionPC 2361 = 3082 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2075 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3083 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2076 : CycleSubmission.Artifact.artifact.instructionPC 2363 = 3084 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2077 : CycleSubmission.Artifact.artifact.instructionPC 2364 = 3086 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2078 : CycleSubmission.Artifact.artifact.instructionPC 2365 = 3087 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2079 : CycleSubmission.Artifact.artifact.instructionPC 2366 = 3088 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2080 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3089 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2081 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3090 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2082 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3091 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2083 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3091 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2084 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3091 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2085 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3091 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2086 : CycleSubmission.Artifact.artifact.instructionPC 2370 = 3093 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2087 : CycleSubmission.Artifact.artifact.instructionPC 2371 = 3094 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2088 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2089 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2090 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2091 : CycleSubmission.Artifact.artifact.instructionPC 2373 = 3096 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2092 : CycleSubmission.Artifact.artifact.instructionPC 2374 = 3097 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2093 : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3099 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2094 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3100 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2095 : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3101 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoCachePC2096 : CycleSubmission.Artifact.artifact.instructionPC 2378 = 3102 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
def cacheBlock (mem : ByteArray) : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  blkCacheChoose++if (MachineState.readWord mem 1536).toNat = 0 then blkCacheZero else blkCacheNormal
@[simp] theorem readyPC2009 : CycleSubmission.Artifact.artifact.instructionPC 2299 = 2975 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2010 : CycleSubmission.Artifact.artifact.instructionPC 2300 = 2976 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2011 : CycleSubmission.Artifact.artifact.instructionPC 2301 = 2977 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2012 : CycleSubmission.Artifact.artifact.instructionPC 2302 = 2978 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2013 : CycleSubmission.Artifact.artifact.instructionPC 2303 = 2981 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2014 : CycleSubmission.Artifact.artifact.instructionPC 2304 = 2982 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2015 : CycleSubmission.Artifact.artifact.instructionPC 2305 = 2983 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2016 : CycleSubmission.Artifact.artifact.instructionPC 2306 = 2984 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2017 : CycleSubmission.Artifact.artifact.instructionPC 2307 = 2985 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2018 : CycleSubmission.Artifact.artifact.instructionPC 2308 = 2988 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2019 : CycleSubmission.Artifact.artifact.instructionPC 2309 = 2989 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2020 : CycleSubmission.Artifact.artifact.instructionPC 2310 = 2992 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2021 : CycleSubmission.Artifact.artifact.instructionPC 2311 = 2993 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2022 : CycleSubmission.Artifact.artifact.instructionPC 2312 = 2995 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2023 : CycleSubmission.Artifact.artifact.instructionPC 2313 = 2996 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2024 : CycleSubmission.Artifact.artifact.instructionPC 2313 = 2996 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2025 : CycleSubmission.Artifact.artifact.instructionPC 2314 = 2999 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2026 : CycleSubmission.Artifact.artifact.instructionPC 2315 = 3000 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2027 : CycleSubmission.Artifact.artifact.instructionPC 2316 = 3003 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2028 : CycleSubmission.Artifact.artifact.instructionPC 2317 = 3004 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2029 : CycleSubmission.Artifact.artifact.instructionPC 2318 = 3005 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2030 : CycleSubmission.Artifact.artifact.instructionPC 2319 = 3006 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2031 : CycleSubmission.Artifact.artifact.instructionPC 2320 = 3007 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2032 : CycleSubmission.Artifact.artifact.instructionPC 2321 = 3009 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2033 : CycleSubmission.Artifact.artifact.instructionPC 2322 = 3010 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2034 : CycleSubmission.Artifact.artifact.instructionPC 2323 = 3013 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2035 : CycleSubmission.Artifact.artifact.instructionPC 2324 = 3014 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2036 : CycleSubmission.Artifact.artifact.instructionPC 2325 = 3015 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2037 : CycleSubmission.Artifact.artifact.instructionPC 2326 = 3016 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2038 : CycleSubmission.Artifact.artifact.instructionPC 2326 = 3016 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2039 : CycleSubmission.Artifact.artifact.instructionPC 2327 = 3018 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2040 : CycleSubmission.Artifact.artifact.instructionPC 2328 = 3019 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2041 : CycleSubmission.Artifact.artifact.instructionPC 2329 = 3021 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2042 : CycleSubmission.Artifact.artifact.instructionPC 2330 = 3022 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2043 : CycleSubmission.Artifact.artifact.instructionPC 2331 = 3025 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2044 : CycleSubmission.Artifact.artifact.instructionPC 2332 = 3026 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2045 : CycleSubmission.Artifact.artifact.instructionPC 2333 = 3029 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2046 : CycleSubmission.Artifact.artifact.instructionPC 2334 = 3030 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2047 : CycleSubmission.Artifact.artifact.instructionPC 2335 = 3033 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2048 : CycleSubmission.Artifact.artifact.instructionPC 2336 = 3034 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2049 : CycleSubmission.Artifact.artifact.instructionPC 2337 = 3037 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2050 : CycleSubmission.Artifact.artifact.instructionPC 2338 = 3038 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2051 : CycleSubmission.Artifact.artifact.instructionPC 2339 = 3041 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2052 : CycleSubmission.Artifact.artifact.instructionPC 2340 = 3042 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2053 : CycleSubmission.Artifact.artifact.instructionPC 2341 = 3045 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2054 : CycleSubmission.Artifact.artifact.instructionPC 2342 = 3046 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2055 : CycleSubmission.Artifact.artifact.instructionPC 2343 = 3049 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2056 : CycleSubmission.Artifact.artifact.instructionPC 2344 = 3050 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2057 : CycleSubmission.Artifact.artifact.instructionPC 2345 = 3053 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2058 : CycleSubmission.Artifact.artifact.instructionPC 2346 = 3054 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2059 : CycleSubmission.Artifact.artifact.instructionPC 2347 = 3057 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2060 : CycleSubmission.Artifact.artifact.instructionPC 2348 = 3058 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2061 : CycleSubmission.Artifact.artifact.instructionPC 2349 = 3061 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2062 : CycleSubmission.Artifact.artifact.instructionPC 2350 = 3062 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2063 : CycleSubmission.Artifact.artifact.instructionPC 2351 = 3065 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2064 : CycleSubmission.Artifact.artifact.instructionPC 2352 = 3066 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2065 : CycleSubmission.Artifact.artifact.instructionPC 2353 = 3067 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2066 : CycleSubmission.Artifact.artifact.instructionPC 2354 = 3068 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2067 : CycleSubmission.Artifact.artifact.instructionPC 2354 = 3068 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2068 : CycleSubmission.Artifact.artifact.instructionPC 2355 = 3071 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2069 : CycleSubmission.Artifact.artifact.instructionPC 2356 = 3072 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2070 : CycleSubmission.Artifact.artifact.instructionPC 2357 = 3076 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2071 : CycleSubmission.Artifact.artifact.instructionPC 2358 = 3077 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2072 : CycleSubmission.Artifact.artifact.instructionPC 2359 = 3078 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2073 : CycleSubmission.Artifact.artifact.instructionPC 2360 = 3081 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2074 : CycleSubmission.Artifact.artifact.instructionPC 2361 = 3082 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2075 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3083 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2076 : CycleSubmission.Artifact.artifact.instructionPC 2363 = 3084 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2077 : CycleSubmission.Artifact.artifact.instructionPC 2364 = 3086 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2078 : CycleSubmission.Artifact.artifact.instructionPC 2365 = 3087 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2079 : CycleSubmission.Artifact.artifact.instructionPC 2366 = 3088 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2080 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3089 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2081 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3090 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2082 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3091 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2083 : CycleSubmission.Artifact.artifact.instructionPC 2370 = 3093 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2084 : CycleSubmission.Artifact.artifact.instructionPC 2371 = 3094 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2085 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2086 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2087 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2088 : CycleSubmission.Artifact.artifact.instructionPC 2373 = 3096 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2089 : CycleSubmission.Artifact.artifact.instructionPC 2374 = 3097 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2090 : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3099 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2091 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3100 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2092 : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3101 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyPC2093 : CycleSubmission.Artifact.artifact.instructionPC 2378 = 3102 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestCacheNormal : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3090 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2368 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
end CycleSubmission.Global.Fast.Shift

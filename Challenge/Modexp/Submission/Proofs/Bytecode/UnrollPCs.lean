import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The first seven bit bodies retain seventeen instructions each; the last retains fifteen. Certificate names are stable API names, while their indices and PCs bind the selected artifact.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

open YulEvmCompiler

private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) = p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 495 = 599 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 496 = 602 := by
  calc
    Artifact.submissionArtifact.instructionPC 496 =
        Artifact.submissionArtifact.instructionPC 495 +
          (YulEvmCompiler.Instr.push 2 2944).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 462 _ (by rfl)
    _ = 556 := by rw [pc485]; rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2170 = 2811 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2171 = 2812 := by
  calc
    Artifact.submissionArtifact.instructionPC 2171 =
        Artifact.submissionArtifact.instructionPC 2170 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2274 _ (by rfl)
    _ = 2945 := by rw [pc2414]; rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2172 = 2814 := by
  calc
    Artifact.submissionArtifact.instructionPC 2172 =
        Artifact.submissionArtifact.instructionPC 2171 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2275 _ (by rfl)
    _ = 2947 := by rw [pc2415]; rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2173 = 2815 := by
  calc
    Artifact.submissionArtifact.instructionPC 2173 =
        Artifact.submissionArtifact.instructionPC 2172 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2276 _ (by rfl)
    _ = 2948 := by rw [pc2416]; rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2174 = 2816 := by
  calc
    Artifact.submissionArtifact.instructionPC 2174 =
        Artifact.submissionArtifact.instructionPC 2173 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2277 _ (by rfl)
    _ = 2949 := by rw [pc2417]; rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2175 = 2817 := by
  calc
    Artifact.submissionArtifact.instructionPC 2175 =
        Artifact.submissionArtifact.instructionPC 2174 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2278 _ (by rfl)
    _ = 2950 := by rw [pc2418]; rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2176 = 2819 := by
  calc
    Artifact.submissionArtifact.instructionPC 2176 =
        Artifact.submissionArtifact.instructionPC 2175 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2279 _ (by rfl)
    _ = 2952 := by rw [pc2419]; rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2177 = 2820 := by
  calc
    Artifact.submissionArtifact.instructionPC 2177 =
        Artifact.submissionArtifact.instructionPC 2176 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2280 _ (by rfl)
    _ = 2953 := by rw [pc2420]; rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2178 = 2822 := by
  calc
    Artifact.submissionArtifact.instructionPC 2178 =
        Artifact.submissionArtifact.instructionPC 2177 +
          (YulEvmCompiler.Instr.push 1 7).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2281 _ (by rfl)
    _ = 2955 := by rw [pc2421]; rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2179 = 2823 := by
  calc
    Artifact.submissionArtifact.instructionPC 2179 =
        Artifact.submissionArtifact.instructionPC 2178 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2282 _ (by rfl)
    _ = 2956 := by rw [pc2422]; rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2180 = 2824 := by
  calc
    Artifact.submissionArtifact.instructionPC 2180 =
        Artifact.submissionArtifact.instructionPC 2179 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2283 _ (by rfl)
    _ = 2957 := by rw [pc2423]; rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2181 = 2825 := by
  calc
    Artifact.submissionArtifact.instructionPC 2181 =
        Artifact.submissionArtifact.instructionPC 2180 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2284 _ (by rfl)
    _ = 2958 := by rw [pc2424]; rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2182 = 2826 := by
  calc
    Artifact.submissionArtifact.instructionPC 2182 =
        Artifact.submissionArtifact.instructionPC 2181 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2285 _ (by rfl)
    _ = 2959 := by rw [pc2425]; rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2183 = 2828 := by
  calc
    Artifact.submissionArtifact.instructionPC 2183 =
        Artifact.submissionArtifact.instructionPC 2182 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2286 _ (by rfl)
    _ = 2961 := by rw [pc2426]; rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2184 = 2829 := by
  calc
    Artifact.submissionArtifact.instructionPC 2184 =
        Artifact.submissionArtifact.instructionPC 2183 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2287 _ (by rfl)
    _ = 2962 := by rw [pc2427]; rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2185 = 2830 := by
  calc
    Artifact.submissionArtifact.instructionPC 2185 =
        Artifact.submissionArtifact.instructionPC 2184 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2288 _ (by rfl)
    _ = 2963 := by rw [pc2428]; rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2186 = 2831 := by
  calc
    Artifact.submissionArtifact.instructionPC 2186 =
        Artifact.submissionArtifact.instructionPC 2185 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2289 _ (by rfl)
    _ = 2964 := by rw [pc2429]; rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2187 = 2832 := by
  calc
    Artifact.submissionArtifact.instructionPC 2187 =
        Artifact.submissionArtifact.instructionPC 2186 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2290 _ (by rfl)
    _ = 2965 := by rw [pc2430]; rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2188 = 2833 := by
  calc
    Artifact.submissionArtifact.instructionPC 2188 =
        Artifact.submissionArtifact.instructionPC 2187 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2291 _ (by rfl)
    _ = 2966 := by rw [pc2431]; rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2189 = 2834 := by
  calc
    Artifact.submissionArtifact.instructionPC 2189 =
        Artifact.submissionArtifact.instructionPC 2188 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2292 _ (by rfl)
    _ = 2967 := by rw [pc2432]; rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2190 = 2835 := by
  calc
    Artifact.submissionArtifact.instructionPC 2190 =
        Artifact.submissionArtifact.instructionPC 2189 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2293 _ (by rfl)
    _ = 2968 := by rw [pc2433]; rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2191 = 2836 := by
  calc
    Artifact.submissionArtifact.instructionPC 2191 =
        Artifact.submissionArtifact.instructionPC 2190 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2294 _ (by rfl)
    _ = 2969 := by rw [pc2434]; rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2192 = 2837 := by
  calc
    Artifact.submissionArtifact.instructionPC 2192 =
        Artifact.submissionArtifact.instructionPC 2191 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2295 _ (by rfl)
    _ = 2970 := by rw [pc2435]; rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2193 = 2839 := by
  calc
    Artifact.submissionArtifact.instructionPC 2193 =
        Artifact.submissionArtifact.instructionPC 2192 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2296 _ (by rfl)
    _ = 2972 := by rw [pc2436]; rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2194 = 2840 := by
  calc
    Artifact.submissionArtifact.instructionPC 2194 =
        Artifact.submissionArtifact.instructionPC 2193 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2297 _ (by rfl)
    _ = 2973 := by rw [pc2437]; rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2195 = 2842 := by
  calc
    Artifact.submissionArtifact.instructionPC 2195 =
        Artifact.submissionArtifact.instructionPC 2194 +
          (YulEvmCompiler.Instr.push 1 6).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2298 _ (by rfl)
    _ = 2975 := by rw [pc2438]; rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2196 = 2843 := by
  calc
    Artifact.submissionArtifact.instructionPC 2196 =
        Artifact.submissionArtifact.instructionPC 2195 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2299 _ (by rfl)
    _ = 2976 := by rw [pc2439]; rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2197 = 2844 := by
  calc
    Artifact.submissionArtifact.instructionPC 2197 =
        Artifact.submissionArtifact.instructionPC 2196 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2300 _ (by rfl)
    _ = 2977 := by rw [pc2440]; rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2198 = 2845 := by
  calc
    Artifact.submissionArtifact.instructionPC 2198 =
        Artifact.submissionArtifact.instructionPC 2197 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2301 _ (by rfl)
    _ = 2978 := by rw [pc2441]; rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2199 = 2846 := by
  calc
    Artifact.submissionArtifact.instructionPC 2199 =
        Artifact.submissionArtifact.instructionPC 2198 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2302 _ (by rfl)
    _ = 2979 := by rw [pc2442]; rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2200 = 2848 := by
  calc
    Artifact.submissionArtifact.instructionPC 2200 =
        Artifact.submissionArtifact.instructionPC 2199 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2303 _ (by rfl)
    _ = 2981 := by rw [pc2443]; rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2201 = 2849 := by
  calc
    Artifact.submissionArtifact.instructionPC 2201 =
        Artifact.submissionArtifact.instructionPC 2200 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2304 _ (by rfl)
    _ = 2982 := by rw [pc2444]; rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2202 = 2850 := by
  calc
    Artifact.submissionArtifact.instructionPC 2202 =
        Artifact.submissionArtifact.instructionPC 2201 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2305 _ (by rfl)
    _ = 2983 := by rw [pc2445]; rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2203 = 2851 := by
  calc
    Artifact.submissionArtifact.instructionPC 2203 =
        Artifact.submissionArtifact.instructionPC 2202 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2306 _ (by rfl)
    _ = 2984 := by rw [pc2446]; rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2204 = 2852 := by
  calc
    Artifact.submissionArtifact.instructionPC 2204 =
        Artifact.submissionArtifact.instructionPC 2203 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2307 _ (by rfl)
    _ = 2985 := by rw [pc2447]; rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2205 = 2853 := by
  calc
    Artifact.submissionArtifact.instructionPC 2205 =
        Artifact.submissionArtifact.instructionPC 2204 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2308 _ (by rfl)
    _ = 2986 := by rw [pc2448]; rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2206 = 2854 := by
  calc
    Artifact.submissionArtifact.instructionPC 2206 =
        Artifact.submissionArtifact.instructionPC 2205 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2309 _ (by rfl)
    _ = 2987 := by rw [pc2449]; rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2207 = 2855 := by
  calc
    Artifact.submissionArtifact.instructionPC 2207 =
        Artifact.submissionArtifact.instructionPC 2206 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2310 _ (by rfl)
    _ = 2988 := by rw [pc2450]; rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2208 = 2856 := by
  calc
    Artifact.submissionArtifact.instructionPC 2208 =
        Artifact.submissionArtifact.instructionPC 2207 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2311 _ (by rfl)
    _ = 2989 := by rw [pc2451]; rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2209 = 2857 := by
  calc
    Artifact.submissionArtifact.instructionPC 2209 =
        Artifact.submissionArtifact.instructionPC 2208 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2312 _ (by rfl)
    _ = 2990 := by rw [pc2452]; rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2210 = 2859 := by
  calc
    Artifact.submissionArtifact.instructionPC 2210 =
        Artifact.submissionArtifact.instructionPC 2209 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2313 _ (by rfl)
    _ = 2992 := by rw [pc2453]; rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2211 = 2860 := by
  calc
    Artifact.submissionArtifact.instructionPC 2211 =
        Artifact.submissionArtifact.instructionPC 2210 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2314 _ (by rfl)
    _ = 2993 := by rw [pc2454]; rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2212 = 2862 := by
  calc
    Artifact.submissionArtifact.instructionPC 2212 =
        Artifact.submissionArtifact.instructionPC 2211 +
          (YulEvmCompiler.Instr.push 1 5).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2315 _ (by rfl)
    _ = 2995 := by rw [pc2455]; rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2213 = 2863 := by
  calc
    Artifact.submissionArtifact.instructionPC 2213 =
        Artifact.submissionArtifact.instructionPC 2212 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2316 _ (by rfl)
    _ = 2996 := by rw [pc2456]; rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2214 = 2864 := by
  calc
    Artifact.submissionArtifact.instructionPC 2214 =
        Artifact.submissionArtifact.instructionPC 2213 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2317 _ (by rfl)
    _ = 2997 := by rw [pc2457]; rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2215 = 2865 := by
  calc
    Artifact.submissionArtifact.instructionPC 2215 =
        Artifact.submissionArtifact.instructionPC 2214 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2318 _ (by rfl)
    _ = 2998 := by rw [pc2458]; rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2216 = 2866 := by
  calc
    Artifact.submissionArtifact.instructionPC 2216 =
        Artifact.submissionArtifact.instructionPC 2215 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2319 _ (by rfl)
    _ = 2999 := by rw [pc2459]; rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2217 = 2868 := by
  calc
    Artifact.submissionArtifact.instructionPC 2217 =
        Artifact.submissionArtifact.instructionPC 2216 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2320 _ (by rfl)
    _ = 3001 := by rw [pc2460]; rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2218 = 2869 := by
  calc
    Artifact.submissionArtifact.instructionPC 2218 =
        Artifact.submissionArtifact.instructionPC 2217 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2321 _ (by rfl)
    _ = 3002 := by rw [pc2461]; rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2219 = 2870 := by
  calc
    Artifact.submissionArtifact.instructionPC 2219 =
        Artifact.submissionArtifact.instructionPC 2218 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2322 _ (by rfl)
    _ = 3003 := by rw [pc2462]; rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2220 = 2871 := by
  calc
    Artifact.submissionArtifact.instructionPC 2220 =
        Artifact.submissionArtifact.instructionPC 2219 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2323 _ (by rfl)
    _ = 3004 := by rw [pc2463]; rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2221 = 2872 := by
  calc
    Artifact.submissionArtifact.instructionPC 2221 =
        Artifact.submissionArtifact.instructionPC 2220 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2324 _ (by rfl)
    _ = 3005 := by rw [pc2464]; rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2222 = 2873 := by
  calc
    Artifact.submissionArtifact.instructionPC 2222 =
        Artifact.submissionArtifact.instructionPC 2221 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2325 _ (by rfl)
    _ = 3006 := by rw [pc2465]; rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2223 = 2874 := by
  calc
    Artifact.submissionArtifact.instructionPC 2223 =
        Artifact.submissionArtifact.instructionPC 2222 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2326 _ (by rfl)
    _ = 3007 := by rw [pc2466]; rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2224 = 2875 := by
  calc
    Artifact.submissionArtifact.instructionPC 2224 =
        Artifact.submissionArtifact.instructionPC 2223 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2327 _ (by rfl)
    _ = 3008 := by rw [pc2467]; rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2225 = 2876 := by
  calc
    Artifact.submissionArtifact.instructionPC 2225 =
        Artifact.submissionArtifact.instructionPC 2224 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2328 _ (by rfl)
    _ = 3009 := by rw [pc2468]; rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2226 = 2877 := by
  calc
    Artifact.submissionArtifact.instructionPC 2226 =
        Artifact.submissionArtifact.instructionPC 2225 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2329 _ (by rfl)
    _ = 3010 := by rw [pc2469]; rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2227 = 2879 := by
  calc
    Artifact.submissionArtifact.instructionPC 2227 =
        Artifact.submissionArtifact.instructionPC 2226 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2330 _ (by rfl)
    _ = 3012 := by rw [pc2470]; rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2228 = 2880 := by
  calc
    Artifact.submissionArtifact.instructionPC 2228 =
        Artifact.submissionArtifact.instructionPC 2227 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2331 _ (by rfl)
    _ = 3013 := by rw [pc2471]; rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2229 = 2882 := by
  calc
    Artifact.submissionArtifact.instructionPC 2229 =
        Artifact.submissionArtifact.instructionPC 2228 +
          (YulEvmCompiler.Instr.push 1 4).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2332 _ (by rfl)
    _ = 3015 := by rw [pc2472]; rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2230 = 2883 := by
  calc
    Artifact.submissionArtifact.instructionPC 2230 =
        Artifact.submissionArtifact.instructionPC 2229 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2333 _ (by rfl)
    _ = 3016 := by rw [pc2473]; rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2231 = 2884 := by
  calc
    Artifact.submissionArtifact.instructionPC 2231 =
        Artifact.submissionArtifact.instructionPC 2230 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2334 _ (by rfl)
    _ = 3017 := by rw [pc2474]; rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2232 = 2885 := by
  calc
    Artifact.submissionArtifact.instructionPC 2232 =
        Artifact.submissionArtifact.instructionPC 2231 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2335 _ (by rfl)
    _ = 3018 := by rw [pc2475]; rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2233 = 2886 := by
  calc
    Artifact.submissionArtifact.instructionPC 2233 =
        Artifact.submissionArtifact.instructionPC 2232 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2336 _ (by rfl)
    _ = 3019 := by rw [pc2476]; rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2234 = 2888 := by
  calc
    Artifact.submissionArtifact.instructionPC 2234 =
        Artifact.submissionArtifact.instructionPC 2233 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2337 _ (by rfl)
    _ = 3021 := by rw [pc2477]; rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2235 = 2889 := by
  calc
    Artifact.submissionArtifact.instructionPC 2235 =
        Artifact.submissionArtifact.instructionPC 2234 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2338 _ (by rfl)
    _ = 3022 := by rw [pc2478]; rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2236 = 2890 := by
  calc
    Artifact.submissionArtifact.instructionPC 2236 =
        Artifact.submissionArtifact.instructionPC 2235 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2339 _ (by rfl)
    _ = 3023 := by rw [pc2479]; rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2237 = 2891 := by
  calc
    Artifact.submissionArtifact.instructionPC 2237 =
        Artifact.submissionArtifact.instructionPC 2236 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2340 _ (by rfl)
    _ = 3024 := by rw [pc2480]; rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2238 = 2892 := by
  calc
    Artifact.submissionArtifact.instructionPC 2238 =
        Artifact.submissionArtifact.instructionPC 2237 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2341 _ (by rfl)
    _ = 3025 := by rw [pc2481]; rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2239 = 2893 := by
  calc
    Artifact.submissionArtifact.instructionPC 2239 =
        Artifact.submissionArtifact.instructionPC 2238 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2342 _ (by rfl)
    _ = 3026 := by rw [pc2482]; rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2240 = 2894 := by
  calc
    Artifact.submissionArtifact.instructionPC 2240 =
        Artifact.submissionArtifact.instructionPC 2239 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2343 _ (by rfl)
    _ = 3027 := by rw [pc2483]; rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2241 = 2895 := by
  calc
    Artifact.submissionArtifact.instructionPC 2241 =
        Artifact.submissionArtifact.instructionPC 2240 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2344 _ (by rfl)
    _ = 3028 := by rw [pc2484]; rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2242 = 2896 := by
  calc
    Artifact.submissionArtifact.instructionPC 2242 =
        Artifact.submissionArtifact.instructionPC 2241 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2345 _ (by rfl)
    _ = 3029 := by rw [pc2485]; rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2243 = 2897 := by
  calc
    Artifact.submissionArtifact.instructionPC 2243 =
        Artifact.submissionArtifact.instructionPC 2242 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2346 _ (by rfl)
    _ = 3030 := by rw [pc2486]; rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2244 = 2899 := by
  calc
    Artifact.submissionArtifact.instructionPC 2244 =
        Artifact.submissionArtifact.instructionPC 2243 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2347 _ (by rfl)
    _ = 3032 := by rw [pc2487]; rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2245 = 2900 := by
  calc
    Artifact.submissionArtifact.instructionPC 2245 =
        Artifact.submissionArtifact.instructionPC 2244 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2348 _ (by rfl)
    _ = 3033 := by rw [pc2488]; rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2246 = 2902 := by
  calc
    Artifact.submissionArtifact.instructionPC 2246 =
        Artifact.submissionArtifact.instructionPC 2245 +
          (YulEvmCompiler.Instr.push 1 3).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2349 _ (by rfl)
    _ = 3035 := by rw [pc2489]; rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2247 = 2903 := by
  calc
    Artifact.submissionArtifact.instructionPC 2247 =
        Artifact.submissionArtifact.instructionPC 2246 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2350 _ (by rfl)
    _ = 3036 := by rw [pc2490]; rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2248 = 2904 := by
  calc
    Artifact.submissionArtifact.instructionPC 2248 =
        Artifact.submissionArtifact.instructionPC 2247 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2351 _ (by rfl)
    _ = 3037 := by rw [pc2491]; rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2249 = 2905 := by
  calc
    Artifact.submissionArtifact.instructionPC 2249 =
        Artifact.submissionArtifact.instructionPC 2248 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2352 _ (by rfl)
    _ = 3038 := by rw [pc2492]; rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2250 = 2906 := by
  calc
    Artifact.submissionArtifact.instructionPC 2250 =
        Artifact.submissionArtifact.instructionPC 2249 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2353 _ (by rfl)
    _ = 3039 := by rw [pc2493]; rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2251 = 2908 := by
  calc
    Artifact.submissionArtifact.instructionPC 2251 =
        Artifact.submissionArtifact.instructionPC 2250 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2354 _ (by rfl)
    _ = 3041 := by rw [pc2494]; rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2252 = 2909 := by
  calc
    Artifact.submissionArtifact.instructionPC 2252 =
        Artifact.submissionArtifact.instructionPC 2251 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2355 _ (by rfl)
    _ = 3042 := by rw [pc2495]; rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2253 = 2910 := by
  calc
    Artifact.submissionArtifact.instructionPC 2253 =
        Artifact.submissionArtifact.instructionPC 2252 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2356 _ (by rfl)
    _ = 3043 := by rw [pc2496]; rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2254 = 2911 := by
  calc
    Artifact.submissionArtifact.instructionPC 2254 =
        Artifact.submissionArtifact.instructionPC 2253 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2357 _ (by rfl)
    _ = 3044 := by rw [pc2497]; rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2255 = 2912 := by
  calc
    Artifact.submissionArtifact.instructionPC 2255 =
        Artifact.submissionArtifact.instructionPC 2254 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2358 _ (by rfl)
    _ = 3045 := by rw [pc2498]; rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2256 = 2913 := by
  calc
    Artifact.submissionArtifact.instructionPC 2256 =
        Artifact.submissionArtifact.instructionPC 2255 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2359 _ (by rfl)
    _ = 3046 := by rw [pc2499]; rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2257 = 2914 := by
  calc
    Artifact.submissionArtifact.instructionPC 2257 =
        Artifact.submissionArtifact.instructionPC 2256 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2360 _ (by rfl)
    _ = 3047 := by rw [pc2500]; rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2258 = 2915 := by
  calc
    Artifact.submissionArtifact.instructionPC 2258 =
        Artifact.submissionArtifact.instructionPC 2257 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2361 _ (by rfl)
    _ = 3048 := by rw [pc2501]; rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2259 = 2916 := by
  calc
    Artifact.submissionArtifact.instructionPC 2259 =
        Artifact.submissionArtifact.instructionPC 2258 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2362 _ (by rfl)
    _ = 3049 := by rw [pc2502]; rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2260 = 2917 := by
  calc
    Artifact.submissionArtifact.instructionPC 2260 =
        Artifact.submissionArtifact.instructionPC 2259 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2363 _ (by rfl)
    _ = 3050 := by rw [pc2503]; rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2261 = 2919 := by
  calc
    Artifact.submissionArtifact.instructionPC 2261 =
        Artifact.submissionArtifact.instructionPC 2260 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2364 _ (by rfl)
    _ = 3052 := by rw [pc2504]; rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2262 = 2920 := by
  calc
    Artifact.submissionArtifact.instructionPC 2262 =
        Artifact.submissionArtifact.instructionPC 2261 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2365 _ (by rfl)
    _ = 3053 := by rw [pc2505]; rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2263 = 2922 := by
  calc
    Artifact.submissionArtifact.instructionPC 2263 =
        Artifact.submissionArtifact.instructionPC 2262 +
          (YulEvmCompiler.Instr.push 1 2).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2366 _ (by rfl)
    _ = 3055 := by rw [pc2506]; rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2264 = 2923 := by
  calc
    Artifact.submissionArtifact.instructionPC 2264 =
        Artifact.submissionArtifact.instructionPC 2263 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2367 _ (by rfl)
    _ = 3056 := by rw [pc2507]; rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2265 = 2924 := by
  calc
    Artifact.submissionArtifact.instructionPC 2265 =
        Artifact.submissionArtifact.instructionPC 2264 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2368 _ (by rfl)
    _ = 3057 := by rw [pc2508]; rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2266 = 2925 := by
  calc
    Artifact.submissionArtifact.instructionPC 2266 =
        Artifact.submissionArtifact.instructionPC 2265 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2369 _ (by rfl)
    _ = 3058 := by rw [pc2509]; rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2267 = 2926 := by
  calc
    Artifact.submissionArtifact.instructionPC 2267 =
        Artifact.submissionArtifact.instructionPC 2266 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2370 _ (by rfl)
    _ = 3059 := by rw [pc2510]; rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2268 = 2928 := by
  calc
    Artifact.submissionArtifact.instructionPC 2268 =
        Artifact.submissionArtifact.instructionPC 2267 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2371 _ (by rfl)
    _ = 3061 := by rw [pc2511]; rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2269 = 2929 := by
  calc
    Artifact.submissionArtifact.instructionPC 2269 =
        Artifact.submissionArtifact.instructionPC 2268 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2372 _ (by rfl)
    _ = 3062 := by rw [pc2512]; rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2270 = 2930 := by
  calc
    Artifact.submissionArtifact.instructionPC 2270 =
        Artifact.submissionArtifact.instructionPC 2269 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2373 _ (by rfl)
    _ = 3063 := by rw [pc2513]; rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2271 = 2931 := by
  calc
    Artifact.submissionArtifact.instructionPC 2271 =
        Artifact.submissionArtifact.instructionPC 2270 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2374 _ (by rfl)
    _ = 3064 := by rw [pc2514]; rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2272 = 2932 := by
  calc
    Artifact.submissionArtifact.instructionPC 2272 =
        Artifact.submissionArtifact.instructionPC 2271 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2375 _ (by rfl)
    _ = 3065 := by rw [pc2515]; rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2273 = 2933 := by
  calc
    Artifact.submissionArtifact.instructionPC 2273 =
        Artifact.submissionArtifact.instructionPC 2272 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2376 _ (by rfl)
    _ = 3066 := by rw [pc2516]; rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2274 = 2934 := by
  calc
    Artifact.submissionArtifact.instructionPC 2274 =
        Artifact.submissionArtifact.instructionPC 2273 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2377 _ (by rfl)
    _ = 3067 := by rw [pc2517]; rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2275 = 2935 := by
  calc
    Artifact.submissionArtifact.instructionPC 2275 =
        Artifact.submissionArtifact.instructionPC 2274 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2378 _ (by rfl)
    _ = 3068 := by rw [pc2518]; rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2276 = 2936 := by
  calc
    Artifact.submissionArtifact.instructionPC 2276 =
        Artifact.submissionArtifact.instructionPC 2275 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2379 _ (by rfl)
    _ = 3069 := by rw [pc2519]; rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2277 = 2937 := by
  calc
    Artifact.submissionArtifact.instructionPC 2277 =
        Artifact.submissionArtifact.instructionPC 2276 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2380 _ (by rfl)
    _ = 3070 := by rw [pc2520]; rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2278 = 2939 := by
  calc
    Artifact.submissionArtifact.instructionPC 2278 =
        Artifact.submissionArtifact.instructionPC 2277 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2381 _ (by rfl)
    _ = 3072 := by rw [pc2521]; rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2279 = 2940 := by
  calc
    Artifact.submissionArtifact.instructionPC 2279 =
        Artifact.submissionArtifact.instructionPC 2278 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2382 _ (by rfl)
    _ = 3073 := by rw [pc2522]; rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2280 = 2942 := by
  calc
    Artifact.submissionArtifact.instructionPC 2280 =
        Artifact.submissionArtifact.instructionPC 2279 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2383 _ (by rfl)
    _ = 3075 := by rw [pc2523]; rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2281 = 2943 := by
  calc
    Artifact.submissionArtifact.instructionPC 2281 =
        Artifact.submissionArtifact.instructionPC 2280 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.SHR).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2384 _ (by rfl)
    _ = 3076 := by rw [pc2524]; rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2282 = 2944 := by
  calc
    Artifact.submissionArtifact.instructionPC 2282 =
        Artifact.submissionArtifact.instructionPC 2281 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2385 _ (by rfl)
    _ = 3077 := by rw [pc2525]; rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2283 = 2945 := by
  calc
    Artifact.submissionArtifact.instructionPC 2283 =
        Artifact.submissionArtifact.instructionPC 2282 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2386 _ (by rfl)
    _ = 3078 := by rw [pc2526]; rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2284 = 2946 := by
  calc
    Artifact.submissionArtifact.instructionPC 2284 =
        Artifact.submissionArtifact.instructionPC 2283 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2387 _ (by rfl)
    _ = 3079 := by rw [pc2527]; rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2285 = 2948 := by
  calc
    Artifact.submissionArtifact.instructionPC 2285 =
        Artifact.submissionArtifact.instructionPC 2284 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2388 _ (by rfl)
    _ = 3081 := by rw [pc2528]; rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2286 = 2949 := by
  calc
    Artifact.submissionArtifact.instructionPC 2286 =
        Artifact.submissionArtifact.instructionPC 2285 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2389 _ (by rfl)
    _ = 3082 := by rw [pc2529]; rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2287 = 2950 := by
  calc
    Artifact.submissionArtifact.instructionPC 2287 =
        Artifact.submissionArtifact.instructionPC 2286 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2390 _ (by rfl)
    _ = 3083 := by rw [pc2530]; rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2288 = 2951 := by
  calc
    Artifact.submissionArtifact.instructionPC 2288 =
        Artifact.submissionArtifact.instructionPC 2287 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2391 _ (by rfl)
    _ = 3084 := by rw [pc2531]; rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2289 = 2952 := by
  calc
    Artifact.submissionArtifact.instructionPC 2289 =
        Artifact.submissionArtifact.instructionPC 2288 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2392 _ (by rfl)
    _ = 3085 := by rw [pc2532]; rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2290 = 2953 := by
  calc
    Artifact.submissionArtifact.instructionPC 2290 =
        Artifact.submissionArtifact.instructionPC 2289 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2393 _ (by rfl)
    _ = 3086 := by rw [pc2533]; rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2291 = 2954 := by
  calc
    Artifact.submissionArtifact.instructionPC 2291 =
        Artifact.submissionArtifact.instructionPC 2290 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2394 _ (by rfl)
    _ = 3087 := by rw [pc2534]; rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2292 = 2955 := by
  calc
    Artifact.submissionArtifact.instructionPC 2292 =
        Artifact.submissionArtifact.instructionPC 2291 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2395 _ (by rfl)
    _ = 3088 := by rw [pc2535]; rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2293 = 2956 := by
  calc
    Artifact.submissionArtifact.instructionPC 2293 =
        Artifact.submissionArtifact.instructionPC 2292 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2396 _ (by rfl)
    _ = 3089 := by rw [pc2536]; rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2294 = 2957 := by
  calc
    Artifact.submissionArtifact.instructionPC 2294 =
        Artifact.submissionArtifact.instructionPC 2293 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 7 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2397 _ (by rfl)
    _ = 3090 := by rw [pc2537]; rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2295 = 2959 := by
  calc
    Artifact.submissionArtifact.instructionPC 2295 =
        Artifact.submissionArtifact.instructionPC 2294 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2398 _ (by rfl)
    _ = 3092 := by rw [pc2538]; rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2296 = 2960 := by
  calc
    Artifact.submissionArtifact.instructionPC 2296 =
        Artifact.submissionArtifact.instructionPC 2295 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2399 _ (by rfl)
    _ = 3093 := by rw [pc2539]; rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2297 = 2961 := by
  calc
    Artifact.submissionArtifact.instructionPC 2297 =
        Artifact.submissionArtifact.instructionPC 2296 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.AND).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2400 _ (by rfl)
    _ = 3094 := by rw [pc2542]; rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2298 = 2962 := by
  calc
    Artifact.submissionArtifact.instructionPC 2298 =
        Artifact.submissionArtifact.instructionPC 2297 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2401 _ (by rfl)
    _ = 3095 := by rw [pc2543]; rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2299 = 2963 := by
  calc
    Artifact.submissionArtifact.instructionPC 2299 =
        Artifact.submissionArtifact.instructionPC 2298 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2402 _ (by rfl)
    _ = 3096 := by rw [pc2544]; rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2300 = 2965 := by
  calc
    Artifact.submissionArtifact.instructionPC 2300 =
        Artifact.submissionArtifact.instructionPC 2299 +
          (YulEvmCompiler.Instr.push 1 1).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2403 _ (by rfl)
    _ = 3098 := by rw [pc2545]; rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2301 = 2966 := by
  calc
    Artifact.submissionArtifact.instructionPC 2301 =
        Artifact.submissionArtifact.instructionPC 2300 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2404 _ (by rfl)
    _ = 3099 := by rw [pc2546]; rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2302 = 2967 := by
  calc
    Artifact.submissionArtifact.instructionPC 2302 =
        Artifact.submissionArtifact.instructionPC 2301 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2405 _ (by rfl)
    _ = 3100 := by rw [pc2547]; rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2303 = 2968 := by
  calc
    Artifact.submissionArtifact.instructionPC 2303 =
        Artifact.submissionArtifact.instructionPC 2302 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 8 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2406 _ (by rfl)
    _ = 3101 := by rw [pc2548]; rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2304 = 2969 := by
  calc
    Artifact.submissionArtifact.instructionPC 2304 =
        Artifact.submissionArtifact.instructionPC 2303 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2407 _ (by rfl)
    _ = 3102 := by rw [pc2549]; rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2305 = 2970 := by
  calc
    Artifact.submissionArtifact.instructionPC 2305 =
        Artifact.submissionArtifact.instructionPC 2304 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2408 _ (by rfl)
    _ = 3103 := by rw [pc2550]; rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2306 = 2971 := by
  calc
    Artifact.submissionArtifact.instructionPC 2306 =
        Artifact.submissionArtifact.instructionPC 2305 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2409 _ (by rfl)
    _ = 3104 := by rw [pc2551]; rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2307 = 2972 := by
  calc
    Artifact.submissionArtifact.instructionPC 2307 =
        Artifact.submissionArtifact.instructionPC 2306 +
          (YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 })).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2410 _ (by rfl)
    _ = 3105 := by rw [pc2552]; rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2308 = 2973 := by
  calc
    Artifact.submissionArtifact.instructionPC 2308 =
        Artifact.submissionArtifact.instructionPC 2307 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2411 _ (by rfl)
    _ = 3106 := by rw [pc2553]; rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2309 = 2974 := by
  calc
    Artifact.submissionArtifact.instructionPC 2309 =
        Artifact.submissionArtifact.instructionPC 2308 +
          (YulEvmCompiler.Instr.op EvmSemantics.Operation.POP).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2412 _ (by rfl)
    _ = 3107 := by rw [pc2554]; rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2310 = 2977 := by
  calc
    Artifact.submissionArtifact.instructionPC 2310 =
        Artifact.submissionArtifact.instructionPC 2309 +
          (YulEvmCompiler.Instr.push 2 557).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2413 _ (by rfl)
    _ = 3110 := by rw [pc2555]; rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

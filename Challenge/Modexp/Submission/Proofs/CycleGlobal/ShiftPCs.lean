import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the appended shift-reduce blocks

Instruction indices 3001 .. 3664, one lemma each.
-/

namespace CycleSubmission.Global.ShiftPCs
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast


open EvmSemantics
open EvmSemantics.EVM

local notation "IPC" => CycleSubmission.Artifact.artifact.instructionPC

/-- An instruction pc by evaluating the byte length of the instruction prefix. -/
local macro "pc_by_len" : tactic =>
  `(tactic| (rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl))

open Lean in
/-- An instruction pc through a constant-offset `PrefixPC` segment and the accepted proof base's
lemma for the matching old index. -/
local macro "pc_by_old " seg:ident i:num old:ident : tactic =>
  let seg' := mkIdent (`CycleSubmission.Global.PrefixPC ++ seg.getId)
  let old' := mkIdent (`Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs ++ old.getId)
  `(tactic| (rw [$seg':ident $i (by decide) (by decide)]; exact $old':ident))

@[simp] theorem pc2545 : IPC 1868 = 2357 := by pc_by_len

@[simp] theorem pc2546 : IPC 1869 = 2358 := by pc_by_len

@[simp] theorem pc2547 : IPC 1870 = 2359 := by pc_by_len

@[simp] theorem pc2548 : IPC 1871 = 2360 := by pc_by_len

@[simp] theorem pc2556 : IPC 1872 = 2361 := by pc_by_len

@[simp] theorem pc2559 : IPC 1873 = 2363 := by pc_by_len

@[simp] theorem pc2560 : IPC 1874 = 2364 := by pc_by_len

@[simp] theorem pc2561 : IPC 1875 = 2365 := by pc_by_len

@[simp] theorem pc2563 : IPC 1876 = 2367 := by pc_by_len

@[simp] theorem pc2566 : IPC 1877 = 2370 := by pc_by_len


@[simp] theorem pc2567 : IPC 1878 = 2371 := by pc_by_len

@[simp] theorem pc2570 : IPC 1879 = 2374 := by pc_by_len

@[simp] theorem pc2574 : IPC 1881 = 2378 := by pc_by_len

@[simp] theorem pc2586 : IPC 1892 = 2397 := by pc_by_len

@[simp] theorem pc2591 : IPC 1898 = 2406 := by pc_by_len

@[simp] theorem pc2592 : IPC 1899 = 2407 := by pc_by_len



@[simp] theorem pc2600 : IPC 1927 = 2452 := by pc_by_len

@[simp] theorem pc2604 : IPC 1929 = 2454 := by pc_by_len



@[simp] theorem pc2618 : IPC 1933 = 2460 := by pc_by_len

@[simp] theorem pc2619 : IPC 1934 = 2461 := by pc_by_len

@[simp] theorem pc2620 : IPC 1935 = 2462 := by pc_by_len

@[simp] theorem pc2621 : IPC 1936 = 2463 := by pc_by_len

@[simp] theorem pc2622 : IPC 1937 = 2464 := by pc_by_len

@[simp] theorem pc2623 : IPC 1938 = 2465 := by pc_by_len

@[simp] theorem pc2624 : IPC 1939 = 2466 := by pc_by_len

@[simp] theorem pc2625 : IPC 1940 = 2467 := by pc_by_len

@[simp] theorem pc2628 : IPC 1941 = 2468 := by pc_by_len

@[simp] theorem pc2629 : IPC 1942 = 2469 := by pc_by_len

@[simp] theorem pc2631 : IPC 1943 = 2471 := by pc_by_len

@[simp] theorem pc2632 : IPC 1944 = 2472 := by pc_by_len

@[simp] theorem pc2633 : IPC 1945 = 2475 := by pc_by_len

@[simp] theorem pc2636 : IPC 1946 = 2476 := by pc_by_len

@[simp] theorem pc2637 : IPC 1947 = 2478 := by pc_by_len

@[simp] theorem pc2638 : IPC 1948 = 2479 := by pc_by_len

@[simp] theorem pc2639 : IPC 1949 = 2482 := by pc_by_len

@[simp] theorem pc2641 : IPC 1950 = 2483 := by pc_by_len

@[simp] theorem pc2642 : IPC 1951 = 2484 := by pc_by_len

@[simp] theorem pc2644 : IPC 1952 = 2485 := by pc_by_len

@[simp] theorem pc2645 : IPC 1953 = 2486 := by pc_by_len

@[simp] theorem pc2648 : IPC 1954 = 2489 := by pc_by_len

@[simp] theorem pc2649 : IPC 1955 = 2490 := by pc_by_len

@[simp] theorem pc2650 : IPC 1956 = 2491 := by pc_by_len

@[simp] theorem pc2651 : IPC 1957 = 2492 := by pc_by_len

@[simp] theorem pc2652 : IPC 1958 = 2493 := by pc_by_len

@[simp] theorem pc2653 : IPC 1959 = 2494 := by pc_by_len

@[simp] theorem pc2654 : IPC 1960 = 2495 := by pc_by_len

@[simp] theorem pc2657 : IPC 1961 = 2498 := by pc_by_len

@[simp] theorem pc2658 : IPC 1962 = 2499 := by pc_by_len

@[simp] theorem pc2659 : IPC 1963 = 2502 := by pc_by_len

@[simp] theorem pc2695 : IPC 2009 = 2556 := by pc_by_len

@[simp] theorem pc2696 : IPC 2010 = 2557 := by pc_by_len

@[simp] theorem pc2698 : IPC 2011 = 2558 := by pc_by_len

@[simp] theorem pc2699 : IPC 2012 = 2559 := by pc_by_len





@[simp] theorem pc2702 : IPC 2013 = 2562 := by pc_by_len

@[simp] theorem pc2703 : IPC 2014 = 2563 := by pc_by_len

@[simp] theorem pc2705 : IPC 2015 = 2564 := by pc_by_len

@[simp] theorem pc2706 : IPC 2016 = 2565 := by pc_by_len

@[simp] theorem pc2713 : IPC 2019 = 2570 := by pc_by_len

@[simp] theorem pc3009 : IPC 2228 = 2881 := by pc_by_len

@[simp] theorem pc3010 : IPC 2229 = 2882 := by pc_by_len

@[simp] theorem pc3011 : IPC 2230 = 2883 := by pc_by_len

@[simp] theorem pc3012 : IPC 2231 = 2884 := by pc_by_len

@[simp] theorem pc3013 : IPC 2232 = 2885 := by pc_by_len





@[simp] theorem pc2712 : IPC 2018 = 2569 := by pc_by_len

@[simp] theorem pc3125 : IPC 2324 = 2993 := by pc_by_len







@[simp] theorem pc3171 : IPC 2361 = 3036 := by pc_by_len

@[simp] theorem pc3174 : IPC 2362 = 3039 := by pc_by_len

@[simp] theorem pc3175 : IPC 2363 = 3040 := by pc_by_len

@[simp] theorem pc3176 : IPC 2364 = 3041 := by pc_by_len

@[simp] theorem pc3177 : IPC 2365 = 3042 := by pc_by_len

@[simp] theorem pc3178 : IPC 2366 = 3043 := by pc_by_len

@[simp] theorem pc3179 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3180 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3181 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3182 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3183 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3184 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3185 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3186 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3187 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3188 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3191 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pc3192 : IPC 2367 = 3051 := by pc_by_len




@[simp] theorem pcSaturate2992 : IPC 2309 = 2974 := by pc_by_len

@[simp] theorem pcSaturate2993 : IPC 2310 = 2975 := by pc_by_len

@[simp] theorem earlyExtraPC2883 : IPC 2639 = 3414 := by pc_by_len

@[simp] theorem earlyExtraPC2884 : IPC 2640 = 3415 := by pc_by_len

@[simp] theorem earlyExtraPC2885 : IPC 2641 = 3416 := by pc_by_len

@[simp] theorem earlyExtraPC2886 : IPC 2642 = 3417 := by pc_by_len

@[simp] theorem earlyExtraPC2888 : IPC 2643 = 3418 := by pc_by_len

@[simp] theorem earlyExtraPC2889 : IPC 2644 = 3419 := by pc_by_len

@[simp] theorem earlyExtraPC2890 : IPC 2645 = 3420 := by pc_by_len

@[simp] theorem earlyExtraPC2891 : IPC 2646 = 3423 := by pc_by_len

@[simp] theorem earlyExtraPC2892 : IPC 2647 = 3424 := by pc_by_len

@[simp] theorem earlyExtraPC2893 : IPC 2647 = 3424 := by pc_by_len

@[simp] theorem earlyExtraPC2894 : IPC 2648 = 3427 := by pc_by_len

@[simp] theorem earlyExtraPC2895 : IPC 2649 = 3428 := by pc_by_len

@[simp] theorem earlyExtraPC2896 : IPC 2661 = 3448 := by pc_by_len

@[simp] theorem earlyExtraPC2930 : IPC 2661 = 3448 := by pc_by_len

@[simp] theorem earlyExtraPC2931 : IPC 2661 = 3448 := by pc_by_len

@[simp] theorem earlyExtraPC2932 : IPC 2662 = 3451 := by pc_by_len

@[simp] theorem earlyExtraPC2933 : IPC 2663 = 3452 := by pc_by_len

@[simp] theorem earlyExtraPC2934 : IPC 2664 = 3453 := by pc_by_len

@[simp] theorem earlyExtraPC2935 : IPC 2665 = 3454 := by pc_by_len

@[simp] theorem earlyExtraPC2936 : IPC 2666 = 3457 := by pc_by_len

@[simp] theorem earlyExtraPC2937 : IPC 2667 = 3458 := by pc_by_len

@[simp] theorem earlyExtraPC2938 : IPC 2668 = 3460 := by pc_by_len

@[simp] theorem earlyExtraPC2939 : IPC 2669 = 3461 := by pc_by_len

@[simp] theorem earlyExtraPC2940 : IPC 2670 = 3462 := by pc_by_len

@[simp] theorem earlyExtraPC2941 : IPC 2671 = 3463 := by pc_by_len

@[simp] theorem earlyExtraPC2942 : IPC 2672 = 3464 := by pc_by_len

@[simp] theorem earlyExtraPC2943 : IPC 2673 = 3467 := by pc_by_len


@[simp] theorem pcC3009 : IPC 2366 = 3043 := by pc_by_len

@[simp] theorem pcC3010 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pcC3011 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pcC3019 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pcC3020 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pcC3021 : IPC 2367 = 3051 := by pc_by_len



/-! Program counters of the retained-T blocks the head-start table did not carry (generated from the artifact). -/

@[simp] theorem pcT2106 : IPC 1882 = 2379 := by pc_by_len

@[simp] theorem pcT2329 : IPC 2312 = 2977 := by pc_by_len

@[simp] theorem pcT2330 : IPC 2313 = 2978 := by pc_by_len

@[simp] theorem pcT2331 : IPC 2314 = 2979 := by pc_by_len

@[simp] theorem pcT2332 : IPC 2315 = 2980 := by pc_by_len

@[simp] theorem pcT2336 : IPC 2319 = 2986 := by pc_by_len

@[simp] theorem pcT2337 : IPC 2320 = 2987 := by pc_by_len

@[simp] theorem pcT2338 : IPC 2321 = 2988 := by pc_by_len

@[simp] theorem pcT2339 : IPC 2322 = 2989 := by pc_by_len

@[simp] theorem pcT2340 : IPC 2323 = 2992 := by pc_by_len

@[simp] theorem pcT2341 : IPC 2324 = 2993 := by pc_by_len

@[simp] theorem pcT2342 : IPC 2325 = 2994 := by pc_by_len

@[simp] theorem pcT2343 : IPC 2326 = 2995 := by pc_by_len

@[simp] theorem pcT2344 : IPC 2327 = 2996 := by pc_by_len

@[simp] theorem pcT2345 : IPC 2328 = 2997 := by pc_by_len

@[simp] theorem pcT2346 : IPC 2329 = 2998 := by pc_by_len

@[simp] theorem pcT2347 : IPC 2330 = 2999 := by pc_by_len

@[simp] theorem pcT2348 : IPC 2331 = 3000 := by pc_by_len

@[simp] theorem pcT2349 : IPC 2332 = 3003 := by pc_by_len

@[simp] theorem pcT2350 : IPC 2333 = 3004 := by pc_by_len

@[simp] theorem pcT2351 : IPC 2334 = 3005 := by pc_by_len

@[simp] theorem pcT2352 : IPC 2335 = 3006 := by pc_by_len

@[simp] theorem pcT2353 : IPC 2336 = 3007 := by pc_by_len

@[simp] theorem pcT2354 : IPC 2337 = 3008 := by pc_by_len

@[simp] theorem pcT2355 : IPC 2338 = 3009 := by pc_by_len

@[simp] theorem pcT2356 : IPC 2339 = 3010 := by pc_by_len

@[simp] theorem pcT2357 : IPC 2340 = 3011 := by pc_by_len

@[simp] theorem pcT2358 : IPC 2341 = 3012 := by pc_by_len

@[simp] theorem pcT2359 : IPC 2342 = 3013 := by pc_by_len

@[simp] theorem pcT2360 : IPC 2343 = 3014 := by pc_by_len

@[simp] theorem pcT2361 : IPC 2344 = 3015 := by pc_by_len

@[simp] theorem pcT2362 : IPC 2345 = 3016 := by pc_by_len

@[simp] theorem pcT2363 : IPC 2346 = 3017 := by pc_by_len

@[simp] theorem pcT2364 : IPC 2347 = 3018 := by pc_by_len

@[simp] theorem pcT2365 : IPC 2348 = 3021 := by pc_by_len

@[simp] theorem pcT2366 : IPC 2349 = 3022 := by pc_by_len

@[simp] theorem pcT2367 : IPC 2350 = 3023 := by pc_by_len

@[simp] theorem pcT2368 : IPC 2351 = 3024 := by pc_by_len

@[simp] theorem pcT2369 : IPC 2352 = 3025 := by pc_by_len

@[simp] theorem pcT2370 : IPC 2353 = 3028 := by pc_by_len

@[simp] theorem pcT2371 : IPC 2354 = 3029 := by pc_by_len

@[simp] theorem pcT2372 : IPC 2355 = 3030 := by pc_by_len

@[simp] theorem pcT2522 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pcI2013 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2014 : IPC 1814 = 2285 := by pc_by_len

@[simp] theorem pcI2015 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2016 : IPC 1816 = 2288 := by pc_by_len

@[simp] theorem pcI2017 : IPC 1817 = 2289 := by pc_by_len

@[simp] theorem pcI2018 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2032 : IPC 1822 = 2298 := by pc_by_len

@[simp] theorem pcI2033 : IPC 1824 = 2300 := by pc_by_len

@[simp] theorem pcI2034 : IPC 1825 = 2301 := by pc_by_len

@[simp] theorem pcI2035 : IPC 1826 = 2304 := by pc_by_len

@[simp] theorem pcI2036 : IPC 1838 = 2318 := by pc_by_len

@[simp] theorem pcI2037 : IPC 1839 = 2319 := by pc_by_len

@[simp] theorem pcI2038 : IPC 1841 = 2322 := by pc_by_len

@[simp] theorem pcI2039 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2040 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2041 : IPC 1842 = 2326 := by pc_by_len

@[simp] theorem pcI2042 : IPC 1843 = 2327 := by pc_by_len

@[simp] theorem pcI2043 : IPC 1847 = 2333 := by pc_by_len

@[simp] theorem pcI2044 : IPC 1849 = 2335 := by pc_by_len

@[simp] theorem pcI2045 : IPC 1850 = 2338 := by pc_by_len

@[simp] theorem pcI2046 : IPC 1851 = 2339 := by pc_by_len

@[simp] theorem pcI2047 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2048 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2049 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2050 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2051 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2052 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2053 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2054 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2055 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2056 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2057 : IPC 1853 = 2342 := by pc_by_len

@[simp] theorem pcI2093 : IPC 1883 = 2380 := by pc_by_len

@[simp] theorem pcI2094 : IPC 1884 = 2383 := by pc_by_len

@[simp] theorem pcI2095 : IPC 1885 = 2386 := by pc_by_len

@[simp] theorem pcI2156 : IPC 1964 = 2503 := by pc_by_len

@[simp] theorem pcI2200 : IPC 2019 = 2570 := by pc_by_len

@[simp] theorem pcI2201 : IPC 2022 = 2579 := by pc_by_len

@[simp] theorem pcI2202 : IPC 2034 = 2598 := by pc_by_len

@[simp] theorem pcI2203 : IPC 2034 = 2598 := by pc_by_len

@[simp] theorem pcI2204 : IPC 2035 = 2599 := by pc_by_len

@[simp] theorem pcI2205 : IPC 2037 = 2601 := by pc_by_len

@[simp] theorem pcI2206 : IPC 2040 = 2604 := by pc_by_len

@[simp] theorem pcI2207 : IPC 2041 = 2607 := by pc_by_len

@[simp] theorem pcI2208 : IPC 2042 = 2608 := by pc_by_len

@[simp] theorem pcI2209 : IPC 2043 = 2611 := by pc_by_len

@[simp] theorem pcI2210 : IPC 2044 = 2612 := by pc_by_len

@[simp] theorem pcI2211 : IPC 2045 = 2615 := by pc_by_len

@[simp] theorem pcI2212 : IPC 2046 = 2616 := by pc_by_len

@[simp] theorem pcI2213 : IPC 2047 = 2619 := by pc_by_len

@[simp] theorem pcI2214 : IPC 2048 = 2620 := by pc_by_len

@[simp] theorem pcI2215 : IPC 2049 = 2623 := by pc_by_len

@[simp] theorem pcI2216 : IPC 2050 = 2624 := by pc_by_len

@[simp] theorem pcI2217 : IPC 2051 = 2627 := by pc_by_len

@[simp] theorem pcI2218 : IPC 2052 = 2628 := by pc_by_len

@[simp] theorem pcI2219 : IPC 2053 = 2631 := by pc_by_len

@[simp] theorem pcI2220 : IPC 2054 = 2632 := by pc_by_len

@[simp] theorem pcI2221 : IPC 2055 = 2635 := by pc_by_len

@[simp] theorem pcI2222 : IPC 2056 = 2636 := by pc_by_len

@[simp] theorem pcI2223 : IPC 2057 = 2639 := by pc_by_len

@[simp] theorem pcI2224 : IPC 2058 = 2640 := by pc_by_len

@[simp] theorem pcI2225 : IPC 2059 = 2643 := by pc_by_len

@[simp] theorem pcI2226 : IPC 2060 = 2644 := by pc_by_len

@[simp] theorem pcI2330 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2332 : IPC 2147 = 2790 := by pc_by_len

@[simp] theorem pcI2333 : IPC 2148 = 2791 := by pc_by_len

@[simp] theorem pcI2334 : IPC 2149 = 2792 := by pc_by_len

@[simp] theorem pcI2335 : IPC 2150 = 2793 := by pc_by_len

@[simp] theorem pcI2336 : IPC 2151 = 2794 := by pc_by_len

@[simp] theorem pcI2337 : IPC 2152 = 2795 := by pc_by_len

@[simp] theorem pcI2338 : IPC 2153 = 2796 := by pc_by_len

@[simp] theorem pcI2339 : IPC 2154 = 2797 := by pc_by_len

@[simp] theorem pcI2340 : IPC 2155 = 2798 := by pc_by_len

@[simp] theorem pcI2341 : IPC 2156 = 2801 := by pc_by_len

@[simp] theorem pcI2342 : IPC 2157 = 2802 := by pc_by_len

@[simp] theorem pcI2343 : IPC 2158 = 2803 := by pc_by_len

@[simp] theorem pcI2344 : IPC 2159 = 2804 := by pc_by_len

@[simp] theorem pcI2345 : IPC 2160 = 2805 := by pc_by_len

@[simp] theorem pcI2346 : IPC 2161 = 2806 := by pc_by_len

@[simp] theorem pcI2347 : IPC 2162 = 2807 := by pc_by_len

@[simp] theorem pcI2348 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2349 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2350 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2351 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2352 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2353 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2354 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2355 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2356 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2357 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2358 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2359 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2360 : IPC 2163 = 2808 := by pc_by_len

@[simp] theorem pcI2361 : IPC 2164 = 2809 := by pc_by_len

@[simp] theorem pcI2362 : IPC 2165 = 2810 := by pc_by_len

@[simp] theorem pcI2363 : IPC 2166 = 2811 := by pc_by_len

@[simp] theorem pcI2364 : IPC 2167 = 2812 := by pc_by_len

@[simp] theorem pcI2365 : IPC 2168 = 2813 := by pc_by_len

@[simp] theorem pcI2366 : IPC 2169 = 2814 := by pc_by_len

@[simp] theorem pcI2367 : IPC 2170 = 2815 := by pc_by_len

@[simp] theorem pcI2368 : IPC 2171 = 2816 := by pc_by_len

@[simp] theorem pcI2369 : IPC 2172 = 2817 := by pc_by_len

@[simp] theorem pcI2370 : IPC 2173 = 2818 := by pc_by_len

@[simp] theorem pcI2371 : IPC 2174 = 2819 := by pc_by_len

@[simp] theorem pcI2372 : IPC 2175 = 2820 := by pc_by_len

@[simp] theorem pcI2373 : IPC 2176 = 2821 := by pc_by_len

@[simp] theorem pcI2374 : IPC 2177 = 2822 := by pc_by_len

@[simp] theorem pcI2375 : IPC 2178 = 2825 := by pc_by_len

@[simp] theorem pcI2376 : IPC 2179 = 2826 := by pc_by_len

@[simp] theorem pcI2377 : IPC 2180 = 2827 := by pc_by_len

@[simp] theorem pcI2378 : IPC 2181 = 2828 := by pc_by_len

@[simp] theorem pcI2379 : IPC 2182 = 2829 := by pc_by_len

@[simp] theorem pcI2380 : IPC 2183 = 2832 := by pc_by_len

@[simp] theorem pcI2381 : IPC 2184 = 2833 := by pc_by_len

@[simp] theorem pcI2382 : IPC 2185 = 2834 := by pc_by_len

@[simp] theorem pcI2383 : IPC 2186 = 2835 := by pc_by_len

@[simp] theorem pcI2384 : IPC 2187 = 2836 := by pc_by_len

@[simp] theorem pcI2385 : IPC 2188 = 2837 := by pc_by_len

@[simp] theorem pcI2386 : IPC 2189 = 2838 := by pc_by_len

@[simp] theorem pcI2387 : IPC 2190 = 2839 := by pc_by_len

@[simp] theorem pcI2388 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2389 : IPC 2191 = 2840 := by pc_by_len

@[simp] theorem pcI2390 : IPC 2192 = 2841 := by pc_by_len

@[simp] theorem pcI2391 : IPC 2193 = 2842 := by pc_by_len

@[simp] theorem pcI2392 : IPC 2194 = 2843 := by pc_by_len

@[simp] theorem pcI2393 : IPC 2195 = 2844 := by pc_by_len

@[simp] theorem pcI2394 : IPC 2196 = 2845 := by pc_by_len

@[simp] theorem pcI2395 : IPC 2197 = 2846 := by pc_by_len

@[simp] theorem pcI2396 : IPC 2198 = 2847 := by pc_by_len

@[simp] theorem pcI2397 : IPC 2199 = 2848 := by pc_by_len

@[simp] theorem pcI2398 : IPC 2200 = 2849 := by pc_by_len

@[simp] theorem pcI2399 : IPC 2201 = 2850 := by pc_by_len

@[simp] theorem pcI2400 : IPC 2202 = 2851 := by pc_by_len

@[simp] theorem pcI2401 : IPC 2203 = 2852 := by pc_by_len

@[simp] theorem pcI2402 : IPC 2204 = 2853 := by pc_by_len

@[simp] theorem pcI2403 : IPC 2205 = 2854 := by pc_by_len

@[simp] theorem pcI2404 : IPC 2206 = 2857 := by pc_by_len

@[simp] theorem pcI2405 : IPC 2207 = 2858 := by pc_by_len

@[simp] theorem pcI2406 : IPC 2208 = 2859 := by pc_by_len

@[simp] theorem pcI2407 : IPC 2209 = 2860 := by pc_by_len

@[simp] theorem pcI2408 : IPC 2210 = 2861 := by pc_by_len

@[simp] theorem pcI2409 : IPC 2211 = 2864 := by pc_by_len

@[simp] theorem pcI2410 : IPC 2212 = 2865 := by pc_by_len

@[simp] theorem pcI2411 : IPC 2213 = 2866 := by pc_by_len

@[simp] theorem pcI2412 : IPC 2214 = 2867 := by pc_by_len

@[simp] theorem pcI2413 : IPC 2215 = 2868 := by pc_by_len

@[simp] theorem pcI2414 : IPC 2216 = 2869 := by pc_by_len

@[simp] theorem pcI2415 : IPC 2217 = 2870 := by pc_by_len

@[simp] theorem pcI2416 : IPC 2218 = 2871 := by pc_by_len

@[simp] theorem pcI2417 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2418 : IPC 2219 = 2872 := by pc_by_len

@[simp] theorem pcI2419 : IPC 2220 = 2873 := by pc_by_len

@[simp] theorem pcI2420 : IPC 2221 = 2874 := by pc_by_len

@[simp] theorem pcI2421 : IPC 2222 = 2875 := by pc_by_len

@[simp] theorem pcI2422 : IPC 2223 = 2876 := by pc_by_len

@[simp] theorem pcI2423 : IPC 2224 = 2877 := by pc_by_len

@[simp] theorem pcI2424 : IPC 2225 = 2878 := by pc_by_len

@[simp] theorem pcI2425 : IPC 2226 = 2879 := by pc_by_len

@[simp] theorem pcI2426 : IPC 2227 = 2880 := by pc_by_len

@[simp] theorem pcI2432 : IPC 2233 = 2886 := by pc_by_len

@[simp] theorem pcI2433 : IPC 2234 = 2889 := by pc_by_len

@[simp] theorem pcI2434 : IPC 2235 = 2890 := by pc_by_len

@[simp] theorem pcI2435 : IPC 2236 = 2891 := by pc_by_len

@[simp] theorem pcI2436 : IPC 2237 = 2892 := by pc_by_len

@[simp] theorem pcI2437 : IPC 2238 = 2893 := by pc_by_len

@[simp] theorem pcI2438 : IPC 2239 = 2896 := by pc_by_len

@[simp] theorem pcI2439 : IPC 2240 = 2897 := by pc_by_len

@[simp] theorem pcI2440 : IPC 2241 = 2898 := by pc_by_len

@[simp] theorem pcI2441 : IPC 2242 = 2899 := by pc_by_len

@[simp] theorem pcI2442 : IPC 2243 = 2900 := by pc_by_len

@[simp] theorem pcI2443 : IPC 2244 = 2901 := by pc_by_len

@[simp] theorem pcI2444 : IPC 2245 = 2902 := by pc_by_len

@[simp] theorem pcI2445 : IPC 2246 = 2903 := by pc_by_len

@[simp] theorem pcI2446 : IPC 2247 = 2904 := by pc_by_len

@[simp] theorem pcI2447 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2448 : IPC 2248 = 2905 := by pc_by_len

@[simp] theorem pcI2449 : IPC 2249 = 2906 := by pc_by_len

@[simp] theorem pcI2450 : IPC 2250 = 2907 := by pc_by_len

@[simp] theorem pcI2451 : IPC 2251 = 2908 := by pc_by_len

@[simp] theorem pcI2452 : IPC 2252 = 2909 := by pc_by_len

@[simp] theorem pcI2453 : IPC 2253 = 2910 := by pc_by_len

@[simp] theorem pcI2454 : IPC 2254 = 2911 := by pc_by_len

@[simp] theorem pcI2455 : IPC 2255 = 2912 := by pc_by_len

@[simp] theorem pcI2456 : IPC 2256 = 2913 := by pc_by_len

@[simp] theorem pcI2457 : IPC 2257 = 2914 := by pc_by_len

@[simp] theorem pcI2458 : IPC 2258 = 2915 := by pc_by_len

@[simp] theorem pcI2459 : IPC 2259 = 2916 := by pc_by_len

@[simp] theorem pcI2460 : IPC 2260 = 2917 := by pc_by_len

@[simp] theorem pcI2461 : IPC 2261 = 2918 := by pc_by_len

@[simp] theorem pcI2462 : IPC 2262 = 2921 := by pc_by_len

@[simp] theorem pcI2463 : IPC 2263 = 2922 := by pc_by_len

@[simp] theorem pcI2464 : IPC 2264 = 2923 := by pc_by_len

@[simp] theorem pcI2465 : IPC 2265 = 2924 := by pc_by_len

@[simp] theorem pcI2466 : IPC 2266 = 2925 := by pc_by_len

@[simp] theorem pcI2467 : IPC 2267 = 2928 := by pc_by_len

@[simp] theorem pcI2468 : IPC 2268 = 2929 := by pc_by_len

@[simp] theorem pcI2469 : IPC 2269 = 2930 := by pc_by_len

@[simp] theorem pcI2470 : IPC 2270 = 2931 := by pc_by_len

@[simp] theorem pcI2471 : IPC 2271 = 2932 := by pc_by_len

@[simp] theorem pcI2472 : IPC 2272 = 2933 := by pc_by_len

@[simp] theorem pcI2473 : IPC 2273 = 2934 := by pc_by_len

@[simp] theorem pcI2474 : IPC 2274 = 2935 := by pc_by_len

@[simp] theorem pcI2475 : IPC 2275 = 2936 := by pc_by_len

@[simp] theorem pcI2476 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2477 : IPC 2276 = 2937 := by pc_by_len

@[simp] theorem pcI2478 : IPC 2277 = 2938 := by pc_by_len

@[simp] theorem pcI2479 : IPC 2278 = 2939 := by pc_by_len

@[simp] theorem pcI2480 : IPC 2279 = 2940 := by pc_by_len

@[simp] theorem pcI2481 : IPC 2280 = 2941 := by pc_by_len

@[simp] theorem pcI2482 : IPC 2281 = 2942 := by pc_by_len

@[simp] theorem pcI2483 : IPC 2282 = 2943 := by pc_by_len

@[simp] theorem pcI2484 : IPC 2283 = 2944 := by pc_by_len

@[simp] theorem pcI2485 : IPC 2284 = 2945 := by pc_by_len

@[simp] theorem pcI2486 : IPC 2285 = 2946 := by pc_by_len

@[simp] theorem pcI2487 : IPC 2286 = 2947 := by pc_by_len

@[simp] theorem pcI2488 : IPC 2287 = 2948 := by pc_by_len

@[simp] theorem pcI2489 : IPC 2288 = 2949 := by pc_by_len

@[simp] theorem pcI2490 : IPC 2289 = 2950 := by pc_by_len

@[simp] theorem pcI2492 : IPC 2290 = 2953 := by pc_by_len

@[simp] theorem pcI2493 : IPC 2291 = 2954 := by pc_by_len

@[simp] theorem pcI2494 : IPC 2292 = 2955 := by pc_by_len

@[simp] theorem pcI2495 : IPC 2293 = 2956 := by pc_by_len

@[simp] theorem pcI2496 : IPC 2294 = 2957 := by pc_by_len

@[simp] theorem pcI2497 : IPC 2295 = 2960 := by pc_by_len

@[simp] theorem pcI2498 : IPC 2296 = 2961 := by pc_by_len

@[simp] theorem pcI2499 : IPC 2297 = 2962 := by pc_by_len

@[simp] theorem pcI2500 : IPC 2298 = 2963 := by pc_by_len

@[simp] theorem pcI2501 : IPC 2299 = 2964 := by pc_by_len

@[simp] theorem pcI2502 : IPC 2300 = 2965 := by pc_by_len

@[simp] theorem pcI2503 : IPC 2301 = 2966 := by pc_by_len

@[simp] theorem pcI2504 : IPC 2302 = 2967 := by pc_by_len

@[simp] theorem pcI2505 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2506 : IPC 2303 = 2968 := by pc_by_len

@[simp] theorem pcI2507 : IPC 2304 = 2969 := by pc_by_len

@[simp] theorem pcI2508 : IPC 2305 = 2970 := by pc_by_len

@[simp] theorem pcI2509 : IPC 2306 = 2971 := by pc_by_len

@[simp] theorem pcI2510 : IPC 2307 = 2972 := by pc_by_len

@[simp] theorem pcI2511 : IPC 2308 = 2973 := by pc_by_len

@[simp] theorem pcI2514 : IPC 2311 = 2976 := by pc_by_len

@[simp] theorem pcI2519 : IPC 2316 = 2981 := by pc_by_len

@[simp] theorem pcI2520 : IPC 2317 = 2982 := by pc_by_len

@[simp] theorem pcI2521 : IPC 2318 = 2985 := by pc_by_len

@[simp] theorem pcI2559 : IPC 2356 = 3031 := by pc_by_len

@[simp] theorem pcI2560 : IPC 2357 = 3032 := by pc_by_len

@[simp] theorem pcI2561 : IPC 2358 = 3033 := by pc_by_len

@[simp] theorem pcI2562 : IPC 2359 = 3034 := by pc_by_len

@[simp] theorem pcI2563 : IPC 2360 = 3035 := by pc_by_len

@[simp] theorem pcI2564 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2565 : IPC 2361 = 3036 := by pc_by_len

@[simp] theorem pcI2566 : IPC 2362 = 3039 := by pc_by_len

@[simp] theorem pcI2585 : IPC 2367 = 3051 := by pc_by_len

/-! ## The straight-line negation and the inline Newton chain (negun, inl693) -/

@[simp] theorem negunPC0 (i : Nat) (hi : 1813 ≤ i) (hii : i ≤ 1821) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2284, 2285, 2287, 2288, 2289, 2290, 2293, 2294, 2297] : List Nat)[i - 1813]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem negunPC1 (i : Nat) (hi : 1886 ≤ i) (hii : i ≤ 1932) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2387, 2388, 2390, 2391, 2394, 2395, 2397, 2398, 2399, 2400, 2403, 2404, 2406, 2407, 2408, 2411, 2412, 2414, 2415, 2416, 2419, 2420, 2422, 2423, 2424, 2427, 2428, 2430, 2431, 2432, 2435, 2436, 2437, 2439, 2440, 2441, 2444, 2445, 2447, 2448, 2449, 2452, 2453, 2454, 2455, 2456, 2457] : List Nat)[i - 1886]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem negunPC2 (i : Nat) (hi : 1965 ≤ i) (hii : i ≤ 2008) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2504, 2505, 2506, 2507, 2508, 2510, 2511, 2513, 2514, 2515, 2516, 2517, 2519, 2520, 2521, 2522, 2523, 2524, 2526, 2527, 2528, 2529, 2530, 2531, 2533, 2534, 2535, 2536, 2537, 2538, 2540, 2541, 2542, 2543, 2544, 2545, 2547, 2548, 2549, 2550, 2551, 2552, 2554, 2555] : List Nat)[i - 1965]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-! ## Directly stated pcs: E5 and the eight-limb loop head (2056 .. 2146), the bottom test,
the exit / E3 phase blocks and the repair loop (2381 .. 2465), and the appended four-limb
loop head (8548 .. 8610). -/

@[simp] theorem pcDual2056 : IPC 2061 = 2647 := by pc_by_len

@[simp] theorem pcDual2057 : IPC 2035 = 2599 := by pc_by_len

@[simp] theorem pcDual2065 : IPC 2035 = 2599 := by pc_by_len

@[simp] theorem pcDual2066 : IPC 2035 = 2599 := by pc_by_len

@[simp] theorem pcDual2067 : IPC 2035 = 2599 := by pc_by_len

@[simp] theorem pcDual2068 : IPC 2061 = 2647 := by pc_by_len

@[simp] theorem pcDual2069 : IPC 2022 = 2579 := by pc_by_len

@[simp] theorem pcDual2070 : IPC 2027 = 2588 := by pc_by_len

@[simp] theorem pcDual2071 : IPC 2027 = 2588 := by pc_by_len

@[simp] theorem pcDual2072 : IPC 2029 = 2590 := by pc_by_len

@[simp] theorem pcDual2073 : IPC 2030 = 2591 := by pc_by_len

@[simp] theorem pcDual2074 : IPC 2031 = 2592 := by pc_by_len

@[simp] theorem pcDual2075 : IPC 2032 = 2594 := by pc_by_len

@[simp] theorem pcDual2076 : IPC 2032 = 2594 := by pc_by_len

@[simp] theorem pcDual2077 : IPC 2033 = 2595 := by pc_by_len

@[simp] theorem pcDual2078 : IPC 2034 = 2598 := by pc_by_len

@[simp] theorem pcDual2079 : IPC 2061 = 2647 := by pc_by_len

@[simp] theorem pcDual2080 : IPC 2061 = 2647 := by pc_by_len

@[simp] theorem pcDual2081 : IPC 2066 = 2654 := by pc_by_len

@[simp] theorem pcDual2082 : IPC 2067 = 2655 := by pc_by_len

@[simp] theorem pcDual2083 : IPC 2068 = 2656 := by pc_by_len

@[simp] theorem pcDual2084 : IPC 2069 = 2657 := by pc_by_len

@[simp] theorem pcDual2085 : IPC 2072 = 2661 := by pc_by_len

@[simp] theorem pcDual2086 : IPC 2072 = 2661 := by pc_by_len

@[simp] theorem pcDual2087 : IPC 2076 = 2667 := by pc_by_len

@[simp] theorem pcDual2088 : IPC 2094 = 2692 := by pc_by_len

@[simp] theorem pcDual2089 : IPC 2094 = 2692 := by pc_by_len

@[simp] theorem pcDual2090 : IPC 2094 = 2692 := by pc_by_len

@[simp] theorem pcDual2091 : IPC 2094 = 2692 := by pc_by_len

@[simp] theorem pcDual2092 : IPC 2095 = 2693 := by pc_by_len

@[simp] theorem pcDual2093 : IPC 2096 = 2694 := by pc_by_len

@[simp] theorem pcDual2094 : IPC 2097 = 2697 := by pc_by_len

@[simp] theorem pcDual2095 : IPC 2098 = 2700 := by pc_by_len

@[simp] theorem pcDual2096 : IPC 2099 = 2701 := by pc_by_len

@[simp] theorem pcDual2100 : IPC 2100 = 2704 := by pc_by_len

@[simp] theorem pcDual2101 : IPC 2101 = 2705 := by pc_by_len

@[simp] theorem pcDual2102 : IPC 2102 = 2706 := by pc_by_len

@[simp] theorem pcDual2103 : IPC 2103 = 2707 := by pc_by_len

@[simp] theorem pcDual2104 : IPC 2104 = 2708 := by pc_by_len

@[simp] theorem pcDual2105 : IPC 2105 = 2709 := by pc_by_len

@[simp] theorem pcDual2106 : IPC 2106 = 2712 := by pc_by_len

@[simp] theorem pcDual2107 : IPC 2107 = 2713 := by pc_by_len

@[simp] theorem pcDual2108 : IPC 2108 = 2714 := by pc_by_len

@[simp] theorem pcDual2109 : IPC 2109 = 2717 := by pc_by_len

@[simp] theorem pcDual2110 : IPC 2110 = 2718 := by pc_by_len

@[simp] theorem pcDual2111 : IPC 2111 = 2719 := by pc_by_len

@[simp] theorem pcDual2112 : IPC 2112 = 2720 := by pc_by_len

@[simp] theorem pcDual2113 : IPC 2114 = 2722 := by pc_by_len

@[simp] theorem pcDual2114 : IPC 2115 = 2723 := by pc_by_len

@[simp] theorem pcDual2115 : IPC 2116 = 2724 := by pc_by_len

@[simp] theorem pcDual2116 : IPC 2117 = 2725 := by pc_by_len

@[simp] theorem pcDual2117 : IPC 2118 = 2726 := by pc_by_len

@[simp] theorem pcDual2118 : IPC 2119 = 2727 := by pc_by_len

@[simp] theorem pcDual2119 : IPC 2120 = 2728 := by pc_by_len

@[simp] theorem pcDual2120 : IPC 2121 = 2729 := by pc_by_len

@[simp] theorem pcDual2121 : IPC 2122 = 2730 := by pc_by_len

@[simp] theorem pcDual2122 : IPC 2123 = 2731 := by pc_by_len

@[simp] theorem pcDual2123 : IPC 2124 = 2732 := by pc_by_len

@[simp] theorem pcDual2124 : IPC 2125 = 2733 := by pc_by_len

@[simp] theorem pcDual2125 : IPC 2126 = 2734 := by pc_by_len

@[simp] theorem pcDual2126 : IPC 2127 = 2735 := by pc_by_len

@[simp] theorem pcDual2127 : IPC 2128 = 2737 := by pc_by_len

@[simp] theorem pcDual2128 : IPC 2129 = 2738 := by pc_by_len

@[simp] theorem pcDual2129 : IPC 2130 = 2739 := by pc_by_len

@[simp] theorem pcDual2130 : IPC 2131 = 2740 := by pc_by_len

@[simp] theorem pcDual2131 : IPC 2132 = 2741 := by pc_by_len

@[simp] theorem pcDual2132 : IPC 2133 = 2742 := by pc_by_len

@[simp] theorem pcDual2133 : IPC 2134 = 2743 := by pc_by_len

@[simp] theorem pcDual2134 : IPC 2135 = 2746 := by pc_by_len

@[simp] theorem pcDual2135 : IPC 2136 = 2747 := by pc_by_len

@[simp] theorem pcDual2136 : IPC 2137 = 2748 := by pc_by_len

@[simp] theorem pcDual2137 : IPC 2138 = 2749 := by pc_by_len

@[simp] theorem pcDual2138 : IPC 2139 = 2750 := by pc_by_len

@[simp] theorem pcDual2139 : IPC 2140 = 2751 := by pc_by_len

@[simp] theorem pcDual2141 : IPC 2141 = 2784 := by pc_by_len

@[simp] theorem pcDual2142 : IPC 2142 = 2785 := by pc_by_len

@[simp] theorem pcDual2143 : IPC 2143 = 2786 := by pc_by_len

@[simp] theorem pcDual2144 : IPC 2144 = 2787 := by pc_by_len

@[simp] theorem pcDual2145 : IPC 2145 = 2788 := by pc_by_len

@[simp] theorem pcDual2146 : IPC 2146 = 2789 := by pc_by_len

@[simp] theorem pcDual2381 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pcDual2382 : IPC 2367 = 3051 := by pc_by_len

@[simp] theorem pcDual2383 : IPC 2370 = 3054 := by pc_by_len

@[simp] theorem pcDual2384 : IPC 2372 = 3056 := by pc_by_len

@[simp] theorem pcDual2385 : IPC 2373 = 3057 := by pc_by_len

@[simp] theorem pcDual2386 : IPC 2374 = 3058 := by pc_by_len

@[simp] theorem pcDual2387 : IPC 2375 = 3059 := by pc_by_len

@[simp] theorem pcDual2388 : IPC 2377 = 3061 := by pc_by_len

@[simp] theorem pcDual2389 : IPC 2377 = 3061 := by pc_by_len

@[simp] theorem pcDual2390 : IPC 2378 = 3062 := by pc_by_len

@[simp] theorem pcDual2391 : IPC 2379 = 3063 := by pc_by_len

@[simp] theorem pcDual2392 : IPC 2379 = 3063 := by pc_by_len

@[simp] theorem pcDual2393 : IPC 2379 = 3063 := by pc_by_len

@[simp] theorem pcDual2394 : IPC 2379 = 3063 := by pc_by_len

@[simp] theorem pcDual2395 : IPC 2382 = 3067 := by pc_by_len

@[simp] theorem pcDual2396 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2397 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2398 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2399 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2400 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2401 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2402 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2403 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2404 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2405 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2406 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2407 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2408 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2409 : IPC 8396 = 10956 := by pc_by_len

@[simp] theorem pcDual2410 : IPC 2382 = 3067 := by pc_by_len

@[simp] theorem pcDual2411 : IPC 2385 = 3072 := by pc_by_len

@[simp] theorem pcDual2412 : IPC 2386 = 3073 := by pc_by_len

@[simp] theorem pcDual2413 : IPC 2387 = 3074 := by pc_by_len

@[simp] theorem pcDual2414 : IPC 2388 = 3075 := by pc_by_len

@[simp] theorem pcDual2415 : IPC 2389 = 3078 := by pc_by_len

@[simp] theorem pcDual2416 : IPC 2390 = 3079 := by pc_by_len

@[simp] theorem pcDual2417 : IPC 2391 = 3080 := by pc_by_len

@[simp] theorem pcDual2418 : IPC 2392 = 3081 := by pc_by_len

@[simp] theorem pcDual2419 : IPC 2393 = 3082 := by pc_by_len

@[simp] theorem pcDual2420 : IPC 2394 = 3085 := by pc_by_len

@[simp] theorem pcDual2421 : IPC 2395 = 3086 := by pc_by_len

@[simp] theorem pcDual2422 : IPC 2396 = 3087 := by pc_by_len

@[simp] theorem pcDual2423 : IPC 2397 = 3088 := by pc_by_len

@[simp] theorem pcDual2424 : IPC 2398 = 3089 := by pc_by_len

@[simp] theorem pcDual2425 : IPC 2399 = 3090 := by pc_by_len

@[simp] theorem pcDual2426 : IPC 2400 = 3091 := by pc_by_len

@[simp] theorem pcDual2427 : IPC 2401 = 3092 := by pc_by_len

@[simp] theorem pcDual2428 : IPC 2402 = 3093 := by pc_by_len

@[simp] theorem pcDual2429 : IPC 2403 = 3094 := by pc_by_len

@[simp] theorem pcDual2430 : IPC 2404 = 3095 := by pc_by_len

@[simp] theorem pcDual2431 : IPC 2405 = 3096 := by pc_by_len

@[simp] theorem pcDual2432 : IPC 2406 = 3097 := by pc_by_len

@[simp] theorem pcDual2433 : IPC 2407 = 3098 := by pc_by_len

@[simp] theorem pcDual2434 : IPC 2408 = 3099 := by pc_by_len

@[simp] theorem pcDual2435 : IPC 2409 = 3100 := by pc_by_len

@[simp] theorem pcDual2436 : IPC 2410 = 3101 := by pc_by_len

@[simp] theorem pcDual2437 : IPC 2411 = 3102 := by pc_by_len

@[simp] theorem pcDual2438 : IPC 2412 = 3103 := by pc_by_len

@[simp] theorem pcDual2439 : IPC 2413 = 3105 := by pc_by_len

@[simp] theorem pcDual2440 : IPC 2414 = 3106 := by pc_by_len

@[simp] theorem pcDual2441 : IPC 2415 = 3107 := by pc_by_len

@[simp] theorem pcDual2442 : IPC 2416 = 3110 := by pc_by_len

@[simp] theorem pcDual2443 : IPC 2417 = 3111 := by pc_by_len

@[simp] theorem pcDual2444 : IPC 2418 = 3112 := by pc_by_len

@[simp] theorem pcDual2445 : IPC 2419 = 3115 := by pc_by_len

@[simp] theorem pcDual2446 : IPC 2420 = 3116 := by pc_by_len

@[simp] theorem pcDual2447 : IPC 2421 = 3117 := by pc_by_len

@[simp] theorem pcDual2448 : IPC 2422 = 3120 := by pc_by_len

@[simp] theorem pcDual2449 : IPC 2423 = 3121 := by pc_by_len

@[simp] theorem pcDual2450 : IPC 2424 = 3122 := by pc_by_len

@[simp] theorem pcDual2451 : IPC 2425 = 3123 := by pc_by_len

@[simp] theorem pcDual2452 : IPC 2426 = 3124 := by pc_by_len

@[simp] theorem pcDual2453 : IPC 2427 = 3127 := by pc_by_len

@[simp] theorem pcDual2454 : IPC 2428 = 3128 := by pc_by_len

@[simp] theorem pcDual2455 : IPC 2429 = 3129 := by pc_by_len

@[simp] theorem pcDual2456 : IPC 2430 = 3130 := by pc_by_len

@[simp] theorem pcDual2457 : IPC 2431 = 3133 := by pc_by_len

@[simp] theorem pcDual2458 : IPC 2432 = 3134 := by pc_by_len

@[simp] theorem pcDual2459 : IPC 2433 = 3137 := by pc_by_len

@[simp] theorem pcDual2460 : IPC 2436 = 3140 := by pc_by_len

@[simp] theorem pcDual2461 : IPC 2437 = 3143 := by pc_by_len

@[simp] theorem pcDual2462 : IPC 2437 = 3143 := by pc_by_len

@[simp] theorem pcDual2463 : IPC 2437 = 3143 := by pc_by_len

@[simp] theorem pcDual2464 : IPC 2437 = 3143 := by pc_by_len

@[simp] theorem pcDual2465 : IPC 2439 = 3145 := by pc_by_len

@[simp] theorem pcDual8548 : IPC 8224 = 10692 := by pc_by_len

@[simp] theorem pcDual8549 : IPC 8224 = 10692 := by pc_by_len

@[simp] theorem pcDual8550 : IPC 8224 = 10692 := by pc_by_len

@[simp] theorem pcDual8551 : IPC 8225 = 10693 := by pc_by_len

@[simp] theorem pcDual8552 : IPC 8226 = 10694 := by pc_by_len

@[simp] theorem pcDual8553 : IPC 8227 = 10697 := by pc_by_len

@[simp] theorem pcDual8554 : IPC 8228 = 10700 := by pc_by_len

@[simp] theorem pcDual8555 : IPC 8229 = 10701 := by pc_by_len

@[simp] theorem pcDual8559 : IPC 8230 = 10704 := by pc_by_len

@[simp] theorem pcDual8560 : IPC 8231 = 10705 := by pc_by_len

@[simp] theorem pcDual8561 : IPC 8232 = 10706 := by pc_by_len

@[simp] theorem pcDual8562 : IPC 8233 = 10707 := by pc_by_len

@[simp] theorem pcDual8563 : IPC 8234 = 10708 := by pc_by_len

@[simp] theorem pcDual8564 : IPC 8235 = 10709 := by pc_by_len

@[simp] theorem pcDual8565 : IPC 8236 = 10712 := by pc_by_len

@[simp] theorem pcDual8566 : IPC 8237 = 10713 := by pc_by_len

@[simp] theorem pcDual8567 : IPC 8238 = 10714 := by pc_by_len

@[simp] theorem pcDual8568 : IPC 8239 = 10717 := by pc_by_len

@[simp] theorem pcDual8569 : IPC 8240 = 10718 := by pc_by_len

@[simp] theorem pcDual8570 : IPC 8241 = 10719 := by pc_by_len

@[simp] theorem pcDual8571 : IPC 8242 = 10720 := by pc_by_len

@[simp] theorem pcDual8572 : IPC 8244 = 10722 := by pc_by_len

@[simp] theorem pcDual8573 : IPC 8245 = 10723 := by pc_by_len

@[simp] theorem pcDual8574 : IPC 8246 = 10724 := by pc_by_len

@[simp] theorem pcDual8575 : IPC 8247 = 10725 := by pc_by_len

@[simp] theorem pcDual8576 : IPC 8248 = 10726 := by pc_by_len

@[simp] theorem pcDual8577 : IPC 8249 = 10727 := by pc_by_len

@[simp] theorem pcDual8578 : IPC 8250 = 10728 := by pc_by_len

@[simp] theorem pcDual8579 : IPC 8251 = 10729 := by pc_by_len

@[simp] theorem pcDual8580 : IPC 8252 = 10730 := by pc_by_len

@[simp] theorem pcDual8581 : IPC 8253 = 10731 := by pc_by_len

@[simp] theorem pcDual8582 : IPC 8254 = 10732 := by pc_by_len

@[simp] theorem pcDual8583 : IPC 8255 = 10733 := by pc_by_len

@[simp] theorem pcDual8584 : IPC 8256 = 10734 := by pc_by_len

@[simp] theorem pcDual8585 : IPC 8257 = 10735 := by pc_by_len

@[simp] theorem pcDual8586 : IPC 8258 = 10737 := by pc_by_len

@[simp] theorem pcDual8587 : IPC 8259 = 10738 := by pc_by_len

@[simp] theorem pcDual8588 : IPC 8260 = 10739 := by pc_by_len

@[simp] theorem pcDual8589 : IPC 8261 = 10740 := by pc_by_len

@[simp] theorem pcDual8590 : IPC 8262 = 10741 := by pc_by_len

@[simp] theorem pcDual8591 : IPC 8263 = 10742 := by pc_by_len

@[simp] theorem pcDual8592 : IPC 8264 = 10743 := by pc_by_len

@[simp] theorem pcDual8593 : IPC 8265 = 10746 := by pc_by_len

@[simp] theorem pcDual8594 : IPC 8266 = 10747 := by pc_by_len

@[simp] theorem pcDual8595 : IPC 8267 = 10748 := by pc_by_len

@[simp] theorem pcDual8596 : IPC 8268 = 10749 := by pc_by_len

@[simp] theorem pcDual8597 : IPC 8269 = 10750 := by pc_by_len

@[simp] theorem pcDual8598 : IPC 8270 = 10751 := by pc_by_len

@[simp] theorem pcDual8600 : IPC 8271 = 10784 := by pc_by_len

@[simp] theorem pcDual8601 : IPC 8272 = 10785 := by pc_by_len

@[simp] theorem pcDual8602 : IPC 8273 = 10786 := by pc_by_len

@[simp] theorem pcDual8603 : IPC 8274 = 10787 := by pc_by_len

@[simp] theorem pcDual8604 : IPC 8275 = 10788 := by pc_by_len

@[simp] theorem pcDual8605 : IPC 8276 = 10789 := by pc_by_len

@[simp] theorem pcDual8606 : IPC 8277 = 10790 := by pc_by_len

@[simp] theorem pcDual8607 : IPC 8278 = 10791 := by pc_by_len

@[simp] theorem pcDual8608 : IPC 8279 = 10792 := by pc_by_len

@[simp] theorem pcDual8609 : IPC 8280 = 10793 := by pc_by_len

@[simp] theorem pcDual8610 : IPC 8281 = 10794 := by pc_by_len

@[simp] theorem pcDual8611 : IPC 8282 = 10795 := by pc_by_len

@[simp] theorem pcDual8612 : IPC 8283 = 10796 := by pc_by_len

@[simp] theorem pcDual8613 : IPC 8284 = 10797 := by pc_by_len

@[simp] theorem pcDual8614 : IPC 8285 = 10798 := by pc_by_len

@[simp] theorem pcDual8615 : IPC 8286 = 10801 := by pc_by_len

@[simp] theorem pcDual8616 : IPC 8287 = 10802 := by pc_by_len

@[simp] theorem pcDual8617 : IPC 8288 = 10803 := by pc_by_len

@[simp] theorem pcDual8618 : IPC 8289 = 10804 := by pc_by_len

@[simp] theorem pcDual8619 : IPC 8290 = 10805 := by pc_by_len

@[simp] theorem pcDual8620 : IPC 8291 = 10806 := by pc_by_len

@[simp] theorem pcDual8621 : IPC 8292 = 10807 := by pc_by_len

@[simp] theorem pcDual8622 : IPC 8293 = 10808 := by pc_by_len

@[simp] theorem pcDual8623 : IPC 8294 = 10809 := by pc_by_len

@[simp] theorem pcDual8624 : IPC 8295 = 10810 := by pc_by_len

@[simp] theorem pcDual8625 : IPC 8296 = 10811 := by pc_by_len

@[simp] theorem pcDual8626 : IPC 8297 = 10812 := by pc_by_len

@[simp] theorem pcDual8627 : IPC 8298 = 10813 := by pc_by_len

@[simp] theorem pcDual8628 : IPC 8299 = 10814 := by pc_by_len

@[simp] theorem pcDual8629 : IPC 8300 = 10815 := by pc_by_len

@[simp] theorem pcDual8630 : IPC 8301 = 10816 := by pc_by_len

@[simp] theorem pcDual8631 : IPC 8302 = 10817 := by pc_by_len

@[simp] theorem pcDual8632 : IPC 8303 = 10818 := by pc_by_len

@[simp] theorem pcDual8633 : IPC 8304 = 10819 := by pc_by_len

@[simp] theorem pcDual8634 : IPC 8305 = 10820 := by pc_by_len

@[simp] theorem pcDual8635 : IPC 8306 = 10821 := by pc_by_len

@[simp] theorem pcDual8636 : IPC 8307 = 10822 := by pc_by_len

@[simp] theorem pcDual8637 : IPC 8308 = 10825 := by pc_by_len

@[simp] theorem pcDual8638 : IPC 8309 = 10826 := by pc_by_len

@[simp] theorem pcDual8639 : IPC 8310 = 10827 := by pc_by_len

@[simp] theorem pcDual8640 : IPC 8311 = 10828 := by pc_by_len

@[simp] theorem pcDual8641 : IPC 8312 = 10829 := by pc_by_len

@[simp] theorem pcDual8642 : IPC 8313 = 10832 := by pc_by_len

@[simp] theorem pcDual8643 : IPC 8314 = 10833 := by pc_by_len

@[simp] theorem pcDual8644 : IPC 8315 = 10834 := by pc_by_len

@[simp] theorem pcDual8645 : IPC 8316 = 10835 := by pc_by_len

@[simp] theorem pcDual8646 : IPC 8317 = 10836 := by pc_by_len

@[simp] theorem pcDual8647 : IPC 8318 = 10837 := by pc_by_len

@[simp] theorem pcDual8648 : IPC 8319 = 10838 := by pc_by_len

@[simp] theorem pcDual8649 : IPC 8320 = 10839 := by pc_by_len

@[simp] theorem pcDual8650 : IPC 8321 = 10840 := by pc_by_len

@[simp] theorem pcDual8651 : IPC 8322 = 10841 := by pc_by_len

@[simp] theorem pcDual8652 : IPC 8323 = 10842 := by pc_by_len

@[simp] theorem pcDual8653 : IPC 8324 = 10843 := by pc_by_len

@[simp] theorem pcDual8654 : IPC 8325 = 10844 := by pc_by_len

@[simp] theorem pcDual8655 : IPC 8326 = 10845 := by pc_by_len

@[simp] theorem pcDual8656 : IPC 8327 = 10846 := by pc_by_len

@[simp] theorem pcDual8657 : IPC 8328 = 10847 := by pc_by_len

@[simp] theorem pcDual8658 : IPC 8329 = 10848 := by pc_by_len

@[simp] theorem pcDual8659 : IPC 8330 = 10849 := by pc_by_len

@[simp] theorem pcDual8660 : IPC 8331 = 10850 := by pc_by_len

@[simp] theorem pcDual8661 : IPC 8332 = 10851 := by pc_by_len

@[simp] theorem pcDual8662 : IPC 8333 = 10852 := by pc_by_len

@[simp] theorem pcDual8663 : IPC 8334 = 10853 := by pc_by_len

@[simp] theorem pcDual8664 : IPC 8335 = 10854 := by pc_by_len

@[simp] theorem pcDual8665 : IPC 8336 = 10857 := by pc_by_len

@[simp] theorem pcDual8666 : IPC 8337 = 10858 := by pc_by_len

@[simp] theorem pcDual8667 : IPC 8338 = 10859 := by pc_by_len

@[simp] theorem pcDual8668 : IPC 8339 = 10860 := by pc_by_len

@[simp] theorem pcDual8669 : IPC 8340 = 10861 := by pc_by_len

@[simp] theorem pcDual8670 : IPC 8341 = 10864 := by pc_by_len

@[simp] theorem pcDual8671 : IPC 8342 = 10865 := by pc_by_len

@[simp] theorem pcDual8672 : IPC 8343 = 10866 := by pc_by_len

@[simp] theorem pcDual8673 : IPC 8344 = 10867 := by pc_by_len

@[simp] theorem pcDual8674 : IPC 8345 = 10868 := by pc_by_len

@[simp] theorem pcDual8675 : IPC 8346 = 10869 := by pc_by_len

@[simp] theorem pcDual8676 : IPC 8347 = 10870 := by pc_by_len

@[simp] theorem pcDual8677 : IPC 8348 = 10871 := by pc_by_len

@[simp] theorem pcDual8678 : IPC 8349 = 10872 := by pc_by_len

@[simp] theorem pcDual8679 : IPC 8350 = 10875 := by pc_by_len

@[simp] theorem pcDual8680 : IPC 8351 = 10876 := by pc_by_len

@[simp] theorem pcDual8681 : IPC 8352 = 10877 := by pc_by_len

@[simp] theorem pcDual8682 : IPC 8353 = 10878 := by pc_by_len

@[simp] theorem pcDual8683 : IPC 8354 = 10879 := by pc_by_len

@[simp] theorem pcDual8684 : IPC 8355 = 10880 := by pc_by_len

@[simp] theorem pcDual8685 : IPC 8356 = 10881 := by pc_by_len

@[simp] theorem pcDual8686 : IPC 8357 = 10882 := by pc_by_len

@[simp] theorem pcDual8687 : IPC 8358 = 10883 := by pc_by_len

@[simp] theorem pcDual8688 : IPC 8359 = 10884 := by pc_by_len

@[simp] theorem pcDual8689 : IPC 8360 = 10885 := by pc_by_len

@[simp] theorem pcDual8690 : IPC 8361 = 10886 := by pc_by_len

@[simp] theorem pcDual8691 : IPC 8362 = 10887 := by pc_by_len

@[simp] theorem pcDual8692 : IPC 8363 = 10888 := by pc_by_len

@[simp] theorem pcDual8693 : IPC 8364 = 10889 := by pc_by_len

@[simp] theorem pcDual8694 : IPC 8365 = 10890 := by pc_by_len

@[simp] theorem pcDual8695 : IPC 8366 = 10893 := by pc_by_len

@[simp] theorem pcDual8696 : IPC 8367 = 10894 := by pc_by_len

@[simp] theorem pcDual8697 : IPC 8368 = 10895 := by pc_by_len

@[simp] theorem pcDual8698 : IPC 8369 = 10896 := by pc_by_len

@[simp] theorem pcDual8699 : IPC 8370 = 10897 := by pc_by_len

@[simp] theorem pcDual8700 : IPC 8371 = 10900 := by pc_by_len

@[simp] theorem pcDual8701 : IPC 8372 = 10901 := by pc_by_len

@[simp] theorem pcDual8702 : IPC 8373 = 10902 := by pc_by_len

@[simp] theorem pcDual8703 : IPC 8374 = 10903 := by pc_by_len

@[simp] theorem pcDual8704 : IPC 8375 = 10904 := by pc_by_len

@[simp] theorem pcDual8705 : IPC 8376 = 10905 := by pc_by_len

@[simp] theorem pcDual8706 : IPC 8377 = 10906 := by pc_by_len

@[simp] theorem pcDual8707 : IPC 8378 = 10907 := by pc_by_len

@[simp] theorem pcDual8708 : IPC 8379 = 10908 := by pc_by_len

@[simp] theorem pcDual8709 : IPC 8380 = 10911 := by pc_by_len

@[simp] theorem pcDual8710 : IPC 8381 = 10912 := by pc_by_len

@[simp] theorem pcDual8711 : IPC 8382 = 10913 := by pc_by_len

@[simp] theorem pcDual8712 : IPC 8383 = 10914 := by pc_by_len

@[simp] theorem pcDual8713 : IPC 8384 = 10915 := by pc_by_len

@[simp] theorem pcDual8714 : IPC 8385 = 10945 := by pc_by_len

@[simp] theorem pcDual8715 : IPC 8385 = 10945 := by pc_by_len

@[simp] theorem pcDual8716 : IPC 8391 = 10951 := by pc_by_len

@[simp] theorem pcDual8717 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8718 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8719 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8720 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8721 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8722 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8723 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8724 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8725 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8726 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8727 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8728 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8729 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8730 : IPC 8389 = 10949 := by pc_by_len

@[simp] theorem pcDual8731 : IPC 8390 = 10950 := by pc_by_len

@[simp] theorem pcDual8732 : IPC 8391 = 10951 := by pc_by_len

@[simp] theorem pcDual8733 : IPC 8392 = 10952 := by pc_by_len

@[simp] theorem pcDual8734 : IPC 8393 = 10953 := by pc_by_len

@[simp] theorem pcDual8735 : IPC 8394 = 10954 := by pc_by_len

@[simp] theorem restoredGeneralPC2339 : CycleSubmission.Artifact.artifact.instructionPC 2361 = 3036 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2340 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3039 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2341 : CycleSubmission.Artifact.artifact.instructionPC 2363 = 3040 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2342 : CycleSubmission.Artifact.artifact.instructionPC 2364 = 3041 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2343 : CycleSubmission.Artifact.artifact.instructionPC 2365 = 3042 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2344 : CycleSubmission.Artifact.artifact.instructionPC 2366 = 3043 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2345 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3051 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2346 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3051 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2347 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3051 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2348 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3052 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2349 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3053 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2350 : CycleSubmission.Artifact.artifact.instructionPC 2370 = 3054 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2351 : CycleSubmission.Artifact.artifact.instructionPC 2371 = 3055 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2352 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3056 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2353 : CycleSubmission.Artifact.artifact.instructionPC 2373 = 3057 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2354 : CycleSubmission.Artifact.artifact.instructionPC 2374 = 3058 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2355 : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3059 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2356 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3060 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2412 : CycleSubmission.Artifact.artifact.instructionPC 2432 = 3134 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2413 : CycleSubmission.Artifact.artifact.instructionPC 2433 = 3137 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2414 : CycleSubmission.Artifact.artifact.instructionPC 2434 = 3138 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2415 : CycleSubmission.Artifact.artifact.instructionPC 2435 = 3139 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2416 : CycleSubmission.Artifact.artifact.instructionPC 2436 = 3140 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2417 : CycleSubmission.Artifact.artifact.instructionPC 2437 = 3143 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem lazyTopPC2339 : CycleSubmission.Artifact.artifact.instructionPC 2361 = 3036 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2340 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3039 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2341 : CycleSubmission.Artifact.artifact.instructionPC 2363 = 3040 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2342 : CycleSubmission.Artifact.artifact.instructionPC 2364 = 3041 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2343 : CycleSubmission.Artifact.artifact.instructionPC 2365 = 3042 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2344 : CycleSubmission.Artifact.artifact.instructionPC 2366 = 3043 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2345 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3051 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2346 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3052 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2347 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3053 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2348 : CycleSubmission.Artifact.artifact.instructionPC 2370 = 3054 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2349 : CycleSubmission.Artifact.artifact.instructionPC 2371 = 3055 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2350 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3056 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2351 : CycleSubmission.Artifact.artifact.instructionPC 2373 = 3057 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2352 : CycleSubmission.Artifact.artifact.instructionPC 2374 = 3058 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2353 : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3059 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2354 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3060 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2355 : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3061 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2451 : CycleSubmission.Artifact.artifact.instructionPC 2472 = 3231 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2452 : CycleSubmission.Artifact.artifact.instructionPC 2473 = 3232 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2453 : CycleSubmission.Artifact.artifact.instructionPC 2476 = 3235 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2454 : CycleSubmission.Artifact.artifact.instructionPC 2477 = 3236 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2455 : CycleSubmission.Artifact.artifact.instructionPC 2480 = 3239 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8399 : CycleSubmission.Artifact.artifact.instructionPC 8379 = 10908 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8400 : CycleSubmission.Artifact.artifact.instructionPC 8380 = 10911 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8401 : CycleSubmission.Artifact.artifact.instructionPC 8381 = 10912 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8402 : CycleSubmission.Artifact.artifact.instructionPC 8382 = 10913 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8403 : CycleSubmission.Artifact.artifact.instructionPC 8383 = 10914 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8404 : CycleSubmission.Artifact.artifact.instructionPC 8384 = 10915 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8405 : CycleSubmission.Artifact.artifact.instructionPC 8385 = 10945 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8406 : CycleSubmission.Artifact.artifact.instructionPC 8387 = 10947 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8407 : CycleSubmission.Artifact.artifact.instructionPC 8389 = 10949 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8408 : CycleSubmission.Artifact.artifact.instructionPC 8390 = 10950 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8409 : CycleSubmission.Artifact.artifact.instructionPC 8391 = 10951 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8410 : CycleSubmission.Artifact.artifact.instructionPC 8392 = 10952 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8411 : CycleSubmission.Artifact.artifact.instructionPC 8393 = 10953 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8412 : CycleSubmission.Artifact.artifact.instructionPC 8394 = 10954 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8413 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8414 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8415 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8416 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8417 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8418 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8419 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8420 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8421 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8422 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8423 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8424 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8425 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8426 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8427 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8428 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8429 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8430 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8431 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8432 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8433 : CycleSubmission.Artifact.artifact.instructionPC 8396 = 10956 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem inlineRepairPC2361 : CycleSubmission.Artifact.artifact.instructionPC 2382 = 3067 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2362 : CycleSubmission.Artifact.artifact.instructionPC 2383 = 3068 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2363 : CycleSubmission.Artifact.artifact.instructionPC 2384 = 3071 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2364 : CycleSubmission.Artifact.artifact.instructionPC 2385 = 3072 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2365 : CycleSubmission.Artifact.artifact.instructionPC 2386 = 3073 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2366 : CycleSubmission.Artifact.artifact.instructionPC 2387 = 3074 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2367 : CycleSubmission.Artifact.artifact.instructionPC 2388 = 3075 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2368 : CycleSubmission.Artifact.artifact.instructionPC 2389 = 3078 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2369 : CycleSubmission.Artifact.artifact.instructionPC 2390 = 3079 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2370 : CycleSubmission.Artifact.artifact.instructionPC 2391 = 3080 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2371 : CycleSubmission.Artifact.artifact.instructionPC 2392 = 3081 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2372 : CycleSubmission.Artifact.artifact.instructionPC 2393 = 3082 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2373 : CycleSubmission.Artifact.artifact.instructionPC 2394 = 3085 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2374 : CycleSubmission.Artifact.artifact.instructionPC 2395 = 3086 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2375 : CycleSubmission.Artifact.artifact.instructionPC 2396 = 3087 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2376 : CycleSubmission.Artifact.artifact.instructionPC 2397 = 3088 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2377 : CycleSubmission.Artifact.artifact.instructionPC 2398 = 3089 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2378 : CycleSubmission.Artifact.artifact.instructionPC 2399 = 3090 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2379 : CycleSubmission.Artifact.artifact.instructionPC 2400 = 3091 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2380 : CycleSubmission.Artifact.artifact.instructionPC 2401 = 3092 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2381 : CycleSubmission.Artifact.artifact.instructionPC 2402 = 3093 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2382 : CycleSubmission.Artifact.artifact.instructionPC 2403 = 3094 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2383 : CycleSubmission.Artifact.artifact.instructionPC 2404 = 3095 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2384 : CycleSubmission.Artifact.artifact.instructionPC 2405 = 3096 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2385 : CycleSubmission.Artifact.artifact.instructionPC 2406 = 3097 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2386 : CycleSubmission.Artifact.artifact.instructionPC 2407 = 3098 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2387 : CycleSubmission.Artifact.artifact.instructionPC 2408 = 3099 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2388 : CycleSubmission.Artifact.artifact.instructionPC 2409 = 3100 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2389 : CycleSubmission.Artifact.artifact.instructionPC 2410 = 3101 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2390 : CycleSubmission.Artifact.artifact.instructionPC 2411 = 3102 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2391 : CycleSubmission.Artifact.artifact.instructionPC 2412 = 3103 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2392 : CycleSubmission.Artifact.artifact.instructionPC 2413 = 3105 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2393 : CycleSubmission.Artifact.artifact.instructionPC 2414 = 3106 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2394 : CycleSubmission.Artifact.artifact.instructionPC 2415 = 3107 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2395 : CycleSubmission.Artifact.artifact.instructionPC 2416 = 3110 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2396 : CycleSubmission.Artifact.artifact.instructionPC 2417 = 3111 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2397 : CycleSubmission.Artifact.artifact.instructionPC 2418 = 3112 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2398 : CycleSubmission.Artifact.artifact.instructionPC 2419 = 3115 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2399 : CycleSubmission.Artifact.artifact.instructionPC 2420 = 3116 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2400 : CycleSubmission.Artifact.artifact.instructionPC 2421 = 3117 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2401 : CycleSubmission.Artifact.artifact.instructionPC 2422 = 3120 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2402 : CycleSubmission.Artifact.artifact.instructionPC 2423 = 3121 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2403 : CycleSubmission.Artifact.artifact.instructionPC 2424 = 3122 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2404 : CycleSubmission.Artifact.artifact.instructionPC 2425 = 3123 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2405 : CycleSubmission.Artifact.artifact.instructionPC 2426 = 3124 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2406 : CycleSubmission.Artifact.artifact.instructionPC 2427 = 3127 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2407 : CycleSubmission.Artifact.artifact.instructionPC 2428 = 3128 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2408 : CycleSubmission.Artifact.artifact.instructionPC 2429 = 3129 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2409 : CycleSubmission.Artifact.artifact.instructionPC 2430 = 3130 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2410 : CycleSubmission.Artifact.artifact.instructionPC 2431 = 3133 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2411 : CycleSubmission.Artifact.artifact.instructionPC 2432 = 3134 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2412 : CycleSubmission.Artifact.artifact.instructionPC 2433 = 3137 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2413 : CycleSubmission.Artifact.artifact.instructionPC 2434 = 3138 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2414 : CycleSubmission.Artifact.artifact.instructionPC 2435 = 3139 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2415 : CycleSubmission.Artifact.artifact.instructionPC 2436 = 3140 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2416 : CycleSubmission.Artifact.artifact.instructionPC 2437 = 3143 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2417 : CycleSubmission.Artifact.artifact.instructionPC 2438 = 3144 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2418 : CycleSubmission.Artifact.artifact.instructionPC 2439 = 3145 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem directInitialPC2009 : CycleSubmission.Artifact.artifact.instructionPC 2009 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2010 : CycleSubmission.Artifact.artifact.instructionPC 2010 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2011 : CycleSubmission.Artifact.artifact.instructionPC 2011 = 2558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2012 : CycleSubmission.Artifact.artifact.instructionPC 2012 = 2559 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2013 : CycleSubmission.Artifact.artifact.instructionPC 2013 = 2562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2014 : CycleSubmission.Artifact.artifact.instructionPC 2014 = 2563 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2015 : CycleSubmission.Artifact.artifact.instructionPC 2015 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2016 : CycleSubmission.Artifact.artifact.instructionPC 2016 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2017 : CycleSubmission.Artifact.artifact.instructionPC 2017 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2018 : CycleSubmission.Artifact.artifact.instructionPC 2018 = 2569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2019 : CycleSubmission.Artifact.artifact.instructionPC 2019 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2020 : CycleSubmission.Artifact.artifact.instructionPC 2020 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2021 : CycleSubmission.Artifact.artifact.instructionPC 2021 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2022 : CycleSubmission.Artifact.artifact.instructionPC 2022 = 2579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2023 : CycleSubmission.Artifact.artifact.instructionPC 2026 = 2585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2024 : CycleSubmission.Artifact.artifact.instructionPC 2027 = 2588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2025 : CycleSubmission.Artifact.artifact.instructionPC 2028 = 2589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2026 : CycleSubmission.Artifact.artifact.instructionPC 2029 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2027 : CycleSubmission.Artifact.artifact.instructionPC 2030 = 2591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2028 : CycleSubmission.Artifact.artifact.instructionPC 2031 = 2592 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2029 : CycleSubmission.Artifact.artifact.instructionPC 2032 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2030 : CycleSubmission.Artifact.artifact.instructionPC 2032 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2031 : CycleSubmission.Artifact.artifact.instructionPC 2033 = 2595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2032 : CycleSubmission.Artifact.artifact.instructionPC 2034 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2033 : CycleSubmission.Artifact.artifact.instructionPC 2035 = 2599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2034 : CycleSubmission.Artifact.artifact.instructionPC 2037 = 2601 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2035 : CycleSubmission.Artifact.artifact.instructionPC 2038 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2036 : CycleSubmission.Artifact.artifact.instructionPC 2039 = 2603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2037 : CycleSubmission.Artifact.artifact.instructionPC 2040 = 2604 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2038 : CycleSubmission.Artifact.artifact.instructionPC 2041 = 2607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2039 : CycleSubmission.Artifact.artifact.instructionPC 2042 = 2608 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2040 : CycleSubmission.Artifact.artifact.instructionPC 2043 = 2611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2041 : CycleSubmission.Artifact.artifact.instructionPC 2044 = 2612 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2042 : CycleSubmission.Artifact.artifact.instructionPC 2045 = 2615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2043 : CycleSubmission.Artifact.artifact.instructionPC 2046 = 2616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2044 : CycleSubmission.Artifact.artifact.instructionPC 2047 = 2619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2045 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2620 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2046 : CycleSubmission.Artifact.artifact.instructionPC 2049 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2047 : CycleSubmission.Artifact.artifact.instructionPC 2050 = 2624 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2048 : CycleSubmission.Artifact.artifact.instructionPC 2051 = 2627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2049 : CycleSubmission.Artifact.artifact.instructionPC 2052 = 2628 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2050 : CycleSubmission.Artifact.artifact.instructionPC 2053 = 2631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2051 : CycleSubmission.Artifact.artifact.instructionPC 2054 = 2632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2052 : CycleSubmission.Artifact.artifact.instructionPC 2055 = 2635 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2053 : CycleSubmission.Artifact.artifact.instructionPC 2056 = 2636 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2054 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2055 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2056 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2057 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2058 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2059 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2648 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem directWordInitPC2009 : CycleSubmission.Artifact.artifact.instructionPC 2009 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2010 : CycleSubmission.Artifact.artifact.instructionPC 2010 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2011 : CycleSubmission.Artifact.artifact.instructionPC 2011 = 2558 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2012 : CycleSubmission.Artifact.artifact.instructionPC 2012 = 2559 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2013 : CycleSubmission.Artifact.artifact.instructionPC 2013 = 2562 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2014 : CycleSubmission.Artifact.artifact.instructionPC 2014 = 2563 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2015 : CycleSubmission.Artifact.artifact.instructionPC 2015 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2016 : CycleSubmission.Artifact.artifact.instructionPC 2016 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2017 : CycleSubmission.Artifact.artifact.instructionPC 2017 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2018 : CycleSubmission.Artifact.artifact.instructionPC 2018 = 2569 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2019 : CycleSubmission.Artifact.artifact.instructionPC 2019 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2020 : CycleSubmission.Artifact.artifact.instructionPC 2020 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2021 : CycleSubmission.Artifact.artifact.instructionPC 2021 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2022 : CycleSubmission.Artifact.artifact.instructionPC 2022 = 2579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2023 : CycleSubmission.Artifact.artifact.instructionPC 2023 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2024 : CycleSubmission.Artifact.artifact.instructionPC 2024 = 2581 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2025 : CycleSubmission.Artifact.artifact.instructionPC 2025 = 2584 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2026 : CycleSubmission.Artifact.artifact.instructionPC 2026 = 2585 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2027 : CycleSubmission.Artifact.artifact.instructionPC 2027 = 2588 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2028 : CycleSubmission.Artifact.artifact.instructionPC 2028 = 2589 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2029 : CycleSubmission.Artifact.artifact.instructionPC 2029 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2030 : CycleSubmission.Artifact.artifact.instructionPC 2030 = 2591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2031 : CycleSubmission.Artifact.artifact.instructionPC 2031 = 2592 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2032 : CycleSubmission.Artifact.artifact.instructionPC 2032 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2033 : CycleSubmission.Artifact.artifact.instructionPC 2033 = 2595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2034 : CycleSubmission.Artifact.artifact.instructionPC 2034 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2035 : CycleSubmission.Artifact.artifact.instructionPC 2035 = 2599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2036 : CycleSubmission.Artifact.artifact.instructionPC 2036 = 2600 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2037 : CycleSubmission.Artifact.artifact.instructionPC 2037 = 2601 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2038 : CycleSubmission.Artifact.artifact.instructionPC 2038 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2039 : CycleSubmission.Artifact.artifact.instructionPC 2039 = 2603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2040 : CycleSubmission.Artifact.artifact.instructionPC 2040 = 2604 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2041 : CycleSubmission.Artifact.artifact.instructionPC 2041 = 2607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2042 : CycleSubmission.Artifact.artifact.instructionPC 2042 = 2608 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2043 : CycleSubmission.Artifact.artifact.instructionPC 2043 = 2611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2044 : CycleSubmission.Artifact.artifact.instructionPC 2044 = 2612 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2045 : CycleSubmission.Artifact.artifact.instructionPC 2045 = 2615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2046 : CycleSubmission.Artifact.artifact.instructionPC 2046 = 2616 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2047 : CycleSubmission.Artifact.artifact.instructionPC 2047 = 2619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2048 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2620 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2049 : CycleSubmission.Artifact.artifact.instructionPC 2049 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2050 : CycleSubmission.Artifact.artifact.instructionPC 2050 = 2624 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2051 : CycleSubmission.Artifact.artifact.instructionPC 2051 = 2627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2052 : CycleSubmission.Artifact.artifact.instructionPC 2052 = 2628 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2053 : CycleSubmission.Artifact.artifact.instructionPC 2053 = 2631 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2054 : CycleSubmission.Artifact.artifact.instructionPC 2054 = 2632 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2055 : CycleSubmission.Artifact.artifact.instructionPC 2055 = 2635 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2056 : CycleSubmission.Artifact.artifact.instructionPC 2056 = 2636 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2057 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2639 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2058 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2640 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2059 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2060 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2061 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2647 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2062 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2648 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
end CycleSubmission.Global.ShiftPCs

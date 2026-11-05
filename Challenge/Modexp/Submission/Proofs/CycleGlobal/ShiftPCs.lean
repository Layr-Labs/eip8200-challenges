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
  `(tactic| (rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl))

open Lean in
/-- An instruction pc through a constant-offset `PrefixPC` segment and the accepted proof base's
lemma for the matching old index. -/
local macro "pc_by_old " seg:ident i:num old:ident : tactic =>
  let seg' := mkIdent (`CycleSubmission.Global.PrefixPC ++ seg.getId)
  let old' := mkIdent (`Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs ++ old.getId)
  `(tactic| (rw [$seg':ident $i (by decide) (by decide)]; exact $old':ident))

@[simp] theorem pc2545 : IPC 1868 = 2390 := by pc_by_len

@[simp] theorem pc2546 : IPC 1869 = 2391 := by pc_by_len

@[simp] theorem pc2547 : IPC 1870 = 2392 := by pc_by_len

@[simp] theorem pc2548 : IPC 1871 = 2393 := by pc_by_len

@[simp] theorem pc2556 : IPC 1872 = 2394 := by pc_by_len

@[simp] theorem pc2559 : IPC 1873 = 2397 := by pc_by_len

@[simp] theorem pc2560 : IPC 1874 = 2398 := by pc_by_len

@[simp] theorem pc2561 : IPC 1875 = 2399 := by pc_by_len

@[simp] theorem pc2563 : IPC 1876 = 2401 := by pc_by_len

@[simp] theorem pc2566 : IPC 1877 = 2404 := by pc_by_len


@[simp] theorem pc2567 : IPC 1878 = 2405 := by pc_by_len

@[simp] theorem pc2570 : IPC 1879 = 2408 := by pc_by_len

@[simp] theorem pc2574 : IPC 1881 = 2412 := by pc_by_len

@[simp] theorem pc2586 : IPC 1892 = 2431 := by pc_by_len

@[simp] theorem pc2591 : IPC 1898 = 2440 := by pc_by_len

@[simp] theorem pc2592 : IPC 1899 = 2441 := by pc_by_len



@[simp] theorem pc2600 : IPC 1927 = 2487 := by pc_by_len

@[simp] theorem pc2604 : IPC 1929 = 2489 := by pc_by_len



@[simp] theorem pc2618 : IPC 1933 = 2495 := by pc_by_len

@[simp] theorem pc2619 : IPC 1934 = 2496 := by pc_by_len

@[simp] theorem pc2620 : IPC 1935 = 2497 := by pc_by_len

@[simp] theorem pc2621 : IPC 1936 = 2498 := by pc_by_len

@[simp] theorem pc2622 : IPC 1937 = 2499 := by pc_by_len

@[simp] theorem pc2623 : IPC 1938 = 2500 := by pc_by_len

@[simp] theorem pc2624 : IPC 1939 = 2501 := by pc_by_len

@[simp] theorem pc2625 : IPC 1940 = 2502 := by pc_by_len

@[simp] theorem pc2628 : IPC 1941 = 2503 := by pc_by_len

@[simp] theorem pc2629 : IPC 1942 = 2504 := by pc_by_len

@[simp] theorem pc2631 : IPC 1943 = 2506 := by pc_by_len

@[simp] theorem pc2632 : IPC 1944 = 2507 := by pc_by_len

@[simp] theorem pc2633 : IPC 1945 = 2510 := by pc_by_len

@[simp] theorem pc2636 : IPC 1946 = 2511 := by pc_by_len

@[simp] theorem pc2637 : IPC 1947 = 2513 := by pc_by_len

@[simp] theorem pc2638 : IPC 1948 = 2514 := by pc_by_len

@[simp] theorem pc2639 : IPC 1949 = 2518 := by pc_by_len

@[simp] theorem pc2641 : IPC 1950 = 2519 := by pc_by_len

@[simp] theorem pc2642 : IPC 1951 = 2520 := by pc_by_len

@[simp] theorem pc2644 : IPC 1952 = 2521 := by pc_by_len

@[simp] theorem pc2645 : IPC 1953 = 2522 := by pc_by_len

@[simp] theorem pc2648 : IPC 1954 = 2525 := by pc_by_len

@[simp] theorem pc2649 : IPC 1955 = 2526 := by pc_by_len

@[simp] theorem pc2650 : IPC 1956 = 2527 := by pc_by_len

@[simp] theorem pc2651 : IPC 1957 = 2528 := by pc_by_len

@[simp] theorem pc2652 : IPC 1958 = 2529 := by pc_by_len

@[simp] theorem pc2653 : IPC 1959 = 2530 := by pc_by_len

@[simp] theorem pc2654 : IPC 1960 = 2531 := by pc_by_len

@[simp] theorem pc2657 : IPC 1961 = 2534 := by pc_by_len

@[simp] theorem pc2658 : IPC 1962 = 2535 := by pc_by_len

@[simp] theorem pc2659 : IPC 1963 = 2538 := by pc_by_len

@[simp] theorem pc2695 : IPC 2009 = 2594 := by pc_by_len

@[simp] theorem pc2696 : IPC 2010 = 2595 := by pc_by_len

@[simp] theorem pc2698 : IPC 2011 = 2596 := by pc_by_len

@[simp] theorem pc2699 : IPC 2012 = 2597 := by pc_by_len





@[simp] theorem pc2702 : IPC 2013 = 2602 := by pc_by_len

@[simp] theorem pc2703 : IPC 2014 = 2603 := by pc_by_len

@[simp] theorem pc2705 : IPC 2015 = 2604 := by pc_by_len

@[simp] theorem pc2706 : IPC 2016 = 2605 := by pc_by_len

@[simp] theorem pc2713 : IPC 2019 = 2612 := by pc_by_len

@[simp] theorem pc3009 : IPC 2208 = 2902 := by pc_by_len

@[simp] theorem pc3010 : IPC 2209 = 2903 := by pc_by_len

@[simp] theorem pc3011 : IPC 2210 = 2904 := by pc_by_len

@[simp] theorem pc3012 : IPC 2211 = 2905 := by pc_by_len

@[simp] theorem pc3013 : IPC 2212 = 2906 := by pc_by_len





@[simp] theorem pc2712 : IPC 2018 = 2611 := by pc_by_len

@[simp] theorem pc3125 : IPC 2304 = 3015 := by pc_by_len







@[simp] theorem pc3171 : IPC 2341 = 3058 := by pc_by_len

@[simp] theorem pc3174 : IPC 2342 = 3061 := by pc_by_len

@[simp] theorem pc3175 : IPC 2343 = 3062 := by pc_by_len

@[simp] theorem pc3176 : IPC 2344 = 3063 := by pc_by_len

@[simp] theorem pc3177 : IPC 2345 = 3064 := by pc_by_len

@[simp] theorem pc3178 : IPC 2346 = 3065 := by pc_by_len

@[simp] theorem pc3179 : IPC 2347 = 3066 := by pc_by_len

@[simp] theorem pc3180 : IPC 2348 = 3067 := by pc_by_len

@[simp] theorem pc3181 : IPC 2349 = 3068 := by pc_by_len

@[simp] theorem pc3182 : IPC 2350 = 3069 := by pc_by_len

@[simp] theorem pc3183 : IPC 2351 = 3070 := by pc_by_len

@[simp] theorem pc3184 : IPC 2352 = 3071 := by pc_by_len

@[simp] theorem pc3185 : IPC 2353 = 3072 := by pc_by_len

@[simp] theorem pc3186 : IPC 2354 = 3073 := by pc_by_len

@[simp] theorem pc3187 : IPC 2355 = 3074 := by pc_by_len

@[simp] theorem pc3188 : IPC 2356 = 3075 := by pc_by_len

@[simp] theorem pc3191 : IPC 2357 = 3078 := by pc_by_len

@[simp] theorem pc3192 : IPC 2358 = 3079 := by pc_by_len




@[simp] theorem pcSaturate2992 : IPC 2289 = 2996 := by pc_by_len

@[simp] theorem pcSaturate2993 : IPC 2290 = 2997 := by pc_by_len

@[simp] theorem earlyExtraPC2883 : IPC 2697 = 3581 := by pc_by_len

@[simp] theorem earlyExtraPC2884 : IPC 2698 = 3582 := by pc_by_len

@[simp] theorem earlyExtraPC2885 : IPC 2699 = 3583 := by pc_by_len

@[simp] theorem earlyExtraPC2886 : IPC 2700 = 3584 := by pc_by_len

@[simp] theorem earlyExtraPC2888 : IPC 2701 = 3585 := by pc_by_len

@[simp] theorem earlyExtraPC2889 : IPC 2702 = 3586 := by pc_by_len

@[simp] theorem earlyExtraPC2890 : IPC 2703 = 3587 := by pc_by_len

@[simp] theorem earlyExtraPC2891 : IPC 2704 = 3590 := by pc_by_len

@[simp] theorem earlyExtraPC2892 : IPC 2705 = 3591 := by pc_by_len

@[simp] theorem earlyExtraPC2893 : IPC 2705 = 3591 := by pc_by_len

@[simp] theorem earlyExtraPC2894 : IPC 2706 = 3594 := by pc_by_len

@[simp] theorem earlyExtraPC2895 : IPC 2707 = 3595 := by pc_by_len

@[simp] theorem earlyExtraPC2896 : IPC 2719 = 3615 := by pc_by_len

@[simp] theorem earlyExtraPC2930 : IPC 2719 = 3615 := by pc_by_len

@[simp] theorem earlyExtraPC2931 : IPC 2719 = 3615 := by pc_by_len

@[simp] theorem earlyExtraPC2932 : IPC 2720 = 3618 := by pc_by_len

@[simp] theorem earlyExtraPC2933 : IPC 2721 = 3619 := by pc_by_len

@[simp] theorem earlyExtraPC2934 : IPC 2722 = 3620 := by pc_by_len

@[simp] theorem earlyExtraPC2935 : IPC 2723 = 3621 := by pc_by_len

@[simp] theorem earlyExtraPC2936 : IPC 2724 = 3624 := by pc_by_len

@[simp] theorem earlyExtraPC2937 : IPC 2725 = 3625 := by pc_by_len

@[simp] theorem earlyExtraPC2938 : IPC 2726 = 3627 := by pc_by_len

@[simp] theorem earlyExtraPC2939 : IPC 2727 = 3628 := by pc_by_len

@[simp] theorem earlyExtraPC2940 : IPC 2728 = 3629 := by pc_by_len

@[simp] theorem earlyExtraPC2941 : IPC 2729 = 3630 := by pc_by_len

@[simp] theorem earlyExtraPC2942 : IPC 2730 = 3631 := by pc_by_len

@[simp] theorem earlyExtraPC2943 : IPC 2731 = 3634 := by pc_by_len


@[simp] theorem pcC3009 : IPC 2346 = 3065 := by pc_by_len

@[simp] theorem pcC3010 : IPC 2347 = 3066 := by pc_by_len

@[simp] theorem pcC3011 : IPC 2348 = 3067 := by pc_by_len

@[simp] theorem pcC3019 : IPC 2355 = 3074 := by pc_by_len

@[simp] theorem pcC3020 : IPC 2356 = 3075 := by pc_by_len

@[simp] theorem pcC3021 : IPC 2357 = 3078 := by pc_by_len



/-! Program counters of the retained-T blocks the head-start table did not carry (generated from the artifact). -/

@[simp] theorem pcT2106 : IPC 1882 = 2413 := by pc_by_len

@[simp] theorem pcT2329 : IPC 2292 = 2999 := by pc_by_len

@[simp] theorem pcT2330 : IPC 2293 = 3000 := by pc_by_len

@[simp] theorem pcT2331 : IPC 2294 = 3001 := by pc_by_len

@[simp] theorem pcT2332 : IPC 2295 = 3002 := by pc_by_len

@[simp] theorem pcT2336 : IPC 2299 = 3008 := by pc_by_len

@[simp] theorem pcT2337 : IPC 2300 = 3009 := by pc_by_len

@[simp] theorem pcT2338 : IPC 2301 = 3010 := by pc_by_len

@[simp] theorem pcT2339 : IPC 2302 = 3011 := by pc_by_len

@[simp] theorem pcT2340 : IPC 2303 = 3014 := by pc_by_len

@[simp] theorem pcT2341 : IPC 2304 = 3015 := by pc_by_len

@[simp] theorem pcT2342 : IPC 2305 = 3016 := by pc_by_len

@[simp] theorem pcT2343 : IPC 2306 = 3017 := by pc_by_len

@[simp] theorem pcT2344 : IPC 2307 = 3018 := by pc_by_len

@[simp] theorem pcT2345 : IPC 2308 = 3019 := by pc_by_len

@[simp] theorem pcT2346 : IPC 2309 = 3020 := by pc_by_len

@[simp] theorem pcT2347 : IPC 2310 = 3021 := by pc_by_len

@[simp] theorem pcT2348 : IPC 2311 = 3022 := by pc_by_len

@[simp] theorem pcT2349 : IPC 2312 = 3025 := by pc_by_len

@[simp] theorem pcT2350 : IPC 2313 = 3026 := by pc_by_len

@[simp] theorem pcT2351 : IPC 2314 = 3027 := by pc_by_len

@[simp] theorem pcT2352 : IPC 2315 = 3028 := by pc_by_len

@[simp] theorem pcT2353 : IPC 2316 = 3029 := by pc_by_len

@[simp] theorem pcT2354 : IPC 2317 = 3030 := by pc_by_len

@[simp] theorem pcT2355 : IPC 2318 = 3031 := by pc_by_len

@[simp] theorem pcT2356 : IPC 2319 = 3032 := by pc_by_len

@[simp] theorem pcT2357 : IPC 2320 = 3033 := by pc_by_len

@[simp] theorem pcT2358 : IPC 2321 = 3034 := by pc_by_len

@[simp] theorem pcT2359 : IPC 2322 = 3035 := by pc_by_len

@[simp] theorem pcT2360 : IPC 2323 = 3036 := by pc_by_len

@[simp] theorem pcT2361 : IPC 2324 = 3037 := by pc_by_len

@[simp] theorem pcT2362 : IPC 2325 = 3038 := by pc_by_len

@[simp] theorem pcT2363 : IPC 2326 = 3039 := by pc_by_len

@[simp] theorem pcT2364 : IPC 2327 = 3040 := by pc_by_len

@[simp] theorem pcT2365 : IPC 2328 = 3043 := by pc_by_len

@[simp] theorem pcT2366 : IPC 2329 = 3044 := by pc_by_len

@[simp] theorem pcT2367 : IPC 2330 = 3045 := by pc_by_len

@[simp] theorem pcT2368 : IPC 2331 = 3046 := by pc_by_len

@[simp] theorem pcT2369 : IPC 2332 = 3047 := by pc_by_len

@[simp] theorem pcT2370 : IPC 2333 = 3050 := by pc_by_len

@[simp] theorem pcT2371 : IPC 2334 = 3051 := by pc_by_len

@[simp] theorem pcT2372 : IPC 2335 = 3052 := by pc_by_len

@[simp] theorem pcT2522 : IPC 2358 = 3079 := by pc_by_len

@[simp] theorem pcI2013 : IPC 1826 = 2317 := by pc_by_len

@[simp] theorem pcI2014 : IPC 1827 = 2318 := by pc_by_len

@[simp] theorem pcI2015 : IPC 1828 = 2319 := by pc_by_len

@[simp] theorem pcI2016 : IPC 1829 = 2321 := by pc_by_len

@[simp] theorem pcI2017 : IPC 1830 = 2322 := by pc_by_len

@[simp] theorem pcI2018 : IPC 1831 = 2325 := by pc_by_len

@[simp] theorem pcI2032 : IPC 1834 = 2329 := by pc_by_len

@[simp] theorem pcI2033 : IPC 1835 = 2330 := by pc_by_len

@[simp] theorem pcI2034 : IPC 1836 = 2332 := by pc_by_len

@[simp] theorem pcI2035 : IPC 1837 = 2335 := by pc_by_len

@[simp] theorem pcI2036 : IPC 1847 = 2350 := by pc_by_len

@[simp] theorem pcI2037 : IPC 1848 = 2351 := by pc_by_len

@[simp] theorem pcI2038 : IPC 1849 = 2354 := by pc_by_len

@[simp] theorem pcI2039 : IPC 1850 = 2355 := by pc_by_len

@[simp] theorem pcI2040 : IPC 1851 = 2356 := by pc_by_len

@[simp] theorem pcI2041 : IPC 1852 = 2358 := by pc_by_len

@[simp] theorem pcI2042 : IPC 1853 = 2359 := by pc_by_len

@[simp] theorem pcI2043 : IPC 1854 = 2363 := by pc_by_len

@[simp] theorem pcI2044 : IPC 1855 = 2364 := by pc_by_len

@[simp] theorem pcI2045 : IPC 1856 = 2366 := by pc_by_len

@[simp] theorem pcI2046 : IPC 1857 = 2367 := by pc_by_len

@[simp] theorem pcI2047 : IPC 1858 = 2369 := by pc_by_len

@[simp] theorem pcI2048 : IPC 1859 = 2370 := by pc_by_len

@[simp] theorem pcI2049 : IPC 1860 = 2373 := by pc_by_len

@[simp] theorem pcI2050 : IPC 1861 = 2375 := by pc_by_len

@[simp] theorem pcI2051 : IPC 1862 = 2376 := by pc_by_len

@[simp] theorem pcI2052 : IPC 1862 = 2376 := by pc_by_len

@[simp] theorem pcI2053 : IPC 1863 = 2377 := by pc_by_len

@[simp] theorem pcI2054 : IPC 1864 = 2380 := by pc_by_len

@[simp] theorem pcI2055 : IPC 1865 = 2383 := by pc_by_len

@[simp] theorem pcI2056 : IPC 1866 = 2386 := by pc_by_len

@[simp] theorem pcI2057 : IPC 1867 = 2389 := by pc_by_len

@[simp] theorem pcI2093 : IPC 1883 = 2414 := by pc_by_len

@[simp] theorem pcI2094 : IPC 1884 = 2417 := by pc_by_len

@[simp] theorem pcI2095 : IPC 1885 = 2420 := by pc_by_len

@[simp] theorem pcI2156 : IPC 1964 = 2539 := by pc_by_len

@[simp] theorem pcI2200 : IPC 2020 = 2613 := by pc_by_len

@[simp] theorem pcI2201 : IPC 2021 = 2614 := by pc_by_len

@[simp] theorem pcI2202 : IPC 2022 = 2615 := by pc_by_len

@[simp] theorem pcI2203 : IPC 2023 = 2616 := by pc_by_len

@[simp] theorem pcI2204 : IPC 2024 = 2617 := by pc_by_len

@[simp] theorem pcI2205 : IPC 2025 = 2618 := by pc_by_len

@[simp] theorem pcI2206 : IPC 2026 = 2621 := by pc_by_len

@[simp] theorem pcI2207 : IPC 2027 = 2622 := by pc_by_len

@[simp] theorem pcI2208 : IPC 2028 = 2625 := by pc_by_len

@[simp] theorem pcI2209 : IPC 2029 = 2626 := by pc_by_len

@[simp] theorem pcI2210 : IPC 2030 = 2629 := by pc_by_len

@[simp] theorem pcI2211 : IPC 2031 = 2630 := by pc_by_len

@[simp] theorem pcI2212 : IPC 2032 = 2633 := by pc_by_len

@[simp] theorem pcI2213 : IPC 2033 = 2634 := by pc_by_len

@[simp] theorem pcI2214 : IPC 2034 = 2637 := by pc_by_len

@[simp] theorem pcI2215 : IPC 2035 = 2638 := by pc_by_len

@[simp] theorem pcI2216 : IPC 2036 = 2641 := by pc_by_len

@[simp] theorem pcI2217 : IPC 2037 = 2642 := by pc_by_len

@[simp] theorem pcI2218 : IPC 2038 = 2645 := by pc_by_len

@[simp] theorem pcI2219 : IPC 2039 = 2646 := by pc_by_len

@[simp] theorem pcI2220 : IPC 2040 = 2649 := by pc_by_len

@[simp] theorem pcI2221 : IPC 2041 = 2650 := by pc_by_len

@[simp] theorem pcI2222 : IPC 2042 = 2653 := by pc_by_len

@[simp] theorem pcI2223 : IPC 2043 = 2654 := by pc_by_len

@[simp] theorem pcI2224 : IPC 2044 = 2657 := by pc_by_len

@[simp] theorem pcI2225 : IPC 2045 = 2658 := by pc_by_len

@[simp] theorem pcI2226 : IPC 2046 = 2661 := by pc_by_len

@[simp] theorem pcI2330 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2332 : IPC 2127 = 2811 := by pc_by_len

@[simp] theorem pcI2333 : IPC 2128 = 2812 := by pc_by_len

@[simp] theorem pcI2334 : IPC 2129 = 2813 := by pc_by_len

@[simp] theorem pcI2335 : IPC 2130 = 2814 := by pc_by_len

@[simp] theorem pcI2336 : IPC 2131 = 2815 := by pc_by_len

@[simp] theorem pcI2337 : IPC 2132 = 2816 := by pc_by_len

@[simp] theorem pcI2338 : IPC 2133 = 2817 := by pc_by_len

@[simp] theorem pcI2339 : IPC 2134 = 2818 := by pc_by_len

@[simp] theorem pcI2340 : IPC 2135 = 2819 := by pc_by_len

@[simp] theorem pcI2341 : IPC 2136 = 2822 := by pc_by_len

@[simp] theorem pcI2342 : IPC 2137 = 2823 := by pc_by_len

@[simp] theorem pcI2343 : IPC 2138 = 2824 := by pc_by_len

@[simp] theorem pcI2344 : IPC 2139 = 2825 := by pc_by_len

@[simp] theorem pcI2345 : IPC 2140 = 2826 := by pc_by_len

@[simp] theorem pcI2346 : IPC 2141 = 2827 := by pc_by_len

@[simp] theorem pcI2347 : IPC 2142 = 2828 := by pc_by_len

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

@[simp] theorem pcI2360 : IPC 2143 = 2829 := by pc_by_len

@[simp] theorem pcI2361 : IPC 2144 = 2830 := by pc_by_len

@[simp] theorem pcI2362 : IPC 2145 = 2831 := by pc_by_len

@[simp] theorem pcI2363 : IPC 2146 = 2832 := by pc_by_len

@[simp] theorem pcI2364 : IPC 2147 = 2833 := by pc_by_len

@[simp] theorem pcI2365 : IPC 2148 = 2834 := by pc_by_len

@[simp] theorem pcI2366 : IPC 2149 = 2835 := by pc_by_len

@[simp] theorem pcI2367 : IPC 2150 = 2836 := by pc_by_len

@[simp] theorem pcI2368 : IPC 2151 = 2837 := by pc_by_len

@[simp] theorem pcI2369 : IPC 2152 = 2838 := by pc_by_len

@[simp] theorem pcI2370 : IPC 2153 = 2839 := by pc_by_len

@[simp] theorem pcI2371 : IPC 2154 = 2840 := by pc_by_len

@[simp] theorem pcI2372 : IPC 2155 = 2841 := by pc_by_len

@[simp] theorem pcI2373 : IPC 2156 = 2842 := by pc_by_len

@[simp] theorem pcI2374 : IPC 2157 = 2843 := by pc_by_len

@[simp] theorem pcI2375 : IPC 2158 = 2846 := by pc_by_len

@[simp] theorem pcI2376 : IPC 2159 = 2847 := by pc_by_len

@[simp] theorem pcI2377 : IPC 2160 = 2848 := by pc_by_len

@[simp] theorem pcI2378 : IPC 2161 = 2849 := by pc_by_len

@[simp] theorem pcI2379 : IPC 2162 = 2850 := by pc_by_len

@[simp] theorem pcI2380 : IPC 2163 = 2853 := by pc_by_len

@[simp] theorem pcI2381 : IPC 2164 = 2854 := by pc_by_len

@[simp] theorem pcI2382 : IPC 2165 = 2855 := by pc_by_len

@[simp] theorem pcI2383 : IPC 2166 = 2856 := by pc_by_len

@[simp] theorem pcI2384 : IPC 2167 = 2857 := by pc_by_len

@[simp] theorem pcI2385 : IPC 2168 = 2858 := by pc_by_len

@[simp] theorem pcI2386 : IPC 2169 = 2859 := by pc_by_len

@[simp] theorem pcI2387 : IPC 2170 = 2860 := by pc_by_len

@[simp] theorem pcI2388 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2389 : IPC 2171 = 2861 := by pc_by_len

@[simp] theorem pcI2390 : IPC 2172 = 2862 := by pc_by_len

@[simp] theorem pcI2391 : IPC 2173 = 2863 := by pc_by_len

@[simp] theorem pcI2392 : IPC 2174 = 2864 := by pc_by_len

@[simp] theorem pcI2393 : IPC 2175 = 2865 := by pc_by_len

@[simp] theorem pcI2394 : IPC 2176 = 2866 := by pc_by_len

@[simp] theorem pcI2395 : IPC 2177 = 2867 := by pc_by_len

@[simp] theorem pcI2396 : IPC 2178 = 2868 := by pc_by_len

@[simp] theorem pcI2397 : IPC 2179 = 2869 := by pc_by_len

@[simp] theorem pcI2398 : IPC 2180 = 2870 := by pc_by_len

@[simp] theorem pcI2399 : IPC 2181 = 2871 := by pc_by_len

@[simp] theorem pcI2400 : IPC 2182 = 2872 := by pc_by_len

@[simp] theorem pcI2401 : IPC 2183 = 2873 := by pc_by_len

@[simp] theorem pcI2402 : IPC 2184 = 2874 := by pc_by_len

@[simp] theorem pcI2403 : IPC 2185 = 2875 := by pc_by_len

@[simp] theorem pcI2404 : IPC 2186 = 2878 := by pc_by_len

@[simp] theorem pcI2405 : IPC 2187 = 2879 := by pc_by_len

@[simp] theorem pcI2406 : IPC 2188 = 2880 := by pc_by_len

@[simp] theorem pcI2407 : IPC 2189 = 2881 := by pc_by_len

@[simp] theorem pcI2408 : IPC 2190 = 2882 := by pc_by_len

@[simp] theorem pcI2409 : IPC 2191 = 2885 := by pc_by_len

@[simp] theorem pcI2410 : IPC 2192 = 2886 := by pc_by_len

@[simp] theorem pcI2411 : IPC 2193 = 2887 := by pc_by_len

@[simp] theorem pcI2412 : IPC 2194 = 2888 := by pc_by_len

@[simp] theorem pcI2413 : IPC 2195 = 2889 := by pc_by_len

@[simp] theorem pcI2414 : IPC 2196 = 2890 := by pc_by_len

@[simp] theorem pcI2415 : IPC 2197 = 2891 := by pc_by_len

@[simp] theorem pcI2416 : IPC 2198 = 2892 := by pc_by_len

@[simp] theorem pcI2417 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2418 : IPC 2199 = 2893 := by pc_by_len

@[simp] theorem pcI2419 : IPC 2200 = 2894 := by pc_by_len

@[simp] theorem pcI2420 : IPC 2201 = 2895 := by pc_by_len

@[simp] theorem pcI2421 : IPC 2202 = 2896 := by pc_by_len

@[simp] theorem pcI2422 : IPC 2203 = 2897 := by pc_by_len

@[simp] theorem pcI2423 : IPC 2204 = 2898 := by pc_by_len

@[simp] theorem pcI2424 : IPC 2205 = 2899 := by pc_by_len

@[simp] theorem pcI2425 : IPC 2206 = 2900 := by pc_by_len

@[simp] theorem pcI2426 : IPC 2207 = 2901 := by pc_by_len

@[simp] theorem pcI2432 : IPC 2213 = 2907 := by pc_by_len

@[simp] theorem pcI2433 : IPC 2214 = 2910 := by pc_by_len

@[simp] theorem pcI2434 : IPC 2215 = 2911 := by pc_by_len

@[simp] theorem pcI2435 : IPC 2216 = 2912 := by pc_by_len

@[simp] theorem pcI2436 : IPC 2217 = 2913 := by pc_by_len

@[simp] theorem pcI2437 : IPC 2218 = 2914 := by pc_by_len

@[simp] theorem pcI2438 : IPC 2219 = 2917 := by pc_by_len

@[simp] theorem pcI2439 : IPC 2220 = 2918 := by pc_by_len

@[simp] theorem pcI2440 : IPC 2221 = 2919 := by pc_by_len

@[simp] theorem pcI2441 : IPC 2222 = 2920 := by pc_by_len

@[simp] theorem pcI2442 : IPC 2223 = 2921 := by pc_by_len

@[simp] theorem pcI2443 : IPC 2224 = 2922 := by pc_by_len

@[simp] theorem pcI2444 : IPC 2225 = 2923 := by pc_by_len

@[simp] theorem pcI2445 : IPC 2226 = 2924 := by pc_by_len

@[simp] theorem pcI2446 : IPC 2227 = 2925 := by pc_by_len

@[simp] theorem pcI2447 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2448 : IPC 2228 = 2926 := by pc_by_len

@[simp] theorem pcI2449 : IPC 2229 = 2927 := by pc_by_len

@[simp] theorem pcI2450 : IPC 2230 = 2928 := by pc_by_len

@[simp] theorem pcI2451 : IPC 2231 = 2929 := by pc_by_len

@[simp] theorem pcI2452 : IPC 2232 = 2930 := by pc_by_len

@[simp] theorem pcI2453 : IPC 2233 = 2931 := by pc_by_len

@[simp] theorem pcI2454 : IPC 2234 = 2932 := by pc_by_len

@[simp] theorem pcI2455 : IPC 2235 = 2933 := by pc_by_len

@[simp] theorem pcI2456 : IPC 2236 = 2934 := by pc_by_len

@[simp] theorem pcI2457 : IPC 2237 = 2935 := by pc_by_len

@[simp] theorem pcI2458 : IPC 2238 = 2936 := by pc_by_len

@[simp] theorem pcI2459 : IPC 2239 = 2937 := by pc_by_len

@[simp] theorem pcI2460 : IPC 2240 = 2938 := by pc_by_len

@[simp] theorem pcI2461 : IPC 2241 = 2939 := by pc_by_len

@[simp] theorem pcI2462 : IPC 2242 = 2942 := by pc_by_len

@[simp] theorem pcI2463 : IPC 2243 = 2943 := by pc_by_len

@[simp] theorem pcI2464 : IPC 2244 = 2944 := by pc_by_len

@[simp] theorem pcI2465 : IPC 2245 = 2945 := by pc_by_len

@[simp] theorem pcI2466 : IPC 2246 = 2946 := by pc_by_len

@[simp] theorem pcI2467 : IPC 2247 = 2949 := by pc_by_len

@[simp] theorem pcI2468 : IPC 2248 = 2950 := by pc_by_len

@[simp] theorem pcI2469 : IPC 2249 = 2951 := by pc_by_len

@[simp] theorem pcI2470 : IPC 2250 = 2952 := by pc_by_len

@[simp] theorem pcI2471 : IPC 2251 = 2953 := by pc_by_len

@[simp] theorem pcI2472 : IPC 2252 = 2954 := by pc_by_len

@[simp] theorem pcI2473 : IPC 2253 = 2955 := by pc_by_len

@[simp] theorem pcI2474 : IPC 2254 = 2956 := by pc_by_len

@[simp] theorem pcI2475 : IPC 2255 = 2957 := by pc_by_len

@[simp] theorem pcI2476 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2477 : IPC 2256 = 2958 := by pc_by_len

@[simp] theorem pcI2478 : IPC 2257 = 2959 := by pc_by_len

@[simp] theorem pcI2479 : IPC 2258 = 2960 := by pc_by_len

@[simp] theorem pcI2480 : IPC 2259 = 2961 := by pc_by_len

@[simp] theorem pcI2481 : IPC 2260 = 2962 := by pc_by_len

@[simp] theorem pcI2482 : IPC 2261 = 2963 := by pc_by_len

@[simp] theorem pcI2483 : IPC 2262 = 2964 := by pc_by_len

@[simp] theorem pcI2484 : IPC 2263 = 2965 := by pc_by_len

@[simp] theorem pcI2485 : IPC 2264 = 2966 := by pc_by_len

@[simp] theorem pcI2486 : IPC 2265 = 2967 := by pc_by_len

@[simp] theorem pcI2487 : IPC 2266 = 2968 := by pc_by_len

@[simp] theorem pcI2488 : IPC 2267 = 2969 := by pc_by_len

@[simp] theorem pcI2489 : IPC 2268 = 2970 := by pc_by_len

@[simp] theorem pcI2490 : IPC 2269 = 2971 := by pc_by_len

@[simp] theorem pcI2492 : IPC 2270 = 2975 := by pc_by_len

@[simp] theorem pcI2493 : IPC 2271 = 2976 := by pc_by_len

@[simp] theorem pcI2494 : IPC 2272 = 2977 := by pc_by_len

@[simp] theorem pcI2495 : IPC 2273 = 2978 := by pc_by_len

@[simp] theorem pcI2496 : IPC 2274 = 2979 := by pc_by_len

@[simp] theorem pcI2497 : IPC 2275 = 2982 := by pc_by_len

@[simp] theorem pcI2498 : IPC 2276 = 2983 := by pc_by_len

@[simp] theorem pcI2499 : IPC 2277 = 2984 := by pc_by_len

@[simp] theorem pcI2500 : IPC 2278 = 2985 := by pc_by_len

@[simp] theorem pcI2501 : IPC 2279 = 2986 := by pc_by_len

@[simp] theorem pcI2502 : IPC 2280 = 2987 := by pc_by_len

@[simp] theorem pcI2503 : IPC 2281 = 2988 := by pc_by_len

@[simp] theorem pcI2504 : IPC 2282 = 2989 := by pc_by_len

@[simp] theorem pcI2505 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2506 : IPC 2283 = 2990 := by pc_by_len

@[simp] theorem pcI2507 : IPC 2284 = 2991 := by pc_by_len

@[simp] theorem pcI2508 : IPC 2285 = 2992 := by pc_by_len

@[simp] theorem pcI2509 : IPC 2286 = 2993 := by pc_by_len

@[simp] theorem pcI2510 : IPC 2287 = 2994 := by pc_by_len

@[simp] theorem pcI2511 : IPC 2288 = 2995 := by pc_by_len

@[simp] theorem pcI2514 : IPC 2291 = 2998 := by pc_by_len

@[simp] theorem pcI2519 : IPC 2296 = 3003 := by pc_by_len

@[simp] theorem pcI2520 : IPC 2297 = 3004 := by pc_by_len

@[simp] theorem pcI2521 : IPC 2298 = 3007 := by pc_by_len

@[simp] theorem pcI2559 : IPC 2336 = 3053 := by pc_by_len

@[simp] theorem pcI2560 : IPC 2337 = 3054 := by pc_by_len

@[simp] theorem pcI2561 : IPC 2338 = 3055 := by pc_by_len

@[simp] theorem pcI2562 : IPC 2339 = 3056 := by pc_by_len

@[simp] theorem pcI2563 : IPC 2340 = 3057 := by pc_by_len

@[simp] theorem pcI2564 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2565 : IPC 2341 = 3058 := by pc_by_len

@[simp] theorem pcI2566 : IPC 2342 = 3061 := by pc_by_len

@[simp] theorem pcI2585 : IPC 2359 = 3080 := by pc_by_len

/-! ## The straight-line negation and the inline Newton chain (negun, inl693) -/

@[simp] theorem negunPC0 (i : Nat) (hi : 1838 ≤ i) (hii : i ≤ 1846) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2336, 2337, 2339, 2340, 2341, 2342, 2345, 2346, 2349] : List Nat)[i - 1838]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem negunPC1 (i : Nat) (hi : 1886 ≤ i) (hii : i ≤ 1932) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2421, 2422, 2424, 2425, 2428, 2429, 2431, 2432, 2433, 2434, 2437, 2438, 2440, 2441, 2442, 2445, 2446, 2448, 2449, 2450, 2453, 2454, 2456, 2457, 2458, 2461, 2462, 2464, 2465, 2466, 2469, 2470, 2471, 2474, 2475, 2476, 2479, 2480, 2482, 2483, 2484, 2487, 2488, 2489, 2490, 2491, 2492] : List Nat)[i - 1886]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem negunPC2 (i : Nat) (hi : 1965 ≤ i) (hii : i ≤ 2008) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2540, 2541, 2542, 2543, 2544, 2546, 2547, 2549, 2550, 2551, 2552, 2553, 2555, 2556, 2557, 2558, 2559, 2560, 2562, 2563, 2564, 2565, 2566, 2567, 2569, 2570, 2571, 2572, 2573, 2574, 2576, 2577, 2578, 2579, 2580, 2581, 2583, 2584, 2585, 2586, 2587, 2588, 2592, 2593] : List Nat)[i - 1965]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-! ## Directly stated pcs: E5 and the eight-limb loop head (2056 .. 2146), the bottom test,
the exit / E3 phase blocks and the repair loop (2381 .. 2465), and the appended four-limb
loop head (8548 .. 8610). -/

@[simp] theorem pcDual2056 : IPC 2047 = 2662 := by pc_by_len

@[simp] theorem pcDual2057 : IPC 2048 = 2663 := by pc_by_len

@[simp] theorem pcDual2065 : IPC 2049 = 2677 := by pc_by_len

@[simp] theorem pcDual2066 : IPC 2050 = 2678 := by pc_by_len

@[simp] theorem pcDual2067 : IPC 2051 = 2680 := by pc_by_len

@[simp] theorem pcDual2068 : IPC 2052 = 2681 := by pc_by_len

@[simp] theorem pcDual2069 : IPC 2053 = 2682 := by pc_by_len

@[simp] theorem pcDual2070 : IPC 2054 = 2684 := by pc_by_len

@[simp] theorem pcDual2071 : IPC 2055 = 2685 := by pc_by_len

@[simp] theorem pcDual2072 : IPC 2056 = 2688 := by pc_by_len

@[simp] theorem pcDual2073 : IPC 2057 = 2689 := by pc_by_len

@[simp] theorem pcDual2074 : IPC 2058 = 2690 := by pc_by_len

@[simp] theorem pcDual2075 : IPC 2059 = 2691 := by pc_by_len

@[simp] theorem pcDual2076 : IPC 2060 = 2692 := by pc_by_len

@[simp] theorem pcDual2077 : IPC 2061 = 2694 := by pc_by_len

@[simp] theorem pcDual2078 : IPC 2062 = 2695 := by pc_by_len

@[simp] theorem pcDual2079 : IPC 2063 = 2696 := by pc_by_len

@[simp] theorem pcDual2080 : IPC 2064 = 2697 := by pc_by_len

@[simp] theorem pcDual2081 : IPC 2065 = 2700 := by pc_by_len

@[simp] theorem pcDual2082 : IPC 2066 = 2701 := by pc_by_len

@[simp] theorem pcDual2083 : IPC 2067 = 2702 := by pc_by_len

@[simp] theorem pcDual2084 : IPC 2068 = 2703 := by pc_by_len

@[simp] theorem pcDual2085 : IPC 2069 = 2706 := by pc_by_len

@[simp] theorem pcDual2086 : IPC 2070 = 2707 := by pc_by_len

@[simp] theorem pcDual2087 : IPC 2071 = 2710 := by pc_by_len

@[simp] theorem pcDual2088 : IPC 2072 = 2711 := by pc_by_len

@[simp] theorem pcDual2089 : IPC 2073 = 2712 := by pc_by_len

@[simp] theorem pcDual2090 : IPC 2074 = 2713 := by pc_by_len

@[simp] theorem pcDual2091 : IPC 2075 = 2714 := by pc_by_len

@[simp] theorem pcDual2092 : IPC 2076 = 2715 := by pc_by_len

@[simp] theorem pcDual2093 : IPC 2077 = 2716 := by pc_by_len

@[simp] theorem pcDual2094 : IPC 2078 = 2719 := by pc_by_len

@[simp] theorem pcDual2095 : IPC 2079 = 2722 := by pc_by_len

@[simp] theorem pcDual2096 : IPC 2080 = 2723 := by pc_by_len

@[simp] theorem pcDual2100 : IPC 2081 = 2726 := by pc_by_len

@[simp] theorem pcDual2101 : IPC 2082 = 2727 := by pc_by_len

@[simp] theorem pcDual2102 : IPC 2083 = 2728 := by pc_by_len

@[simp] theorem pcDual2103 : IPC 2084 = 2729 := by pc_by_len

@[simp] theorem pcDual2104 : IPC 2085 = 2730 := by pc_by_len

@[simp] theorem pcDual2105 : IPC 2086 = 2731 := by pc_by_len

@[simp] theorem pcDual2106 : IPC 2087 = 2734 := by pc_by_len

@[simp] theorem pcDual2107 : IPC 2088 = 2735 := by pc_by_len

@[simp] theorem pcDual2108 : IPC 2089 = 2736 := by pc_by_len

@[simp] theorem pcDual2109 : IPC 2090 = 2739 := by pc_by_len

@[simp] theorem pcDual2110 : IPC 2091 = 2740 := by pc_by_len

@[simp] theorem pcDual2111 : IPC 2092 = 2741 := by pc_by_len

@[simp] theorem pcDual2112 : IPC 2093 = 2742 := by pc_by_len

@[simp] theorem pcDual2113 : IPC 2094 = 2743 := by pc_by_len

@[simp] theorem pcDual2114 : IPC 2095 = 2744 := by pc_by_len

@[simp] theorem pcDual2115 : IPC 2096 = 2745 := by pc_by_len

@[simp] theorem pcDual2116 : IPC 2097 = 2746 := by pc_by_len

@[simp] theorem pcDual2117 : IPC 2098 = 2747 := by pc_by_len

@[simp] theorem pcDual2118 : IPC 2099 = 2748 := by pc_by_len

@[simp] theorem pcDual2119 : IPC 2100 = 2749 := by pc_by_len

@[simp] theorem pcDual2120 : IPC 2101 = 2750 := by pc_by_len

@[simp] theorem pcDual2121 : IPC 2102 = 2751 := by pc_by_len

@[simp] theorem pcDual2122 : IPC 2103 = 2752 := by pc_by_len

@[simp] theorem pcDual2123 : IPC 2104 = 2753 := by pc_by_len

@[simp] theorem pcDual2124 : IPC 2105 = 2754 := by pc_by_len

@[simp] theorem pcDual2125 : IPC 2106 = 2755 := by pc_by_len

@[simp] theorem pcDual2126 : IPC 2107 = 2756 := by pc_by_len

@[simp] theorem pcDual2127 : IPC 2108 = 2758 := by pc_by_len

@[simp] theorem pcDual2128 : IPC 2109 = 2759 := by pc_by_len

@[simp] theorem pcDual2129 : IPC 2110 = 2760 := by pc_by_len

@[simp] theorem pcDual2130 : IPC 2111 = 2761 := by pc_by_len

@[simp] theorem pcDual2131 : IPC 2112 = 2762 := by pc_by_len

@[simp] theorem pcDual2132 : IPC 2113 = 2763 := by pc_by_len

@[simp] theorem pcDual2133 : IPC 2114 = 2764 := by pc_by_len

@[simp] theorem pcDual2134 : IPC 2115 = 2767 := by pc_by_len

@[simp] theorem pcDual2135 : IPC 2116 = 2768 := by pc_by_len

@[simp] theorem pcDual2136 : IPC 2117 = 2769 := by pc_by_len

@[simp] theorem pcDual2137 : IPC 2118 = 2770 := by pc_by_len

@[simp] theorem pcDual2138 : IPC 2119 = 2771 := by pc_by_len

@[simp] theorem pcDual2139 : IPC 2120 = 2772 := by pc_by_len

@[simp] theorem pcDual2141 : IPC 2121 = 2805 := by pc_by_len

@[simp] theorem pcDual2142 : IPC 2122 = 2806 := by pc_by_len

@[simp] theorem pcDual2143 : IPC 2123 = 2807 := by pc_by_len

@[simp] theorem pcDual2144 : IPC 2124 = 2808 := by pc_by_len

@[simp] theorem pcDual2145 : IPC 2125 = 2809 := by pc_by_len

@[simp] theorem pcDual2146 : IPC 2126 = 2810 := by pc_by_len

@[simp] theorem pcDual2381 : IPC 2360 = 3081 := by pc_by_len

@[simp] theorem pcDual2382 : IPC 2361 = 3084 := by pc_by_len

@[simp] theorem pcDual2383 : IPC 2362 = 3085 := by pc_by_len

@[simp] theorem pcDual2384 : IPC 2363 = 3086 := by pc_by_len

@[simp] theorem pcDual2385 : IPC 2364 = 3087 := by pc_by_len

@[simp] theorem pcDual2386 : IPC 2365 = 3088 := by pc_by_len

@[simp] theorem pcDual2387 : IPC 2366 = 3089 := by pc_by_len

@[simp] theorem pcDual2388 : IPC 2367 = 3090 := by pc_by_len

@[simp] theorem pcDual2389 : IPC 2368 = 3091 := by pc_by_len

@[simp] theorem pcDual2390 : IPC 2369 = 3092 := by pc_by_len

@[simp] theorem pcDual2391 : IPC 2370 = 3093 := by pc_by_len

@[simp] theorem pcDual2392 : IPC 2371 = 3096 := by pc_by_len

@[simp] theorem pcDual2393 : IPC 2372 = 3097 := by pc_by_len

@[simp] theorem pcDual2394 : IPC 2373 = 3098 := by pc_by_len

@[simp] theorem pcDual2395 : IPC 2374 = 3101 := by pc_by_len

@[simp] theorem pcDual2396 : IPC 2375 = 3102 := by pc_by_len

@[simp] theorem pcDual2397 : IPC 2376 = 3103 := by pc_by_len

@[simp] theorem pcDual2398 : IPC 2377 = 3106 := by pc_by_len

@[simp] theorem pcDual2399 : IPC 2378 = 3107 := by pc_by_len

@[simp] theorem pcDual2400 : IPC 2379 = 3109 := by pc_by_len

@[simp] theorem pcDual2401 : IPC 2380 = 3110 := by pc_by_len

@[simp] theorem pcDual2402 : IPC 2381 = 3111 := by pc_by_len

@[simp] theorem pcDual2403 : IPC 2382 = 3114 := by pc_by_len

@[simp] theorem pcDual2404 : IPC 2383 = 3117 := by pc_by_len

@[simp] theorem pcDual2405 : IPC 2384 = 3118 := by pc_by_len

@[simp] theorem pcDual2406 : IPC 2385 = 3119 := by pc_by_len

@[simp] theorem pcDual2407 : IPC 2386 = 3121 := by pc_by_len

@[simp] theorem pcDual2408 : IPC 2387 = 3122 := by pc_by_len

@[simp] theorem pcDual2409 : IPC 2388 = 3123 := by pc_by_len

@[simp] theorem pcDual2410 : IPC 2390 = 3125 := by pc_by_len

@[simp] theorem pcDual2411 : IPC 2391 = 3126 := by pc_by_len

@[simp] theorem pcDual2412 : IPC 2393 = 3160 := by pc_by_len

@[simp] theorem pcDual2413 : IPC 2394 = 3161 := by pc_by_len

@[simp] theorem pcDual2414 : IPC 2395 = 3162 := by pc_by_len

@[simp] theorem pcDual2415 : IPC 2396 = 3165 := by pc_by_len

@[simp] theorem pcDual2416 : IPC 2397 = 3166 := by pc_by_len

@[simp] theorem pcDual2417 : IPC 2398 = 3167 := by pc_by_len

@[simp] theorem pcDual2418 : IPC 2399 = 3168 := by pc_by_len

@[simp] theorem pcDual2419 : IPC 2400 = 3169 := by pc_by_len

@[simp] theorem pcDual2420 : IPC 2401 = 3172 := by pc_by_len

@[simp] theorem pcDual2421 : IPC 2402 = 3173 := by pc_by_len

@[simp] theorem pcDual2422 : IPC 2403 = 3174 := by pc_by_len

@[simp] theorem pcDual2423 : IPC 2404 = 3175 := by pc_by_len

@[simp] theorem pcDual2424 : IPC 2405 = 3176 := by pc_by_len

@[simp] theorem pcDual2425 : IPC 2406 = 3177 := by pc_by_len

@[simp] theorem pcDual2426 : IPC 2407 = 3178 := by pc_by_len

@[simp] theorem pcDual2427 : IPC 2408 = 3179 := by pc_by_len

@[simp] theorem pcDual2428 : IPC 2409 = 3180 := by pc_by_len

@[simp] theorem pcDual2429 : IPC 2410 = 3181 := by pc_by_len

@[simp] theorem pcDual2430 : IPC 2411 = 3182 := by pc_by_len

@[simp] theorem pcDual2431 : IPC 2412 = 3183 := by pc_by_len

@[simp] theorem pcDual2432 : IPC 2413 = 3184 := by pc_by_len

@[simp] theorem pcDual2433 : IPC 2414 = 3185 := by pc_by_len

@[simp] theorem pcDual2434 : IPC 2415 = 3186 := by pc_by_len

@[simp] theorem pcDual2435 : IPC 2416 = 3187 := by pc_by_len

@[simp] theorem pcDual2436 : IPC 2417 = 3188 := by pc_by_len

@[simp] theorem pcDual2437 : IPC 2418 = 3189 := by pc_by_len

@[simp] theorem pcDual2438 : IPC 2419 = 3190 := by pc_by_len

@[simp] theorem pcDual2439 : IPC 2420 = 3191 := by pc_by_len

@[simp] theorem pcDual2440 : IPC 2421 = 3192 := by pc_by_len

@[simp] theorem pcDual2441 : IPC 2490 = 3267 := by pc_by_len

@[simp] theorem pcDual2442 : IPC 2491 = 3270 := by pc_by_len

@[simp] theorem pcDual2443 : IPC 2492 = 3271 := by pc_by_len

@[simp] theorem pcDual2444 : IPC 2493 = 3272 := by pc_by_len

@[simp] theorem pcDual2445 : IPC 2494 = 3275 := by pc_by_len

@[simp] theorem pcDual2446 : IPC 2495 = 3276 := by pc_by_len

@[simp] theorem pcDual2447 : IPC 2496 = 3277 := by pc_by_len

@[simp] theorem pcDual2448 : IPC 2497 = 3280 := by pc_by_len

@[simp] theorem pcDual2449 : IPC 2498 = 3281 := by pc_by_len

@[simp] theorem pcDual2450 : IPC 2499 = 3282 := by pc_by_len

@[simp] theorem pcDual2451 : IPC 2500 = 3283 := by pc_by_len

@[simp] theorem pcDual2452 : IPC 2501 = 3284 := by pc_by_len

@[simp] theorem pcDual2453 : IPC 2502 = 3287 := by pc_by_len

@[simp] theorem pcDual2454 : IPC 2503 = 3288 := by pc_by_len

@[simp] theorem pcDual2455 : IPC 2504 = 3289 := by pc_by_len

@[simp] theorem pcDual2456 : IPC 2505 = 3290 := by pc_by_len

@[simp] theorem pcDual2457 : IPC 2506 = 3293 := by pc_by_len

@[simp] theorem pcDual2458 : IPC 2508 = 3295 := by pc_by_len

@[simp] theorem pcDual2459 : IPC 2509 = 3298 := by pc_by_len

@[simp] theorem pcDual2460 : IPC 2510 = 3299 := by pc_by_len

@[simp] theorem pcDual2461 : IPC 2511 = 3300 := by pc_by_len

@[simp] theorem pcDual2462 : IPC 2512 = 3301 := by pc_by_len

@[simp] theorem pcDual2463 : IPC 2513 = 3304 := by pc_by_len

@[simp] theorem pcDual2464 : IPC 2514 = 3305 := by pc_by_len

@[simp] theorem pcDual2465 : IPC 2515 = 3308 := by pc_by_len

@[simp] theorem pcDual8548 : IPC 8405 = 10724 := by pc_by_len

@[simp] theorem pcDual8549 : IPC 8406 = 10725 := by pc_by_len

@[simp] theorem pcDual8550 : IPC 8407 = 10726 := by pc_by_len

@[simp] theorem pcDual8551 : IPC 8408 = 10727 := by pc_by_len

@[simp] theorem pcDual8552 : IPC 8409 = 10728 := by pc_by_len

@[simp] theorem pcDual8553 : IPC 8410 = 10731 := by pc_by_len

@[simp] theorem pcDual8554 : IPC 8411 = 10734 := by pc_by_len

@[simp] theorem pcDual8555 : IPC 8412 = 10735 := by pc_by_len

@[simp] theorem pcDual8559 : IPC 8413 = 10738 := by pc_by_len

@[simp] theorem pcDual8560 : IPC 8414 = 10739 := by pc_by_len

@[simp] theorem pcDual8561 : IPC 8415 = 10740 := by pc_by_len

@[simp] theorem pcDual8562 : IPC 8416 = 10741 := by pc_by_len

@[simp] theorem pcDual8563 : IPC 8417 = 10742 := by pc_by_len

@[simp] theorem pcDual8564 : IPC 8418 = 10743 := by pc_by_len

@[simp] theorem pcDual8565 : IPC 8419 = 10746 := by pc_by_len

@[simp] theorem pcDual8566 : IPC 8420 = 10747 := by pc_by_len

@[simp] theorem pcDual8567 : IPC 8421 = 10748 := by pc_by_len

@[simp] theorem pcDual8568 : IPC 8422 = 10751 := by pc_by_len

@[simp] theorem pcDual8569 : IPC 8423 = 10752 := by pc_by_len

@[simp] theorem pcDual8570 : IPC 8424 = 10753 := by pc_by_len

@[simp] theorem pcDual8571 : IPC 8425 = 10754 := by pc_by_len

@[simp] theorem pcDual8572 : IPC 8426 = 10755 := by pc_by_len

@[simp] theorem pcDual8573 : IPC 8427 = 10756 := by pc_by_len

@[simp] theorem pcDual8574 : IPC 8428 = 10757 := by pc_by_len

@[simp] theorem pcDual8575 : IPC 8429 = 10758 := by pc_by_len

@[simp] theorem pcDual8576 : IPC 8430 = 10759 := by pc_by_len

@[simp] theorem pcDual8577 : IPC 8431 = 10760 := by pc_by_len

@[simp] theorem pcDual8578 : IPC 8432 = 10761 := by pc_by_len

@[simp] theorem pcDual8579 : IPC 8433 = 10762 := by pc_by_len

@[simp] theorem pcDual8580 : IPC 8434 = 10763 := by pc_by_len

@[simp] theorem pcDual8581 : IPC 8435 = 10764 := by pc_by_len

@[simp] theorem pcDual8582 : IPC 8436 = 10765 := by pc_by_len

@[simp] theorem pcDual8583 : IPC 8437 = 10766 := by pc_by_len

@[simp] theorem pcDual8584 : IPC 8438 = 10767 := by pc_by_len

@[simp] theorem pcDual8585 : IPC 8439 = 10768 := by pc_by_len

@[simp] theorem pcDual8586 : IPC 8440 = 10770 := by pc_by_len

@[simp] theorem pcDual8587 : IPC 8441 = 10771 := by pc_by_len

@[simp] theorem pcDual8588 : IPC 8442 = 10772 := by pc_by_len

@[simp] theorem pcDual8589 : IPC 8443 = 10773 := by pc_by_len

@[simp] theorem pcDual8590 : IPC 8444 = 10774 := by pc_by_len

@[simp] theorem pcDual8591 : IPC 8445 = 10775 := by pc_by_len

@[simp] theorem pcDual8592 : IPC 8446 = 10776 := by pc_by_len

@[simp] theorem pcDual8593 : IPC 8447 = 10779 := by pc_by_len

@[simp] theorem pcDual8594 : IPC 8448 = 10780 := by pc_by_len

@[simp] theorem pcDual8595 : IPC 8449 = 10781 := by pc_by_len

@[simp] theorem pcDual8596 : IPC 8450 = 10782 := by pc_by_len

@[simp] theorem pcDual8597 : IPC 8451 = 10783 := by pc_by_len

@[simp] theorem pcDual8598 : IPC 8452 = 10784 := by pc_by_len

@[simp] theorem pcDual8600 : IPC 8453 = 10817 := by pc_by_len

@[simp] theorem pcDual8601 : IPC 8454 = 10818 := by pc_by_len

@[simp] theorem pcDual8602 : IPC 8455 = 10819 := by pc_by_len

@[simp] theorem pcDual8603 : IPC 8456 = 10820 := by pc_by_len

@[simp] theorem pcDual8604 : IPC 8457 = 10821 := by pc_by_len

@[simp] theorem pcDual8605 : IPC 8458 = 10822 := by pc_by_len

@[simp] theorem pcDual8606 : IPC 8459 = 10823 := by pc_by_len

@[simp] theorem pcDual8607 : IPC 8460 = 10824 := by pc_by_len

@[simp] theorem pcDual8608 : IPC 8461 = 10825 := by pc_by_len

@[simp] theorem pcDual8609 : IPC 8462 = 10826 := by pc_by_len

@[simp] theorem pcDual8610 : IPC 8463 = 10827 := by pc_by_len

@[simp] theorem pcDual8611 : IPC 8464 = 10828 := by pc_by_len

@[simp] theorem pcDual8612 : IPC 8465 = 10829 := by pc_by_len

@[simp] theorem pcDual8613 : IPC 8466 = 10830 := by pc_by_len

@[simp] theorem pcDual8614 : IPC 8467 = 10831 := by pc_by_len

@[simp] theorem pcDual8615 : IPC 8468 = 10834 := by pc_by_len

@[simp] theorem pcDual8616 : IPC 8469 = 10835 := by pc_by_len

@[simp] theorem pcDual8617 : IPC 8470 = 10836 := by pc_by_len

@[simp] theorem pcDual8618 : IPC 8471 = 10837 := by pc_by_len

@[simp] theorem pcDual8619 : IPC 8472 = 10838 := by pc_by_len

@[simp] theorem pcDual8620 : IPC 8473 = 10839 := by pc_by_len

@[simp] theorem pcDual8621 : IPC 8474 = 10840 := by pc_by_len

@[simp] theorem pcDual8622 : IPC 8475 = 10841 := by pc_by_len

@[simp] theorem pcDual8623 : IPC 8476 = 10842 := by pc_by_len

@[simp] theorem pcDual8624 : IPC 8477 = 10843 := by pc_by_len

@[simp] theorem pcDual8625 : IPC 8478 = 10844 := by pc_by_len

@[simp] theorem pcDual8626 : IPC 8479 = 10845 := by pc_by_len

@[simp] theorem pcDual8627 : IPC 8480 = 10846 := by pc_by_len

@[simp] theorem pcDual8628 : IPC 8481 = 10847 := by pc_by_len

@[simp] theorem pcDual8629 : IPC 8482 = 10848 := by pc_by_len

@[simp] theorem pcDual8630 : IPC 8483 = 10849 := by pc_by_len

@[simp] theorem pcDual8631 : IPC 8484 = 10850 := by pc_by_len

@[simp] theorem pcDual8632 : IPC 8485 = 10851 := by pc_by_len

@[simp] theorem pcDual8633 : IPC 8486 = 10852 := by pc_by_len

@[simp] theorem pcDual8634 : IPC 8487 = 10853 := by pc_by_len

@[simp] theorem pcDual8635 : IPC 8488 = 10854 := by pc_by_len

@[simp] theorem pcDual8636 : IPC 8489 = 10855 := by pc_by_len

@[simp] theorem pcDual8637 : IPC 8490 = 10858 := by pc_by_len

@[simp] theorem pcDual8638 : IPC 8491 = 10859 := by pc_by_len

@[simp] theorem pcDual8639 : IPC 8492 = 10860 := by pc_by_len

@[simp] theorem pcDual8640 : IPC 8493 = 10861 := by pc_by_len

@[simp] theorem pcDual8641 : IPC 8494 = 10862 := by pc_by_len

@[simp] theorem pcDual8642 : IPC 8495 = 10865 := by pc_by_len

@[simp] theorem pcDual8643 : IPC 8496 = 10866 := by pc_by_len

@[simp] theorem pcDual8644 : IPC 8497 = 10867 := by pc_by_len

@[simp] theorem pcDual8645 : IPC 8498 = 10868 := by pc_by_len

@[simp] theorem pcDual8646 : IPC 8499 = 10869 := by pc_by_len

@[simp] theorem pcDual8647 : IPC 8500 = 10870 := by pc_by_len

@[simp] theorem pcDual8648 : IPC 8501 = 10871 := by pc_by_len

@[simp] theorem pcDual8649 : IPC 8502 = 10872 := by pc_by_len

@[simp] theorem pcDual8650 : IPC 8503 = 10873 := by pc_by_len

@[simp] theorem pcDual8651 : IPC 8504 = 10874 := by pc_by_len

@[simp] theorem pcDual8652 : IPC 8505 = 10875 := by pc_by_len

@[simp] theorem pcDual8653 : IPC 8506 = 10876 := by pc_by_len

@[simp] theorem pcDual8654 : IPC 8507 = 10877 := by pc_by_len

@[simp] theorem pcDual8655 : IPC 8508 = 10878 := by pc_by_len

@[simp] theorem pcDual8656 : IPC 8509 = 10879 := by pc_by_len

@[simp] theorem pcDual8657 : IPC 8510 = 10880 := by pc_by_len

@[simp] theorem pcDual8658 : IPC 8511 = 10881 := by pc_by_len

@[simp] theorem pcDual8659 : IPC 8512 = 10882 := by pc_by_len

@[simp] theorem pcDual8660 : IPC 8513 = 10883 := by pc_by_len

@[simp] theorem pcDual8661 : IPC 8514 = 10884 := by pc_by_len

@[simp] theorem pcDual8662 : IPC 8515 = 10885 := by pc_by_len

@[simp] theorem pcDual8663 : IPC 8516 = 10886 := by pc_by_len

@[simp] theorem pcDual8664 : IPC 8517 = 10887 := by pc_by_len

@[simp] theorem pcDual8665 : IPC 8518 = 10890 := by pc_by_len

@[simp] theorem pcDual8666 : IPC 8519 = 10891 := by pc_by_len

@[simp] theorem pcDual8667 : IPC 8520 = 10892 := by pc_by_len

@[simp] theorem pcDual8668 : IPC 8521 = 10893 := by pc_by_len

@[simp] theorem pcDual8669 : IPC 8522 = 10894 := by pc_by_len

@[simp] theorem pcDual8670 : IPC 8523 = 10897 := by pc_by_len

@[simp] theorem pcDual8671 : IPC 8524 = 10898 := by pc_by_len

@[simp] theorem pcDual8672 : IPC 8525 = 10899 := by pc_by_len

@[simp] theorem pcDual8673 : IPC 8526 = 10900 := by pc_by_len

@[simp] theorem pcDual8674 : IPC 8527 = 10901 := by pc_by_len

@[simp] theorem pcDual8675 : IPC 8528 = 10902 := by pc_by_len

@[simp] theorem pcDual8676 : IPC 8529 = 10903 := by pc_by_len

@[simp] theorem pcDual8677 : IPC 8530 = 10904 := by pc_by_len

@[simp] theorem pcDual8678 : IPC 8531 = 10905 := by pc_by_len

@[simp] theorem pcDual8679 : IPC 8532 = 10908 := by pc_by_len

@[simp] theorem pcDual8680 : IPC 8533 = 10909 := by pc_by_len

@[simp] theorem pcDual8681 : IPC 8534 = 10910 := by pc_by_len

@[simp] theorem pcDual8682 : IPC 8535 = 10911 := by pc_by_len

@[simp] theorem pcDual8683 : IPC 8536 = 10912 := by pc_by_len

@[simp] theorem pcDual8684 : IPC 8537 = 10913 := by pc_by_len

@[simp] theorem pcDual8685 : IPC 8538 = 10914 := by pc_by_len

@[simp] theorem pcDual8686 : IPC 8539 = 10915 := by pc_by_len

@[simp] theorem pcDual8687 : IPC 8540 = 10916 := by pc_by_len

@[simp] theorem pcDual8688 : IPC 8541 = 10917 := by pc_by_len

@[simp] theorem pcDual8689 : IPC 8542 = 10918 := by pc_by_len

@[simp] theorem pcDual8690 : IPC 8543 = 10919 := by pc_by_len

@[simp] theorem pcDual8691 : IPC 8544 = 10920 := by pc_by_len

@[simp] theorem pcDual8692 : IPC 8545 = 10921 := by pc_by_len

@[simp] theorem pcDual8693 : IPC 8546 = 10922 := by pc_by_len

@[simp] theorem pcDual8694 : IPC 8547 = 10923 := by pc_by_len

@[simp] theorem pcDual8695 : IPC 8548 = 10926 := by pc_by_len

@[simp] theorem pcDual8696 : IPC 8549 = 10927 := by pc_by_len

@[simp] theorem pcDual8697 : IPC 8550 = 10928 := by pc_by_len

@[simp] theorem pcDual8698 : IPC 8551 = 10929 := by pc_by_len

@[simp] theorem pcDual8699 : IPC 8552 = 10930 := by pc_by_len

@[simp] theorem pcDual8700 : IPC 8553 = 10933 := by pc_by_len

@[simp] theorem pcDual8701 : IPC 8554 = 10934 := by pc_by_len

@[simp] theorem pcDual8702 : IPC 8555 = 10935 := by pc_by_len

@[simp] theorem pcDual8703 : IPC 8556 = 10936 := by pc_by_len

@[simp] theorem pcDual8704 : IPC 8557 = 10937 := by pc_by_len

@[simp] theorem pcDual8705 : IPC 8558 = 10938 := by pc_by_len

@[simp] theorem pcDual8706 : IPC 8559 = 10939 := by pc_by_len

@[simp] theorem pcDual8707 : IPC 8560 = 10940 := by pc_by_len

@[simp] theorem pcDual8708 : IPC 8561 = 10941 := by pc_by_len

@[simp] theorem pcDual8709 : IPC 8562 = 10944 := by pc_by_len

@[simp] theorem pcDual8710 : IPC 8563 = 10945 := by pc_by_len

@[simp] theorem pcDual8711 : IPC 8564 = 10946 := by pc_by_len

@[simp] theorem pcDual8712 : IPC 8565 = 10947 := by pc_by_len

@[simp] theorem pcDual8713 : IPC 8566 = 10948 := by pc_by_len

@[simp] theorem pcDual8714 : IPC 8567 = 10949 := by pc_by_len

@[simp] theorem pcDual8715 : IPC 8568 = 10950 := by pc_by_len

@[simp] theorem pcDual8716 : IPC 8569 = 10951 := by pc_by_len

@[simp] theorem pcDual8717 : IPC 8570 = 10952 := by pc_by_len

@[simp] theorem pcDual8718 : IPC 8571 = 10953 := by pc_by_len

@[simp] theorem pcDual8719 : IPC 8572 = 10954 := by pc_by_len

@[simp] theorem pcDual8720 : IPC 8573 = 10955 := by pc_by_len

@[simp] theorem pcDual8721 : IPC 8574 = 10956 := by pc_by_len

@[simp] theorem pcDual8722 : IPC 8575 = 10957 := by pc_by_len

@[simp] theorem pcDual8723 : IPC 8576 = 10958 := by pc_by_len

@[simp] theorem pcDual8724 : IPC 8577 = 10961 := by pc_by_len

@[simp] theorem pcDual8725 : IPC 8578 = 10962 := by pc_by_len

@[simp] theorem pcDual8726 : IPC 8579 = 10963 := by pc_by_len

@[simp] theorem pcDual8727 : IPC 8580 = 10964 := by pc_by_len

@[simp] theorem pcDual8728 : IPC 8581 = 10969 := by pc_by_len

@[simp] theorem pcDual8729 : IPC 8582 = 10970 := by pc_by_len

@[simp] theorem pcDual8730 : IPC 8583 = 10971 := by pc_by_len

@[simp] theorem pcDual8731 : IPC 8584 = 10972 := by pc_by_len

@[simp] theorem pcDual8732 : IPC 8585 = 10973 := by pc_by_len

@[simp] theorem pcDual8733 : IPC 8586 = 10974 := by pc_by_len

@[simp] theorem pcDual8734 : IPC 8587 = 10975 := by pc_by_len

@[simp] theorem pcDual8735 : IPC 8588 = 10978 := by pc_by_len

end CycleSubmission.Global.ShiftPCs

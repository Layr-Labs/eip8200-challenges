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

private abbrev cachedArtifact := CycleSubmission.Artifact.artifact

namespace CycleSubmission.Global.ShiftPCs
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast


open EvmSemantics
open EvmSemantics.EVM

local notation "IPC" => cachedArtifact.instructionPC

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

@[simp] theorem pc2545 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pc2546 : IPC 1847 = 2339 := by pc_by_len

@[simp] theorem pc2547 : IPC 1848 = 2340 := by pc_by_len

@[simp] theorem pc2548 : IPC 1849 = 2341 := by pc_by_len

@[simp] theorem pc2556 : IPC 1850 = 2342 := by pc_by_len

@[simp] theorem pc2559 : IPC 1851 = 2344 := by pc_by_len

@[simp] theorem pc2560 : IPC 1852 = 2345 := by pc_by_len

@[simp] theorem pc2561 : IPC 1853 = 2346 := by pc_by_len

@[simp] theorem pc2563 : IPC 1854 = 2348 := by pc_by_len

@[simp] theorem pc2566 : IPC 1855 = 2351 := by pc_by_len


@[simp] theorem pc2567 : IPC 1856 = 2352 := by pc_by_len

@[simp] theorem pc2570 : IPC 1857 = 2355 := by pc_by_len

@[simp] theorem pc2574 : IPC 1859 = 2359 := by pc_by_len

@[simp] theorem pc2586 : IPC 1870 = 2378 := by pc_by_len

@[simp] theorem pc2591 : IPC 1876 = 2387 := by pc_by_len

@[simp] theorem pc2592 : IPC 1877 = 2388 := by pc_by_len



@[simp] theorem pc2600 : IPC 1905 = 2433 := by pc_by_len

@[simp] theorem pc2604 : IPC 1907 = 2435 := by pc_by_len



@[simp] theorem pc2618 : IPC 1911 = 2441 := by pc_by_len

@[simp] theorem pc2619 : IPC 1912 = 2442 := by pc_by_len

@[simp] theorem pc2620 : IPC 1913 = 2443 := by pc_by_len

@[simp] theorem pc2621 : IPC 1914 = 2444 := by pc_by_len

@[simp] theorem pc2622 : IPC 1915 = 2445 := by pc_by_len

@[simp] theorem pc2623 : IPC 1916 = 2446 := by pc_by_len

@[simp] theorem pc2624 : IPC 1917 = 2447 := by pc_by_len

@[simp] theorem pc2625 : IPC 1917 = 2447 := by pc_by_len

@[simp] theorem pc2628 : IPC 1918 = 2448 := by pc_by_len

@[simp] theorem pc2629 : IPC 1919 = 2449 := by pc_by_len

@[simp] theorem pc2631 : IPC 1920 = 2451 := by pc_by_len

@[simp] theorem pc2632 : IPC 1921 = 2452 := by pc_by_len

@[simp] theorem pc2633 : IPC 1922 = 2455 := by pc_by_len

@[simp] theorem pc2636 : IPC 1923 = 2456 := by pc_by_len

@[simp] theorem pc2637 : IPC 1924 = 2458 := by pc_by_len

@[simp] theorem pc2638 : IPC 1925 = 2459 := by pc_by_len

@[simp] theorem pc2639 : IPC 1926 = 2460 := by pc_by_len

@[simp] theorem pc2641 : IPC 1927 = 2463 := by pc_by_len

@[simp] theorem pc2642 : IPC 1928 = 2464 := by pc_by_len

@[simp] theorem pc2644 : IPC 1929 = 2465 := by pc_by_len

@[simp] theorem pc2645 : IPC 1930 = 2466 := by pc_by_len

@[simp] theorem pc2648 : IPC 1931 = 2469 := by pc_by_len

@[simp] theorem pc2649 : IPC 1932 = 2470 := by pc_by_len

@[simp] theorem pc2650 : IPC 1933 = 2471 := by pc_by_len

@[simp] theorem pc2651 : IPC 1934 = 2472 := by pc_by_len

@[simp] theorem pc2652 : IPC 1935 = 2473 := by pc_by_len

@[simp] theorem pc2653 : IPC 1936 = 2474 := by pc_by_len

@[simp] theorem pc2654 : IPC 1937 = 2475 := by pc_by_len

@[simp] theorem pc2657 : IPC 1938 = 2478 := by pc_by_len

@[simp] theorem pc2658 : IPC 1939 = 2479 := by pc_by_len

@[simp] theorem pc2659 : IPC 1940 = 2482 := by pc_by_len

@[simp] theorem pc2695 : IPC 1986 = 2536 := by pc_by_len

@[simp] theorem pc2696 : IPC 1987 = 2537 := by pc_by_len

@[simp] theorem pc2698 : IPC 1988 = 2538 := by pc_by_len

@[simp] theorem pc2699 : IPC 1989 = 2539 := by pc_by_len





@[simp] theorem pc2702 : IPC 1990 = 2542 := by pc_by_len

@[simp] theorem pc2703 : IPC 1991 = 2543 := by pc_by_len

@[simp] theorem pc2705 : IPC 1992 = 2544 := by pc_by_len

@[simp] theorem pc2706 : IPC 1993 = 2545 := by pc_by_len

@[simp] theorem pc2713 : IPC 1996 = 2550 := by pc_by_len

@[simp] theorem pc3009 : IPC 2203 = 2825 := by pc_by_len

@[simp] theorem pc3010 : IPC 2204 = 2826 := by pc_by_len

@[simp] theorem pc3011 : IPC 2205 = 2827 := by pc_by_len

@[simp] theorem pc3012 : IPC 2206 = 2828 := by pc_by_len

@[simp] theorem pc3013 : IPC 2207 = 2829 := by pc_by_len





@[simp] theorem pc2712 : IPC 1995 = 2549 := by pc_by_len

@[simp] theorem pc3125 : IPC 2299 = 2937 := by pc_by_len







@[simp] theorem pc3171 : IPC 2336 = 2980 := by pc_by_len

@[simp] theorem pc3174 : IPC 2337 = 2983 := by pc_by_len

@[simp] theorem pc3175 : IPC 2338 = 2984 := by pc_by_len

@[simp] theorem pc3176 : IPC 2339 = 2985 := by pc_by_len

@[simp] theorem pc3177 : IPC 2340 = 2986 := by pc_by_len

@[simp] theorem pc3178 : IPC 2341 = 2987 := by pc_by_len

@[simp] theorem pc3179 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3180 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3181 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3182 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3183 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3184 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3185 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3186 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3187 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3188 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3191 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pc3192 : IPC 2342 = 2990 := by pc_by_len




@[simp] theorem pcSaturate2992 : IPC 2284 = 2918 := by pc_by_len

@[simp] theorem pcSaturate2993 : IPC 2285 = 2919 := by pc_by_len

@[simp] theorem earlyExtraPC2883 : IPC 2595 = 3299 := by pc_by_len

@[simp] theorem earlyExtraPC2884 : IPC 2596 = 3300 := by pc_by_len

@[simp] theorem earlyExtraPC2885 : IPC 2597 = 3301 := by pc_by_len

@[simp] theorem earlyExtraPC2886 : IPC 2598 = 3302 := by pc_by_len

@[simp] theorem earlyExtraPC2888 : IPC 2599 = 3303 := by pc_by_len

@[simp] theorem earlyExtraPC2889 : IPC 2600 = 3304 := by pc_by_len

@[simp] theorem earlyExtraPC2890 : IPC 2601 = 3305 := by pc_by_len

@[simp] theorem earlyExtraPC2891 : IPC 2602 = 3308 := by pc_by_len

@[simp] theorem earlyExtraPC2892 : IPC 2603 = 3309 := by pc_by_len

@[simp] theorem earlyExtraPC2893 : IPC 2603 = 3309 := by pc_by_len

@[simp] theorem earlyExtraPC2894 : IPC 2604 = 3312 := by pc_by_len

@[simp] theorem earlyExtraPC2895 : IPC 2605 = 3313 := by pc_by_len

@[simp] theorem earlyExtraPC2896 : IPC 2617 = 3332 := by pc_by_len

@[simp] theorem earlyExtraPC2930 : IPC 2617 = 3332 := by pc_by_len

@[simp] theorem earlyExtraPC2931 : IPC 2617 = 3332 := by pc_by_len

@[simp] theorem earlyExtraPC2932 : IPC 2617 = 3332 := by pc_by_len

@[simp] theorem earlyExtraPC2933 : IPC 2636 = 3355 := by pc_by_len

@[simp] theorem earlyExtraPC2934 : IPC 3597 = 4605 := by pc_by_len

@[simp] theorem earlyExtraPC2935 : IPC 3598 = 4606 := by pc_by_len

@[simp] theorem earlyExtraPC2936 : IPC 3599 = 4609 := by pc_by_len

@[simp] theorem earlyExtraPC2937 : IPC 3600 = 4610 := by pc_by_len

@[simp] theorem earlyExtraPC2938 : IPC 3601 = 4612 := by pc_by_len

@[simp] theorem earlyExtraPC2939 : IPC 3602 = 4613 := by pc_by_len

@[simp] theorem earlyExtraPC2940 : IPC 3603 = 4614 := by pc_by_len

@[simp] theorem earlyExtraPC2941 : IPC 3604 = 4615 := by pc_by_len

@[simp] theorem earlyExtraPC2942 : IPC 3605 = 4616 := by pc_by_len

@[simp] theorem earlyExtraPC2943 : IPC 3606 = 4619 := by pc_by_len


@[simp] theorem pcC3009 : IPC 2341 = 2987 := by pc_by_len

@[simp] theorem pcC3010 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pcC3011 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pcC3019 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pcC3020 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pcC3021 : IPC 2342 = 2990 := by pc_by_len



/-! Program counters of the retained-T blocks the head-start table did not carry (generated from the artifact). -/

@[simp] theorem pcT2106 : IPC 1860 = 2360 := by pc_by_len

@[simp] theorem pcT2329 : IPC 2287 = 2921 := by pc_by_len

@[simp] theorem pcT2330 : IPC 2288 = 2922 := by pc_by_len

@[simp] theorem pcT2331 : IPC 2289 = 2923 := by pc_by_len

@[simp] theorem pcT2332 : IPC 2290 = 2924 := by pc_by_len

@[simp] theorem pcT2336 : IPC 2294 = 2930 := by pc_by_len

@[simp] theorem pcT2337 : IPC 2295 = 2931 := by pc_by_len

@[simp] theorem pcT2338 : IPC 2296 = 2932 := by pc_by_len

@[simp] theorem pcT2339 : IPC 2297 = 2933 := by pc_by_len

@[simp] theorem pcT2340 : IPC 2298 = 2936 := by pc_by_len

@[simp] theorem pcT2341 : IPC 2299 = 2937 := by pc_by_len

@[simp] theorem pcT2342 : IPC 2300 = 2938 := by pc_by_len

@[simp] theorem pcT2343 : IPC 2301 = 2939 := by pc_by_len

@[simp] theorem pcT2344 : IPC 2302 = 2940 := by pc_by_len

@[simp] theorem pcT2345 : IPC 2303 = 2941 := by pc_by_len

@[simp] theorem pcT2346 : IPC 2304 = 2942 := by pc_by_len

@[simp] theorem pcT2347 : IPC 2305 = 2943 := by pc_by_len

@[simp] theorem pcT2348 : IPC 2306 = 2944 := by pc_by_len

@[simp] theorem pcT2349 : IPC 2307 = 2947 := by pc_by_len

@[simp] theorem pcT2350 : IPC 2308 = 2948 := by pc_by_len

@[simp] theorem pcT2351 : IPC 2309 = 2949 := by pc_by_len

@[simp] theorem pcT2352 : IPC 2310 = 2950 := by pc_by_len

@[simp] theorem pcT2353 : IPC 2311 = 2951 := by pc_by_len

@[simp] theorem pcT2354 : IPC 2312 = 2952 := by pc_by_len

@[simp] theorem pcT2355 : IPC 2313 = 2953 := by pc_by_len

@[simp] theorem pcT2356 : IPC 2314 = 2954 := by pc_by_len

@[simp] theorem pcT2357 : IPC 2315 = 2955 := by pc_by_len

@[simp] theorem pcT2358 : IPC 2316 = 2956 := by pc_by_len

@[simp] theorem pcT2359 : IPC 2317 = 2957 := by pc_by_len

@[simp] theorem pcT2360 : IPC 2318 = 2958 := by pc_by_len

@[simp] theorem pcT2361 : IPC 2319 = 2959 := by pc_by_len

@[simp] theorem pcT2362 : IPC 2320 = 2960 := by pc_by_len

@[simp] theorem pcT2363 : IPC 2321 = 2961 := by pc_by_len

@[simp] theorem pcT2364 : IPC 2322 = 2962 := by pc_by_len

@[simp] theorem pcT2365 : IPC 2323 = 2965 := by pc_by_len

@[simp] theorem pcT2366 : IPC 2324 = 2966 := by pc_by_len

@[simp] theorem pcT2367 : IPC 2325 = 2967 := by pc_by_len

@[simp] theorem pcT2368 : IPC 2326 = 2968 := by pc_by_len

@[simp] theorem pcT2369 : IPC 2327 = 2969 := by pc_by_len

@[simp] theorem pcT2370 : IPC 2328 = 2972 := by pc_by_len

@[simp] theorem pcT2371 : IPC 2329 = 2973 := by pc_by_len

@[simp] theorem pcT2372 : IPC 2330 = 2974 := by pc_by_len

@[simp] theorem pcT2522 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pcI2013 : IPC 1812 = 2284 := by pc_by_len

@[simp] theorem pcI2014 : IPC 1813 = 2285 := by pc_by_len

@[simp] theorem pcI2015 : IPC 1812 = 2284 := by pc_by_len

@[simp] theorem pcI2016 : IPC 1815 = 2288 := by pc_by_len

@[simp] theorem pcI2017 : IPC 1816 = 2289 := by pc_by_len

@[simp] theorem pcI2018 : IPC 1812 = 2284 := by pc_by_len

@[simp] theorem pcI2032 : IPC 1821 = 2298 := by pc_by_len

@[simp] theorem pcI2033 : IPC 1823 = 2300 := by pc_by_len

@[simp] theorem pcI2034 : IPC 1824 = 2301 := by pc_by_len

@[simp] theorem pcI2035 : IPC 1825 = 2305 := by pc_by_len




@[simp] theorem pcI2039 : IPC 1812 = 2284 := by pc_by_len

@[simp] theorem pcI2040 : IPC 1812 = 2284 := by pc_by_len


@[simp] theorem pcI2042 : IPC 1835 = 2322 := by pc_by_len

@[simp] theorem pcI2043 : IPC 1838 = 2326 := by pc_by_len

@[simp] theorem pcI2044 : IPC 1842 = 2331 := by pc_by_len

@[simp] theorem pcI2045 : IPC 1843 = 2334 := by pc_by_len

@[simp] theorem pcI2046 : IPC 1844 = 2335 := by pc_by_len

@[simp] theorem pcI2047 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2048 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2049 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2050 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2051 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2052 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2053 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2054 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2055 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2056 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2057 : IPC 1846 = 2338 := by pc_by_len

@[simp] theorem pcI2093 : IPC 1861 = 2361 := by pc_by_len

@[simp] theorem pcI2094 : IPC 1862 = 2364 := by pc_by_len

@[simp] theorem pcI2095 : IPC 1863 = 2367 := by pc_by_len

@[simp] theorem pcI2156 : IPC 1941 = 2483 := by pc_by_len

@[simp] theorem pcI2200 : IPC 1996 = 2550 := by pc_by_len

@[simp] theorem pcI2201 : IPC 1999 = 2556 := by pc_by_len

@[simp] theorem pcI2202 : IPC 2010 = 2574 := by pc_by_len

@[simp] theorem pcI2203 : IPC 2010 = 2574 := by pc_by_len

@[simp] theorem pcI2204 : IPC 2011 = 2575 := by pc_by_len

@[simp] theorem pcI2205 : IPC 2013 = 2577 := by pc_by_len

@[simp] theorem pcI2206 : IPC 2013 = 2577 := by pc_by_len

@[simp] theorem pcI2207 : IPC 2015 = 2580 := by pc_by_len

@[simp] theorem pcI2208 : IPC 2016 = 2582 := by pc_by_len

@[simp] theorem pcI2209 : IPC 2018 = 2586 := by pc_by_len

@[simp] theorem pcI2210 : IPC 2018 = 2586 := by pc_by_len

@[simp] theorem pcI2211 : IPC 2020 = 2590 := by pc_by_len

@[simp] theorem pcI2212 : IPC 2020 = 2590 := by pc_by_len

@[simp] theorem pcI2213 : IPC 2022 = 2594 := by pc_by_len

@[simp] theorem pcI2214 : IPC 2022 = 2594 := by pc_by_len

@[simp] theorem pcI2215 : IPC 2024 = 2598 := by pc_by_len

@[simp] theorem pcI2216 : IPC 2024 = 2598 := by pc_by_len

@[simp] theorem pcI2217 : IPC 2026 = 2602 := by pc_by_len

@[simp] theorem pcI2218 : IPC 2026 = 2602 := by pc_by_len

@[simp] theorem pcI2219 : IPC 2028 = 2606 := by pc_by_len

@[simp] theorem pcI2220 : IPC 2028 = 2606 := by pc_by_len

@[simp] theorem pcI2221 : IPC 2030 = 2610 := by pc_by_len

@[simp] theorem pcI2222 : IPC 2030 = 2610 := by pc_by_len

@[simp] theorem pcI2223 : IPC 2032 = 2614 := by pc_by_len

@[simp] theorem pcI2224 : IPC 2032 = 2614 := by pc_by_len

@[simp] theorem pcI2225 : IPC 2034 = 2618 := by pc_by_len

@[simp] theorem pcI2226 : IPC 2034 = 2618 := by pc_by_len

@[simp] theorem pcI2330 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2332 : IPC 2122 = 2734 := by pc_by_len

@[simp] theorem pcI2333 : IPC 2123 = 2735 := by pc_by_len

@[simp] theorem pcI2334 : IPC 2124 = 2736 := by pc_by_len

@[simp] theorem pcI2335 : IPC 2125 = 2737 := by pc_by_len

@[simp] theorem pcI2336 : IPC 2126 = 2738 := by pc_by_len

@[simp] theorem pcI2337 : IPC 2127 = 2739 := by pc_by_len

@[simp] theorem pcI2338 : IPC 2128 = 2740 := by pc_by_len

@[simp] theorem pcI2339 : IPC 2129 = 2741 := by pc_by_len

@[simp] theorem pcI2340 : IPC 2130 = 2742 := by pc_by_len

@[simp] theorem pcI2341 : IPC 2131 = 2745 := by pc_by_len

@[simp] theorem pcI2342 : IPC 2132 = 2746 := by pc_by_len

@[simp] theorem pcI2343 : IPC 2133 = 2747 := by pc_by_len

@[simp] theorem pcI2344 : IPC 2134 = 2748 := by pc_by_len

@[simp] theorem pcI2345 : IPC 2135 = 2749 := by pc_by_len

@[simp] theorem pcI2346 : IPC 2136 = 2750 := by pc_by_len

@[simp] theorem pcI2347 : IPC 2137 = 2751 := by pc_by_len

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

@[simp] theorem pcI2360 : IPC 2138 = 2752 := by pc_by_len

@[simp] theorem pcI2361 : IPC 2139 = 2753 := by pc_by_len

@[simp] theorem pcI2362 : IPC 2140 = 2754 := by pc_by_len

@[simp] theorem pcI2363 : IPC 2141 = 2755 := by pc_by_len

@[simp] theorem pcI2364 : IPC 2142 = 2756 := by pc_by_len

@[simp] theorem pcI2365 : IPC 2143 = 2757 := by pc_by_len

@[simp] theorem pcI2366 : IPC 2144 = 2758 := by pc_by_len

@[simp] theorem pcI2367 : IPC 2145 = 2759 := by pc_by_len

@[simp] theorem pcI2368 : IPC 2146 = 2760 := by pc_by_len

@[simp] theorem pcI2369 : IPC 2147 = 2761 := by pc_by_len

@[simp] theorem pcI2370 : IPC 2148 = 2762 := by pc_by_len

@[simp] theorem pcI2371 : IPC 2149 = 2763 := by pc_by_len

@[simp] theorem pcI2372 : IPC 2150 = 2764 := by pc_by_len

@[simp] theorem pcI2373 : IPC 2151 = 2765 := by pc_by_len

@[simp] theorem pcI2374 : IPC 2152 = 2766 := by pc_by_len

@[simp] theorem pcI2375 : IPC 2153 = 2769 := by pc_by_len

@[simp] theorem pcI2376 : IPC 2154 = 2770 := by pc_by_len

@[simp] theorem pcI2377 : IPC 2155 = 2771 := by pc_by_len

@[simp] theorem pcI2378 : IPC 2156 = 2772 := by pc_by_len

@[simp] theorem pcI2379 : IPC 2157 = 2773 := by pc_by_len

@[simp] theorem pcI2380 : IPC 2158 = 2776 := by pc_by_len

@[simp] theorem pcI2381 : IPC 2159 = 2777 := by pc_by_len

@[simp] theorem pcI2382 : IPC 2160 = 2778 := by pc_by_len

@[simp] theorem pcI2383 : IPC 2161 = 2779 := by pc_by_len

@[simp] theorem pcI2384 : IPC 2162 = 2780 := by pc_by_len

@[simp] theorem pcI2385 : IPC 2163 = 2781 := by pc_by_len

@[simp] theorem pcI2386 : IPC 2164 = 2782 := by pc_by_len

@[simp] theorem pcI2387 : IPC 2165 = 2783 := by pc_by_len

@[simp] theorem pcI2388 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2389 : IPC 2166 = 2784 := by pc_by_len

@[simp] theorem pcI2390 : IPC 2167 = 2785 := by pc_by_len

@[simp] theorem pcI2391 : IPC 2168 = 2786 := by pc_by_len

@[simp] theorem pcI2392 : IPC 2169 = 2787 := by pc_by_len

@[simp] theorem pcI2393 : IPC 2170 = 2788 := by pc_by_len

@[simp] theorem pcI2394 : IPC 2171 = 2789 := by pc_by_len

@[simp] theorem pcI2395 : IPC 2172 = 2790 := by pc_by_len

@[simp] theorem pcI2396 : IPC 2173 = 2791 := by pc_by_len

@[simp] theorem pcI2397 : IPC 2174 = 2792 := by pc_by_len

@[simp] theorem pcI2398 : IPC 2175 = 2793 := by pc_by_len

@[simp] theorem pcI2399 : IPC 2176 = 2794 := by pc_by_len

@[simp] theorem pcI2400 : IPC 2177 = 2795 := by pc_by_len

@[simp] theorem pcI2401 : IPC 2178 = 2796 := by pc_by_len

@[simp] theorem pcI2402 : IPC 2179 = 2797 := by pc_by_len

@[simp] theorem pcI2403 : IPC 2180 = 2798 := by pc_by_len

@[simp] theorem pcI2404 : IPC 2181 = 2801 := by pc_by_len

@[simp] theorem pcI2405 : IPC 2182 = 2802 := by pc_by_len

@[simp] theorem pcI2406 : IPC 2183 = 2803 := by pc_by_len

@[simp] theorem pcI2407 : IPC 2184 = 2804 := by pc_by_len

@[simp] theorem pcI2408 : IPC 2185 = 2805 := by pc_by_len

@[simp] theorem pcI2409 : IPC 2186 = 2808 := by pc_by_len

@[simp] theorem pcI2410 : IPC 2187 = 2809 := by pc_by_len

@[simp] theorem pcI2411 : IPC 2188 = 2810 := by pc_by_len

@[simp] theorem pcI2412 : IPC 2189 = 2811 := by pc_by_len

@[simp] theorem pcI2413 : IPC 2190 = 2812 := by pc_by_len

@[simp] theorem pcI2414 : IPC 2191 = 2813 := by pc_by_len

@[simp] theorem pcI2415 : IPC 2192 = 2814 := by pc_by_len

@[simp] theorem pcI2416 : IPC 2193 = 2815 := by pc_by_len

@[simp] theorem pcI2417 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2418 : IPC 2194 = 2816 := by pc_by_len

@[simp] theorem pcI2419 : IPC 2195 = 2817 := by pc_by_len

@[simp] theorem pcI2420 : IPC 2196 = 2818 := by pc_by_len

@[simp] theorem pcI2421 : IPC 2197 = 2819 := by pc_by_len

@[simp] theorem pcI2422 : IPC 2198 = 2820 := by pc_by_len

@[simp] theorem pcI2423 : IPC 2199 = 2821 := by pc_by_len

@[simp] theorem pcI2424 : IPC 2200 = 2822 := by pc_by_len

@[simp] theorem pcI2425 : IPC 2201 = 2823 := by pc_by_len

@[simp] theorem pcI2426 : IPC 2202 = 2824 := by pc_by_len

@[simp] theorem pcI2432 : IPC 2208 = 2830 := by pc_by_len

@[simp] theorem pcI2433 : IPC 2209 = 2833 := by pc_by_len

@[simp] theorem pcI2434 : IPC 2210 = 2834 := by pc_by_len

@[simp] theorem pcI2435 : IPC 2211 = 2835 := by pc_by_len

@[simp] theorem pcI2436 : IPC 2212 = 2836 := by pc_by_len

@[simp] theorem pcI2437 : IPC 2213 = 2837 := by pc_by_len

@[simp] theorem pcI2438 : IPC 2214 = 2840 := by pc_by_len

@[simp] theorem pcI2439 : IPC 2215 = 2841 := by pc_by_len

@[simp] theorem pcI2440 : IPC 2216 = 2842 := by pc_by_len

@[simp] theorem pcI2441 : IPC 2217 = 2843 := by pc_by_len

@[simp] theorem pcI2442 : IPC 2218 = 2844 := by pc_by_len

@[simp] theorem pcI2443 : IPC 2219 = 2845 := by pc_by_len

@[simp] theorem pcI2444 : IPC 2220 = 2846 := by pc_by_len

@[simp] theorem pcI2445 : IPC 2221 = 2847 := by pc_by_len

@[simp] theorem pcI2446 : IPC 2222 = 2848 := by pc_by_len

@[simp] theorem pcI2447 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2448 : IPC 2223 = 2849 := by pc_by_len

@[simp] theorem pcI2449 : IPC 2224 = 2850 := by pc_by_len

@[simp] theorem pcI2450 : IPC 2225 = 2851 := by pc_by_len

@[simp] theorem pcI2451 : IPC 2226 = 2852 := by pc_by_len

@[simp] theorem pcI2452 : IPC 2227 = 2853 := by pc_by_len

@[simp] theorem pcI2453 : IPC 2228 = 2854 := by pc_by_len

@[simp] theorem pcI2454 : IPC 2229 = 2855 := by pc_by_len

@[simp] theorem pcI2455 : IPC 2230 = 2856 := by pc_by_len

@[simp] theorem pcI2456 : IPC 2231 = 2857 := by pc_by_len

@[simp] theorem pcI2457 : IPC 2232 = 2858 := by pc_by_len

@[simp] theorem pcI2458 : IPC 2233 = 2859 := by pc_by_len

@[simp] theorem pcI2459 : IPC 2234 = 2860 := by pc_by_len

@[simp] theorem pcI2460 : IPC 2235 = 2861 := by pc_by_len

@[simp] theorem pcI2461 : IPC 2236 = 2862 := by pc_by_len

@[simp] theorem pcI2462 : IPC 2237 = 2865 := by pc_by_len

@[simp] theorem pcI2463 : IPC 2238 = 2866 := by pc_by_len

@[simp] theorem pcI2464 : IPC 2239 = 2867 := by pc_by_len

@[simp] theorem pcI2465 : IPC 2240 = 2868 := by pc_by_len

@[simp] theorem pcI2466 : IPC 2241 = 2869 := by pc_by_len

@[simp] theorem pcI2467 : IPC 2242 = 2872 := by pc_by_len

@[simp] theorem pcI2468 : IPC 2243 = 2873 := by pc_by_len

@[simp] theorem pcI2469 : IPC 2244 = 2874 := by pc_by_len

@[simp] theorem pcI2470 : IPC 2245 = 2875 := by pc_by_len

@[simp] theorem pcI2471 : IPC 2246 = 2876 := by pc_by_len

@[simp] theorem pcI2472 : IPC 2247 = 2877 := by pc_by_len

@[simp] theorem pcI2473 : IPC 2248 = 2878 := by pc_by_len

@[simp] theorem pcI2474 : IPC 2249 = 2879 := by pc_by_len

@[simp] theorem pcI2475 : IPC 2250 = 2880 := by pc_by_len

@[simp] theorem pcI2476 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2477 : IPC 2251 = 2881 := by pc_by_len

@[simp] theorem pcI2478 : IPC 2252 = 2882 := by pc_by_len

@[simp] theorem pcI2479 : IPC 2253 = 2883 := by pc_by_len

@[simp] theorem pcI2480 : IPC 2254 = 2884 := by pc_by_len

@[simp] theorem pcI2481 : IPC 2255 = 2885 := by pc_by_len

@[simp] theorem pcI2482 : IPC 2256 = 2886 := by pc_by_len

@[simp] theorem pcI2483 : IPC 2257 = 2887 := by pc_by_len

@[simp] theorem pcI2484 : IPC 2258 = 2888 := by pc_by_len

@[simp] theorem pcI2485 : IPC 2259 = 2889 := by pc_by_len

@[simp] theorem pcI2486 : IPC 2260 = 2890 := by pc_by_len

@[simp] theorem pcI2487 : IPC 2261 = 2891 := by pc_by_len

@[simp] theorem pcI2488 : IPC 2262 = 2892 := by pc_by_len

@[simp] theorem pcI2489 : IPC 2263 = 2893 := by pc_by_len

@[simp] theorem pcI2490 : IPC 2264 = 2894 := by pc_by_len

@[simp] theorem pcI2492 : IPC 2265 = 2897 := by pc_by_len

@[simp] theorem pcI2493 : IPC 2266 = 2898 := by pc_by_len

@[simp] theorem pcI2494 : IPC 2267 = 2899 := by pc_by_len

@[simp] theorem pcI2495 : IPC 2268 = 2900 := by pc_by_len

@[simp] theorem pcI2496 : IPC 2269 = 2901 := by pc_by_len

@[simp] theorem pcI2497 : IPC 2270 = 2904 := by pc_by_len

@[simp] theorem pcI2498 : IPC 2271 = 2905 := by pc_by_len

@[simp] theorem pcI2499 : IPC 2272 = 2906 := by pc_by_len

@[simp] theorem pcI2500 : IPC 2273 = 2907 := by pc_by_len

@[simp] theorem pcI2501 : IPC 2274 = 2908 := by pc_by_len

@[simp] theorem pcI2502 : IPC 2275 = 2909 := by pc_by_len

@[simp] theorem pcI2503 : IPC 2276 = 2910 := by pc_by_len

@[simp] theorem pcI2504 : IPC 2277 = 2911 := by pc_by_len

@[simp] theorem pcI2505 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2506 : IPC 2278 = 2912 := by pc_by_len

@[simp] theorem pcI2507 : IPC 2279 = 2913 := by pc_by_len

@[simp] theorem pcI2508 : IPC 2280 = 2914 := by pc_by_len

@[simp] theorem pcI2509 : IPC 2281 = 2915 := by pc_by_len

@[simp] theorem pcI2510 : IPC 2282 = 2916 := by pc_by_len

@[simp] theorem pcI2511 : IPC 2283 = 2917 := by pc_by_len

@[simp] theorem pcI2514 : IPC 2286 = 2920 := by pc_by_len

@[simp] theorem pcI2519 : IPC 2291 = 2925 := by pc_by_len

@[simp] theorem pcI2520 : IPC 2292 = 2926 := by pc_by_len

@[simp] theorem pcI2521 : IPC 2293 = 2929 := by pc_by_len

@[simp] theorem pcI2559 : IPC 2331 = 2975 := by pc_by_len

@[simp] theorem pcI2560 : IPC 2332 = 2976 := by pc_by_len

@[simp] theorem pcI2561 : IPC 2333 = 2977 := by pc_by_len

@[simp] theorem pcI2562 : IPC 2334 = 2978 := by pc_by_len

@[simp] theorem pcI2563 : IPC 2335 = 2979 := by pc_by_len

@[simp] theorem pcI2564 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2565 : IPC 2336 = 2980 := by pc_by_len

@[simp] theorem pcI2566 : IPC 2337 = 2983 := by pc_by_len

@[simp] theorem pcI2585 : IPC 2342 = 2990 := by pc_by_len

/-! ## The straight-line negation and the inline Newton chain (negun, inl693) -/

@[simp] theorem negunPC0 (i : Nat) (hi : 1812 ≤ i) (hii : i ≤ 1820) :
    cachedArtifact.instructionPC i =
      ([2284,2285,2287,2288,2289,2290,2293,2294,2297] : List Nat)[i - 1812]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem negunPC1 (i : Nat) (hi : 1864 ≤ i) (hii : i ≤ 1910) :
    cachedArtifact.instructionPC i =
      ([2368,2369,2371,2372,2375,2376,2378,2379,2380,2381,2384,2385,2387,2388,2389,2392,2393,2395,2396,2397,2400,2401,2403,2404,2405,2408,2409,2411,2412,2413,2416,2417,2418,2420,2421,2422,2425,2426,2428,2429,2430,2433,2434,2435,2436,2437,2438] : List Nat)[i - 1864]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem negunPC2 (i : Nat) (hi : 1942 ≤ i) (hii : i ≤ 1985) :
    cachedArtifact.instructionPC i =
      ([2484,2485,2486,2487,2488,2490,2491,2493,2494,2495,2496,2497,2499,2500,2501,2502,2503,2504,2506,2507,2508,2509,2510,2511,2513,2514,2515,2516,2517,2518,2520,2521,2522,2523,2524,2525,2527,2528,2529,2530,2531,2532,2534,2535] : List Nat)[i - 1942]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

/-! ## Directly stated pcs: E5 and the eight-limb loop head (2056 .. 2146), the bottom test,
the exit / E3 phase blocks and the repair loop (2381 .. 2465), and the appended four-limb
loop head (8548 .. 8610). -/

@[simp] theorem pcDual2056 : IPC 2036 = 2622 := by pc_by_len

@[simp] theorem pcDual2057 : IPC 2011 = 2575 := by pc_by_len

@[simp] theorem pcDual2065 : IPC 2011 = 2575 := by pc_by_len

@[simp] theorem pcDual2066 : IPC 2011 = 2575 := by pc_by_len

@[simp] theorem pcDual2067 : IPC 2011 = 2575 := by pc_by_len

@[simp] theorem pcDual2068 : IPC 2036 = 2622 := by pc_by_len

@[simp] theorem pcDual2069 : IPC 1999 = 2556 := by pc_by_len

@[simp] theorem pcDual2070 : IPC 2003 = 2564 := by pc_by_len

@[simp] theorem pcDual2071 : IPC 2003 = 2564 := by pc_by_len

@[simp] theorem pcDual2072 : IPC 2005 = 2566 := by pc_by_len

@[simp] theorem pcDual2073 : IPC 2006 = 2567 := by pc_by_len

@[simp] theorem pcDual2074 : IPC 2007 = 2568 := by pc_by_len

@[simp] theorem pcDual2075 : IPC 2008 = 2570 := by pc_by_len

@[simp] theorem pcDual2076 : IPC 2008 = 2570 := by pc_by_len

@[simp] theorem pcDual2077 : IPC 2009 = 2571 := by pc_by_len

@[simp] theorem pcDual2078 : IPC 2010 = 2574 := by pc_by_len

@[simp] theorem pcDual2079 : IPC 2036 = 2622 := by pc_by_len

@[simp] theorem pcDual2080 : IPC 2036 = 2622 := by pc_by_len

@[simp] theorem pcDual2081 : IPC 2038 = 2626 := by pc_by_len

@[simp] theorem pcDual2082 : IPC 2039 = 2627 := by pc_by_len

@[simp] theorem pcDual2083 : IPC 2040 = 2628 := by pc_by_len

@[simp] theorem pcDual2084 : IPC 2040 = 2628 := by pc_by_len

@[simp] theorem pcDual2085 : IPC 2040 = 2628 := by pc_by_len

@[simp] theorem pcDual2086 : IPC 2040 = 2628 := by pc_by_len

@[simp] theorem pcDual2087 : IPC 2042 = 2632 := by pc_by_len

@[simp] theorem pcDual2088 : IPC 2068 = 2667 := by pc_by_len

@[simp] theorem pcDual2089 : IPC 2068 = 2667 := by pc_by_len

@[simp] theorem pcDual2090 : IPC 2068 = 2667 := by pc_by_len

@[simp] theorem pcDual2091 : IPC 2068 = 2667 := by pc_by_len

@[simp] theorem pcDual2092 : IPC 2069 = 2668 := by pc_by_len

@[simp] theorem pcDual2093 : IPC 2070 = 2669 := by pc_by_len

@[simp] theorem pcDual2094 : IPC 2071 = 2672 := by pc_by_len

@[simp] theorem pcDual2095 : IPC 2072 = 2675 := by pc_by_len

@[simp] theorem pcDual2096 : IPC 2073 = 2676 := by pc_by_len

@[simp] theorem pcDual2100 : IPC 2074 = 2679 := by pc_by_len

@[simp] theorem pcDual2101 : IPC 2075 = 2680 := by pc_by_len

@[simp] theorem pcDual2102 : IPC 2076 = 2681 := by pc_by_len

@[simp] theorem pcDual2103 : IPC 2077 = 2682 := by pc_by_len

@[simp] theorem pcDual2104 : IPC 2078 = 2683 := by pc_by_len

@[simp] theorem pcDual2105 : IPC 2079 = 2684 := by pc_by_len

@[simp] theorem pcDual2106 : IPC 2080 = 2687 := by pc_by_len

@[simp] theorem pcDual2107 : IPC 2081 = 2688 := by pc_by_len

@[simp] theorem pcDual2108 : IPC 2082 = 2689 := by pc_by_len

@[simp] theorem pcDual2109 : IPC 2083 = 2692 := by pc_by_len

@[simp] theorem pcDual2110 : IPC 2084 = 2693 := by pc_by_len

@[simp] theorem pcDual2111 : IPC 2085 = 2694 := by pc_by_len

@[simp] theorem pcDual2112 : IPC 2086 = 2695 := by pc_by_len

@[simp] theorem pcDual2113 : IPC 2087 = 2696 := by pc_by_len

@[simp] theorem pcDual2114 : IPC 2088 = 2697 := by pc_by_len

@[simp] theorem pcDual2115 : IPC 2089 = 2698 := by pc_by_len

@[simp] theorem pcDual2116 : IPC 2090 = 2699 := by pc_by_len

@[simp] theorem pcDual2117 : IPC 2091 = 2700 := by pc_by_len

@[simp] theorem pcDual2118 : IPC 2092 = 2701 := by pc_by_len

@[simp] theorem pcDual2119 : IPC 2093 = 2702 := by pc_by_len

@[simp] theorem pcDual2120 : IPC 2094 = 2703 := by pc_by_len

@[simp] theorem pcDual2121 : IPC 2095 = 2704 := by pc_by_len

@[simp] theorem pcDual2122 : IPC 2096 = 2705 := by pc_by_len

@[simp] theorem pcDual2123 : IPC 2097 = 2706 := by pc_by_len

@[simp] theorem pcDual2124 : IPC 2098 = 2707 := by pc_by_len

@[simp] theorem pcDual2125 : IPC 2099 = 2708 := by pc_by_len

@[simp] theorem pcDual2126 : IPC 2100 = 2709 := by pc_by_len

@[simp] theorem pcDual2127 : IPC 2101 = 2711 := by pc_by_len

@[simp] theorem pcDual2128 : IPC 2102 = 2712 := by pc_by_len

@[simp] theorem pcDual2129 : IPC 2103 = 2713 := by pc_by_len

@[simp] theorem pcDual2130 : IPC 2104 = 2714 := by pc_by_len

@[simp] theorem pcDual2131 : IPC 2105 = 2715 := by pc_by_len

@[simp] theorem pcDual2132 : IPC 2106 = 2716 := by pc_by_len

@[simp] theorem pcDual2133 : IPC 2107 = 2717 := by pc_by_len

@[simp] theorem pcDual2134 : IPC 2108 = 2720 := by pc_by_len

@[simp] theorem pcDual2135 : IPC 2109 = 2721 := by pc_by_len

@[simp] theorem pcDual2136 : IPC 2110 = 2722 := by pc_by_len

@[simp] theorem pcDual2137 : IPC 2111 = 2723 := by pc_by_len

@[simp] theorem pcDual2138 : IPC 2112 = 2724 := by pc_by_len

@[simp] theorem pcDual2139 : IPC 2114 = 2726 := by pc_by_len

@[simp] theorem pcDual2141 : IPC 2116 = 2728 := by pc_by_len

@[simp] theorem pcDual2142 : IPC 2117 = 2729 := by pc_by_len

@[simp] theorem pcDual2143 : IPC 2118 = 2730 := by pc_by_len

@[simp] theorem pcDual2144 : IPC 2119 = 2731 := by pc_by_len

@[simp] theorem pcDual2145 : IPC 2120 = 2732 := by pc_by_len

@[simp] theorem pcDual2146 : IPC 2121 = 2733 := by pc_by_len

@[simp] theorem pcDual2381 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pcDual2382 : IPC 2342 = 2990 := by pc_by_len

@[simp] theorem pcDual2383 : IPC 2345 = 2993 := by pc_by_len

@[simp] theorem pcDual2384 : IPC 2347 = 2995 := by pc_by_len

@[simp] theorem pcDual2385 : IPC 2348 = 2996 := by pc_by_len

@[simp] theorem pcDual2386 : IPC 2349 = 2997 := by pc_by_len

@[simp] theorem pcDual2387 : IPC 2350 = 2998 := by pc_by_len

@[simp] theorem pcDual2388 : IPC 2351 = 2999 := by pc_by_len

@[simp] theorem pcDual2389 : IPC 2351 = 2999 := by pc_by_len

@[simp] theorem pcDual2390 : IPC 2351 = 2999 := by pc_by_len

@[simp] theorem pcDual2391 : IPC 2352 = 3000 := by pc_by_len

@[simp] theorem pcDual2392 : IPC 2352 = 3000 := by pc_by_len

@[simp] theorem pcDual2393 : IPC 2352 = 3000 := by pc_by_len

@[simp] theorem pcDual2394 : IPC 2352 = 3000 := by pc_by_len

@[simp] theorem pcDual2395 : IPC 2354 = 3002 := by pc_by_len

@[simp] theorem pcDual2396 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2397 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2398 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2399 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2400 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2401 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2402 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2403 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2404 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2405 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2406 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2407 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2408 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2409 : IPC 8401 = 10741 := by pc_by_len

@[simp] theorem pcDual2410 : IPC 2354 = 3002 := by pc_by_len

@[simp] theorem pcDual2411 : IPC 2357 = 3007 := by pc_by_len

@[simp] theorem pcDual2412 : IPC 2358 = 3008 := by pc_by_len

@[simp] theorem pcDual2413 : IPC 2359 = 3009 := by pc_by_len

@[simp] theorem pcDual2414 : IPC 2360 = 3010 := by pc_by_len

@[simp] theorem pcDual2415 : IPC 2361 = 3013 := by pc_by_len

@[simp] theorem pcDual2416 : IPC 2362 = 3014 := by pc_by_len

@[simp] theorem pcDual2417 : IPC 2363 = 3015 := by pc_by_len

@[simp] theorem pcDual2418 : IPC 2364 = 3016 := by pc_by_len

@[simp] theorem pcDual2419 : IPC 2365 = 3017 := by pc_by_len

@[simp] theorem pcDual2420 : IPC 2366 = 3020 := by pc_by_len

@[simp] theorem pcDual2421 : IPC 2367 = 3021 := by pc_by_len

@[simp] theorem pcDual2422 : IPC 2368 = 3022 := by pc_by_len

@[simp] theorem pcDual2423 : IPC 2369 = 3023 := by pc_by_len

@[simp] theorem pcDual2424 : IPC 2370 = 3024 := by pc_by_len

@[simp] theorem pcDual2425 : IPC 2371 = 3025 := by pc_by_len

@[simp] theorem pcDual2426 : IPC 2372 = 3026 := by pc_by_len

@[simp] theorem pcDual2427 : IPC 2373 = 3027 := by pc_by_len

@[simp] theorem pcDual2428 : IPC 2374 = 3028 := by pc_by_len

@[simp] theorem pcDual2429 : IPC 2375 = 3029 := by pc_by_len

@[simp] theorem pcDual2430 : IPC 2376 = 3030 := by pc_by_len

@[simp] theorem pcDual2431 : IPC 2377 = 3031 := by pc_by_len

@[simp] theorem pcDual2432 : IPC 2378 = 3032 := by pc_by_len

@[simp] theorem pcDual2433 : IPC 2379 = 3033 := by pc_by_len

@[simp] theorem pcDual2434 : IPC 2380 = 3034 := by pc_by_len

@[simp] theorem pcDual2435 : IPC 2381 = 3035 := by pc_by_len

@[simp] theorem pcDual2436 : IPC 2382 = 3036 := by pc_by_len

@[simp] theorem pcDual2437 : IPC 2383 = 3037 := by pc_by_len

@[simp] theorem pcDual2438 : IPC 2384 = 3038 := by pc_by_len

@[simp] theorem pcDual2439 : IPC 2385 = 3040 := by pc_by_len

@[simp] theorem pcDual2440 : IPC 2386 = 3041 := by pc_by_len

@[simp] theorem pcDual2441 : IPC 2387 = 3042 := by pc_by_len

@[simp] theorem pcDual2442 : IPC 2388 = 3045 := by pc_by_len

@[simp] theorem pcDual2443 : IPC 2389 = 3046 := by pc_by_len

@[simp] theorem pcDual2444 : IPC 2390 = 3047 := by pc_by_len

@[simp] theorem pcDual2445 : IPC 2391 = 3050 := by pc_by_len

@[simp] theorem pcDual2446 : IPC 2392 = 3051 := by pc_by_len

@[simp] theorem pcDual2447 : IPC 2393 = 3052 := by pc_by_len

@[simp] theorem pcDual2448 : IPC 2394 = 3055 := by pc_by_len

@[simp] theorem pcDual2449 : IPC 2395 = 3056 := by pc_by_len

@[simp] theorem pcDual2450 : IPC 2396 = 3057 := by pc_by_len

@[simp] theorem pcDual2451 : IPC 2397 = 3058 := by pc_by_len

@[simp] theorem pcDual2452 : IPC 2398 = 3059 := by pc_by_len

@[simp] theorem pcDual2453 : IPC 2399 = 3062 := by pc_by_len

@[simp] theorem pcDual2454 : IPC 2400 = 3063 := by pc_by_len

@[simp] theorem pcDual2455 : IPC 2401 = 3064 := by pc_by_len

@[simp] theorem pcDual2456 : IPC 2402 = 3065 := by pc_by_len

@[simp] theorem pcDual2457 : IPC 2403 = 3068 := by pc_by_len

@[simp] theorem pcDual2458 : IPC 2404 = 3069 := by pc_by_len

@[simp] theorem pcDual2459 : IPC 2405 = 3072 := by pc_by_len

@[simp] theorem pcDual2460 : IPC 2408 = 3075 := by pc_by_len

@[simp] theorem pcDual2461 : IPC 2409 = 3078 := by pc_by_len

@[simp] theorem pcDual2462 : IPC 2409 = 3078 := by pc_by_len

@[simp] theorem pcDual2463 : IPC 2409 = 3078 := by pc_by_len

@[simp] theorem pcDual2464 : IPC 2409 = 3078 := by pc_by_len

@[simp] theorem pcDual2465 : IPC 2411 = 3080 := by pc_by_len

@[simp] theorem pcDual8548 : IPC 8228 = 10535 := by pc_by_len

@[simp] theorem pcDual8549 : IPC 8228 = 10535 := by pc_by_len

@[simp] theorem pcDual8550 : IPC 8228 = 10535 := by pc_by_len

@[simp] theorem pcDual8551 : IPC 8229 = 10536 := by pc_by_len

@[simp] theorem pcDual8552 : IPC 8230 = 10537 := by pc_by_len

@[simp] theorem pcDual8553 : IPC 8231 = 10540 := by pc_by_len

@[simp] theorem pcDual8554 : IPC 8232 = 10543 := by pc_by_len

@[simp] theorem pcDual8555 : IPC 8233 = 10544 := by pc_by_len

@[simp] theorem pcDual8559 : IPC 8234 = 10547 := by pc_by_len

@[simp] theorem pcDual8560 : IPC 8235 = 10548 := by pc_by_len

@[simp] theorem pcDual8561 : IPC 8236 = 10549 := by pc_by_len

@[simp] theorem pcDual8562 : IPC 8237 = 10550 := by pc_by_len

@[simp] theorem pcDual8563 : IPC 8238 = 10551 := by pc_by_len

@[simp] theorem pcDual8564 : IPC 8239 = 10552 := by pc_by_len

@[simp] theorem pcDual8565 : IPC 8240 = 10555 := by pc_by_len

@[simp] theorem pcDual8566 : IPC 8241 = 10556 := by pc_by_len

@[simp] theorem pcDual8567 : IPC 8242 = 10557 := by pc_by_len

@[simp] theorem pcDual8568 : IPC 8243 = 10560 := by pc_by_len

@[simp] theorem pcDual8569 : IPC 8244 = 10561 := by pc_by_len

@[simp] theorem pcDual8570 : IPC 8245 = 10562 := by pc_by_len

@[simp] theorem pcDual8571 : IPC 8246 = 10563 := by pc_by_len

@[simp] theorem pcDual8572 : IPC 8247 = 10564 := by pc_by_len

@[simp] theorem pcDual8573 : IPC 8248 = 10565 := by pc_by_len

@[simp] theorem pcDual8574 : IPC 8249 = 10566 := by pc_by_len

@[simp] theorem pcDual8575 : IPC 8250 = 10567 := by pc_by_len

@[simp] theorem pcDual8576 : IPC 8251 = 10568 := by pc_by_len

@[simp] theorem pcDual8577 : IPC 8252 = 10569 := by pc_by_len

@[simp] theorem pcDual8578 : IPC 8253 = 10570 := by pc_by_len

@[simp] theorem pcDual8579 : IPC 8254 = 10571 := by pc_by_len

@[simp] theorem pcDual8580 : IPC 8255 = 10572 := by pc_by_len

@[simp] theorem pcDual8581 : IPC 8256 = 10573 := by pc_by_len

@[simp] theorem pcDual8582 : IPC 8257 = 10574 := by pc_by_len

@[simp] theorem pcDual8583 : IPC 8258 = 10575 := by pc_by_len

@[simp] theorem pcDual8584 : IPC 8259 = 10576 := by pc_by_len

@[simp] theorem pcDual8585 : IPC 8260 = 10577 := by pc_by_len

@[simp] theorem pcDual8586 : IPC 8261 = 10579 := by pc_by_len

@[simp] theorem pcDual8587 : IPC 8262 = 10580 := by pc_by_len

@[simp] theorem pcDual8588 : IPC 8263 = 10581 := by pc_by_len

@[simp] theorem pcDual8589 : IPC 8264 = 10582 := by pc_by_len

@[simp] theorem pcDual8590 : IPC 8265 = 10583 := by pc_by_len

@[simp] theorem pcDual8591 : IPC 8266 = 10584 := by pc_by_len

@[simp] theorem pcDual8592 : IPC 8267 = 10585 := by pc_by_len

@[simp] theorem pcDual8593 : IPC 8268 = 10588 := by pc_by_len

@[simp] theorem pcDual8594 : IPC 8269 = 10589 := by pc_by_len

@[simp] theorem pcDual8595 : IPC 8270 = 10590 := by pc_by_len

@[simp] theorem pcDual8596 : IPC 8271 = 10591 := by pc_by_len

@[simp] theorem pcDual8597 : IPC 8272 = 10592 := by pc_by_len

@[simp] theorem pcDual8598 : IPC 8274 = 10594 := by pc_by_len

@[simp] theorem pcDual8600 : IPC 8276 = 10596 := by pc_by_len

@[simp] theorem pcDual8601 : IPC 8277 = 10597 := by pc_by_len

@[simp] theorem pcDual8602 : IPC 8278 = 10598 := by pc_by_len

@[simp] theorem pcDual8603 : IPC 8279 = 10599 := by pc_by_len

@[simp] theorem pcDual8604 : IPC 8280 = 10600 := by pc_by_len

@[simp] theorem pcDual8605 : IPC 8281 = 10601 := by pc_by_len

@[simp] theorem pcDual8606 : IPC 8282 = 10602 := by pc_by_len

@[simp] theorem pcDual8607 : IPC 8283 = 10603 := by pc_by_len

@[simp] theorem pcDual8608 : IPC 8284 = 10604 := by pc_by_len

@[simp] theorem pcDual8609 : IPC 8285 = 10605 := by pc_by_len

@[simp] theorem pcDual8610 : IPC 8286 = 10606 := by pc_by_len

@[simp] theorem pcDual8611 : IPC 8287 = 10607 := by pc_by_len

@[simp] theorem pcDual8612 : IPC 8288 = 10608 := by pc_by_len

@[simp] theorem pcDual8613 : IPC 8289 = 10609 := by pc_by_len

@[simp] theorem pcDual8614 : IPC 8290 = 10610 := by pc_by_len

@[simp] theorem pcDual8615 : IPC 8291 = 10613 := by pc_by_len

@[simp] theorem pcDual8616 : IPC 8292 = 10614 := by pc_by_len

@[simp] theorem pcDual8617 : IPC 8293 = 10615 := by pc_by_len

@[simp] theorem pcDual8618 : IPC 8294 = 10616 := by pc_by_len

@[simp] theorem pcDual8619 : IPC 8295 = 10617 := by pc_by_len

@[simp] theorem pcDual8620 : IPC 8296 = 10618 := by pc_by_len

@[simp] theorem pcDual8621 : IPC 8297 = 10619 := by pc_by_len

@[simp] theorem pcDual8622 : IPC 8298 = 10620 := by pc_by_len

@[simp] theorem pcDual8623 : IPC 8299 = 10621 := by pc_by_len

@[simp] theorem pcDual8624 : IPC 8300 = 10622 := by pc_by_len

@[simp] theorem pcDual8625 : IPC 8301 = 10623 := by pc_by_len

@[simp] theorem pcDual8626 : IPC 8302 = 10624 := by pc_by_len

@[simp] theorem pcDual8627 : IPC 8303 = 10625 := by pc_by_len

@[simp] theorem pcDual8628 : IPC 8304 = 10626 := by pc_by_len

@[simp] theorem pcDual8629 : IPC 8305 = 10627 := by pc_by_len

@[simp] theorem pcDual8630 : IPC 8306 = 10628 := by pc_by_len

@[simp] theorem pcDual8631 : IPC 8307 = 10629 := by pc_by_len

@[simp] theorem pcDual8632 : IPC 8308 = 10630 := by pc_by_len

@[simp] theorem pcDual8633 : IPC 8309 = 10631 := by pc_by_len

@[simp] theorem pcDual8634 : IPC 8310 = 10632 := by pc_by_len

@[simp] theorem pcDual8635 : IPC 8311 = 10633 := by pc_by_len

@[simp] theorem pcDual8636 : IPC 8312 = 10634 := by pc_by_len

@[simp] theorem pcDual8637 : IPC 8313 = 10637 := by pc_by_len

@[simp] theorem pcDual8638 : IPC 8314 = 10638 := by pc_by_len

@[simp] theorem pcDual8639 : IPC 8315 = 10639 := by pc_by_len

@[simp] theorem pcDual8640 : IPC 8316 = 10640 := by pc_by_len

@[simp] theorem pcDual8641 : IPC 8317 = 10641 := by pc_by_len

@[simp] theorem pcDual8642 : IPC 8318 = 10644 := by pc_by_len

@[simp] theorem pcDual8643 : IPC 8319 = 10645 := by pc_by_len

@[simp] theorem pcDual8644 : IPC 8320 = 10646 := by pc_by_len

@[simp] theorem pcDual8645 : IPC 8321 = 10647 := by pc_by_len

@[simp] theorem pcDual8646 : IPC 8322 = 10648 := by pc_by_len

@[simp] theorem pcDual8647 : IPC 8323 = 10649 := by pc_by_len

@[simp] theorem pcDual8648 : IPC 8324 = 10650 := by pc_by_len

@[simp] theorem pcDual8649 : IPC 8325 = 10651 := by pc_by_len

@[simp] theorem pcDual8650 : IPC 8326 = 10652 := by pc_by_len

@[simp] theorem pcDual8651 : IPC 8327 = 10653 := by pc_by_len

@[simp] theorem pcDual8652 : IPC 8328 = 10654 := by pc_by_len

@[simp] theorem pcDual8653 : IPC 8329 = 10655 := by pc_by_len

@[simp] theorem pcDual8654 : IPC 8330 = 10656 := by pc_by_len

@[simp] theorem pcDual8655 : IPC 8331 = 10657 := by pc_by_len

@[simp] theorem pcDual8656 : IPC 8332 = 10658 := by pc_by_len

@[simp] theorem pcDual8657 : IPC 8333 = 10659 := by pc_by_len

@[simp] theorem pcDual8658 : IPC 8334 = 10660 := by pc_by_len

@[simp] theorem pcDual8659 : IPC 8335 = 10661 := by pc_by_len

@[simp] theorem pcDual8660 : IPC 8336 = 10662 := by pc_by_len

@[simp] theorem pcDual8661 : IPC 8337 = 10663 := by pc_by_len

@[simp] theorem pcDual8662 : IPC 8338 = 10664 := by pc_by_len

@[simp] theorem pcDual8663 : IPC 8339 = 10665 := by pc_by_len

@[simp] theorem pcDual8664 : IPC 8340 = 10666 := by pc_by_len

@[simp] theorem pcDual8665 : IPC 8341 = 10669 := by pc_by_len

@[simp] theorem pcDual8666 : IPC 8342 = 10670 := by pc_by_len

@[simp] theorem pcDual8667 : IPC 8343 = 10671 := by pc_by_len

@[simp] theorem pcDual8668 : IPC 8344 = 10672 := by pc_by_len

@[simp] theorem pcDual8669 : IPC 8345 = 10673 := by pc_by_len

@[simp] theorem pcDual8670 : IPC 8346 = 10676 := by pc_by_len

@[simp] theorem pcDual8671 : IPC 8347 = 10677 := by pc_by_len

@[simp] theorem pcDual8672 : IPC 8348 = 10678 := by pc_by_len

@[simp] theorem pcDual8673 : IPC 8349 = 10679 := by pc_by_len

@[simp] theorem pcDual8674 : IPC 8350 = 10680 := by pc_by_len

@[simp] theorem pcDual8675 : IPC 8351 = 10681 := by pc_by_len

@[simp] theorem pcDual8676 : IPC 8352 = 10682 := by pc_by_len

@[simp] theorem pcDual8677 : IPC 8353 = 10683 := by pc_by_len

@[simp] theorem pcDual8678 : IPC 8354 = 10684 := by pc_by_len

@[simp] theorem pcDual8679 : IPC 8355 = 10687 := by pc_by_len

@[simp] theorem pcDual8680 : IPC 8356 = 10688 := by pc_by_len

@[simp] theorem pcDual8681 : IPC 8357 = 10689 := by pc_by_len

@[simp] theorem pcDual8682 : IPC 8358 = 10690 := by pc_by_len

@[simp] theorem pcDual8683 : IPC 8359 = 10691 := by pc_by_len

@[simp] theorem pcDual8684 : IPC 8360 = 10692 := by pc_by_len

@[simp] theorem pcDual8685 : IPC 8361 = 10693 := by pc_by_len

@[simp] theorem pcDual8686 : IPC 8362 = 10694 := by pc_by_len

@[simp] theorem pcDual8687 : IPC 8363 = 10695 := by pc_by_len

@[simp] theorem pcDual8688 : IPC 8364 = 10696 := by pc_by_len

@[simp] theorem pcDual8689 : IPC 8365 = 10697 := by pc_by_len

@[simp] theorem pcDual8690 : IPC 8366 = 10698 := by pc_by_len

@[simp] theorem pcDual8691 : IPC 8367 = 10699 := by pc_by_len

@[simp] theorem pcDual8692 : IPC 8368 = 10700 := by pc_by_len

@[simp] theorem pcDual8693 : IPC 8369 = 10701 := by pc_by_len

@[simp] theorem pcDual8694 : IPC 8370 = 10702 := by pc_by_len

@[simp] theorem pcDual8695 : IPC 8371 = 10705 := by pc_by_len

@[simp] theorem pcDual8696 : IPC 8372 = 10706 := by pc_by_len

@[simp] theorem pcDual8697 : IPC 8373 = 10707 := by pc_by_len

@[simp] theorem pcDual8698 : IPC 8374 = 10708 := by pc_by_len

@[simp] theorem pcDual8699 : IPC 8375 = 10709 := by pc_by_len

@[simp] theorem pcDual8700 : IPC 8376 = 10712 := by pc_by_len

@[simp] theorem pcDual8701 : IPC 8377 = 10713 := by pc_by_len

@[simp] theorem pcDual8702 : IPC 8378 = 10714 := by pc_by_len

@[simp] theorem pcDual8703 : IPC 8379 = 10715 := by pc_by_len

@[simp] theorem pcDual8704 : IPC 8380 = 10716 := by pc_by_len

@[simp] theorem pcDual8705 : IPC 8381 = 10717 := by pc_by_len

@[simp] theorem pcDual8706 : IPC 8382 = 10718 := by pc_by_len

@[simp] theorem pcDual8707 : IPC 8383 = 10719 := by pc_by_len

@[simp] theorem pcDual8708 : IPC 8384 = 10720 := by pc_by_len

@[simp] theorem pcDual8709 : IPC 8385 = 10723 := by pc_by_len

@[simp] theorem pcDual8710 : IPC 8386 = 10724 := by pc_by_len

@[simp] theorem pcDual8711 : IPC 8387 = 10725 := by pc_by_len

@[simp] theorem pcDual8712 : IPC 8388 = 10726 := by pc_by_len

@[simp] theorem pcDual8713 : IPC 8389 = 10727 := by pc_by_len

@[simp] theorem pcDual8714 : IPC 8390 = 10730 := by pc_by_len

@[simp] theorem pcDual8715 : IPC 8390 = 10730 := by pc_by_len

@[simp] theorem pcDual8716 : IPC 8396 = 10736 := by pc_by_len

@[simp] theorem pcDual8717 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8718 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8719 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8720 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8721 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8722 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8723 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8724 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8725 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8726 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8727 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8728 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8729 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8730 : IPC 8394 = 10734 := by pc_by_len

@[simp] theorem pcDual8731 : IPC 8395 = 10735 := by pc_by_len

@[simp] theorem pcDual8732 : IPC 8396 = 10736 := by pc_by_len

@[simp] theorem pcDual8733 : IPC 8397 = 10737 := by pc_by_len

@[simp] theorem pcDual8734 : IPC 8398 = 10738 := by pc_by_len

@[simp] theorem pcDual8735 : IPC 8399 = 10739 := by pc_by_len

@[simp] theorem restoredGeneralPC2339 : cachedArtifact.instructionPC 2336 = 2980 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2340 : cachedArtifact.instructionPC 2337 = 2983 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2341 : cachedArtifact.instructionPC 2338 = 2984 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2342 : cachedArtifact.instructionPC 2339 = 2985 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2343 : cachedArtifact.instructionPC 2340 = 2986 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2344 : cachedArtifact.instructionPC 2341 = 2987 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2345 : cachedArtifact.instructionPC 2342 = 2990 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2346 : cachedArtifact.instructionPC 2342 = 2990 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2347 : cachedArtifact.instructionPC 2342 = 2990 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2348 : cachedArtifact.instructionPC 2343 = 2991 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2349 : cachedArtifact.instructionPC 2344 = 2992 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2350 : cachedArtifact.instructionPC 2345 = 2993 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2351 : cachedArtifact.instructionPC 2346 = 2994 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2352 : cachedArtifact.instructionPC 2347 = 2995 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2353 : cachedArtifact.instructionPC 2348 = 2996 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2354 : cachedArtifact.instructionPC 2349 = 2997 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2355 : cachedArtifact.instructionPC 2350 = 2998 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2356 : cachedArtifact.instructionPC 2347 = 2995 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2412 : cachedArtifact.instructionPC 2404 = 3069 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2413 : cachedArtifact.instructionPC 2405 = 3072 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2414 : cachedArtifact.instructionPC 2406 = 3073 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2415 : cachedArtifact.instructionPC 2407 = 3074 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2416 : cachedArtifact.instructionPC 2408 = 3075 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2417 : cachedArtifact.instructionPC 2409 = 3078 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem lazyTopPC2339 : cachedArtifact.instructionPC 2336 = 2980 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2340 : cachedArtifact.instructionPC 2337 = 2983 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2341 : cachedArtifact.instructionPC 2338 = 2984 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2342 : cachedArtifact.instructionPC 2339 = 2985 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2343 : cachedArtifact.instructionPC 2340 = 2986 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2344 : cachedArtifact.instructionPC 2341 = 2987 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2345 : cachedArtifact.instructionPC 2342 = 2990 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2346 : cachedArtifact.instructionPC 2343 = 2991 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2347 : cachedArtifact.instructionPC 2344 = 2992 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2348 : cachedArtifact.instructionPC 2345 = 2993 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2349 : cachedArtifact.instructionPC 2346 = 2994 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2350 : cachedArtifact.instructionPC 2347 = 2995 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2351 : cachedArtifact.instructionPC 2348 = 2996 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2352 : cachedArtifact.instructionPC 2349 = 2997 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2353 : cachedArtifact.instructionPC 2350 = 2998 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2354 : cachedArtifact.instructionPC 2347 = 2995 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2355 : cachedArtifact.instructionPC 2351 = 2999 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2451 : cachedArtifact.instructionPC 2448 = 3136 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2452 : cachedArtifact.instructionPC 2448 = 3136 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2453 : cachedArtifact.instructionPC 2448 = 3136 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2454 : cachedArtifact.instructionPC 2448 = 3136 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2455 : cachedArtifact.instructionPC 2448 = 3136 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8399 : cachedArtifact.instructionPC 8384 = 10720 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8400 : cachedArtifact.instructionPC 8385 = 10723 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8401 : cachedArtifact.instructionPC 8386 = 10724 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8402 : cachedArtifact.instructionPC 8387 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8403 : cachedArtifact.instructionPC 8388 = 10726 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8404 : cachedArtifact.instructionPC 8389 = 10727 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8405 : cachedArtifact.instructionPC 8390 = 10730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8406 : cachedArtifact.instructionPC 8392 = 10732 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8407 : cachedArtifact.instructionPC 8394 = 10734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8408 : cachedArtifact.instructionPC 8395 = 10735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8409 : cachedArtifact.instructionPC 8396 = 10736 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8410 : cachedArtifact.instructionPC 8397 = 10737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8411 : cachedArtifact.instructionPC 8398 = 10738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8412 : cachedArtifact.instructionPC 8399 = 10739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8413 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8414 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8415 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8416 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8417 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8418 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8419 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8420 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8421 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8422 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8423 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8424 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8425 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8426 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8427 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8428 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8429 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8430 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8431 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8432 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8433 : cachedArtifact.instructionPC 8401 = 10741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem inlineRepairPC2361 : cachedArtifact.instructionPC 2354 = 3002 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2362 : cachedArtifact.instructionPC 2355 = 3003 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2363 : cachedArtifact.instructionPC 2356 = 3006 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2364 : cachedArtifact.instructionPC 2357 = 3007 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2365 : cachedArtifact.instructionPC 2358 = 3008 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2366 : cachedArtifact.instructionPC 2359 = 3009 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2367 : cachedArtifact.instructionPC 2360 = 3010 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2368 : cachedArtifact.instructionPC 2361 = 3013 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2369 : cachedArtifact.instructionPC 2362 = 3014 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2370 : cachedArtifact.instructionPC 2363 = 3015 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2371 : cachedArtifact.instructionPC 2364 = 3016 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2372 : cachedArtifact.instructionPC 2365 = 3017 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2373 : cachedArtifact.instructionPC 2366 = 3020 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2374 : cachedArtifact.instructionPC 2367 = 3021 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2375 : cachedArtifact.instructionPC 2368 = 3022 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2376 : cachedArtifact.instructionPC 2369 = 3023 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2377 : cachedArtifact.instructionPC 2370 = 3024 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2378 : cachedArtifact.instructionPC 2371 = 3025 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2379 : cachedArtifact.instructionPC 2372 = 3026 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2380 : cachedArtifact.instructionPC 2373 = 3027 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2381 : cachedArtifact.instructionPC 2374 = 3028 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2382 : cachedArtifact.instructionPC 2375 = 3029 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2383 : cachedArtifact.instructionPC 2376 = 3030 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2384 : cachedArtifact.instructionPC 2377 = 3031 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2385 : cachedArtifact.instructionPC 2378 = 3032 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2386 : cachedArtifact.instructionPC 2379 = 3033 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2387 : cachedArtifact.instructionPC 2380 = 3034 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2388 : cachedArtifact.instructionPC 2381 = 3035 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2389 : cachedArtifact.instructionPC 2382 = 3036 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2390 : cachedArtifact.instructionPC 2383 = 3037 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2391 : cachedArtifact.instructionPC 2384 = 3038 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2392 : cachedArtifact.instructionPC 2385 = 3040 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2393 : cachedArtifact.instructionPC 2386 = 3041 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2394 : cachedArtifact.instructionPC 2387 = 3042 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2395 : cachedArtifact.instructionPC 2388 = 3045 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2396 : cachedArtifact.instructionPC 2389 = 3046 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2397 : cachedArtifact.instructionPC 2390 = 3047 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2398 : cachedArtifact.instructionPC 2391 = 3050 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2399 : cachedArtifact.instructionPC 2392 = 3051 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2400 : cachedArtifact.instructionPC 2393 = 3052 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2401 : cachedArtifact.instructionPC 2394 = 3055 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2402 : cachedArtifact.instructionPC 2395 = 3056 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2403 : cachedArtifact.instructionPC 2396 = 3057 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2404 : cachedArtifact.instructionPC 2397 = 3058 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2405 : cachedArtifact.instructionPC 2398 = 3059 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2406 : cachedArtifact.instructionPC 2399 = 3062 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2407 : cachedArtifact.instructionPC 2400 = 3063 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2408 : cachedArtifact.instructionPC 2401 = 3064 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2409 : cachedArtifact.instructionPC 2402 = 3065 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2410 : cachedArtifact.instructionPC 2403 = 3068 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2411 : cachedArtifact.instructionPC 2404 = 3069 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2412 : cachedArtifact.instructionPC 2405 = 3072 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2413 : cachedArtifact.instructionPC 2406 = 3073 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2414 : cachedArtifact.instructionPC 2407 = 3074 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2415 : cachedArtifact.instructionPC 2408 = 3075 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2416 : cachedArtifact.instructionPC 2409 = 3078 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2417 : cachedArtifact.instructionPC 2410 = 3079 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2418 : cachedArtifact.instructionPC 2411 = 3080 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem directInitialPC2009 : cachedArtifact.instructionPC 1986 = 2536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2010 : cachedArtifact.instructionPC 1987 = 2537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2011 : cachedArtifact.instructionPC 1988 = 2538 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2012 : cachedArtifact.instructionPC 1989 = 2539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2013 : cachedArtifact.instructionPC 1990 = 2542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2014 : cachedArtifact.instructionPC 1991 = 2543 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2015 : cachedArtifact.instructionPC 1992 = 2544 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2016 : cachedArtifact.instructionPC 1993 = 2545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2017 : cachedArtifact.instructionPC 1994 = 2546 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2018 : cachedArtifact.instructionPC 1995 = 2549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2019 : cachedArtifact.instructionPC 1996 = 2550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2020 : cachedArtifact.instructionPC 1997 = 2553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2021 : cachedArtifact.instructionPC 1998 = 2554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2022 : cachedArtifact.instructionPC 1999 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2023 : cachedArtifact.instructionPC 2002 = 2561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2024 : cachedArtifact.instructionPC 2003 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2025 : cachedArtifact.instructionPC 2004 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2026 : cachedArtifact.instructionPC 2005 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2027 : cachedArtifact.instructionPC 2006 = 2567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2028 : cachedArtifact.instructionPC 2007 = 2568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2029 : cachedArtifact.instructionPC 2008 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2030 : cachedArtifact.instructionPC 2008 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2031 : cachedArtifact.instructionPC 2009 = 2571 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2032 : cachedArtifact.instructionPC 2010 = 2574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2033 : cachedArtifact.instructionPC 2011 = 2575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2034 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2035 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2036 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2037 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2038 : cachedArtifact.instructionPC 2015 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2039 : cachedArtifact.instructionPC 2016 = 2582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2040 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2041 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2042 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2043 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2044 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2045 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2046 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2047 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2048 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2049 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2050 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2051 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2052 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2053 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2054 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2055 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2056 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2057 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2058 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2059 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

@[simp] theorem directWordInitPC2009 : cachedArtifact.instructionPC 1986 = 2536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2010 : cachedArtifact.instructionPC 1987 = 2537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2011 : cachedArtifact.instructionPC 1988 = 2538 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2012 : cachedArtifact.instructionPC 1989 = 2539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2013 : cachedArtifact.instructionPC 1990 = 2542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2014 : cachedArtifact.instructionPC 1991 = 2543 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2015 : cachedArtifact.instructionPC 1992 = 2544 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2016 : cachedArtifact.instructionPC 1993 = 2545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2017 : cachedArtifact.instructionPC 1994 = 2546 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2018 : cachedArtifact.instructionPC 1995 = 2549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2019 : cachedArtifact.instructionPC 1996 = 2550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2020 : cachedArtifact.instructionPC 1997 = 2553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2021 : cachedArtifact.instructionPC 1998 = 2554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2022 : cachedArtifact.instructionPC 1999 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2023 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2024 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2025 : cachedArtifact.instructionPC 2001 = 2560 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2026 : cachedArtifact.instructionPC 2002 = 2561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2027 : cachedArtifact.instructionPC 2003 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2028 : cachedArtifact.instructionPC 2004 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2029 : cachedArtifact.instructionPC 2005 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2030 : cachedArtifact.instructionPC 2006 = 2567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2031 : cachedArtifact.instructionPC 2007 = 2568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2032 : cachedArtifact.instructionPC 2008 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2033 : cachedArtifact.instructionPC 2009 = 2571 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2034 : cachedArtifact.instructionPC 2010 = 2574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2035 : cachedArtifact.instructionPC 2011 = 2575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2036 : cachedArtifact.instructionPC 2012 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2037 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2038 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2039 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2040 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2041 : cachedArtifact.instructionPC 2015 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2042 : cachedArtifact.instructionPC 2016 = 2582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2043 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2044 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2045 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2046 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2047 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2048 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2049 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2050 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2051 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2052 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2053 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2054 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2055 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2056 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2057 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2058 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2059 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2060 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2061 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2062 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2009 : cachedArtifact.instructionPC 1986 = 2536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2010 : cachedArtifact.instructionPC 1987 = 2537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2011 : cachedArtifact.instructionPC 1988 = 2538 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2012 : cachedArtifact.instructionPC 1989 = 2539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2013 : cachedArtifact.instructionPC 1990 = 2542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2014 : cachedArtifact.instructionPC 1991 = 2543 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2015 : cachedArtifact.instructionPC 1992 = 2544 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2016 : cachedArtifact.instructionPC 1993 = 2545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2017 : cachedArtifact.instructionPC 1994 = 2546 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2018 : cachedArtifact.instructionPC 1995 = 2549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2019 : cachedArtifact.instructionPC 1996 = 2550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2020 : cachedArtifact.instructionPC 1996 = 2550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2021 : cachedArtifact.instructionPC 1997 = 2553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2022 : cachedArtifact.instructionPC 1998 = 2554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2023 : cachedArtifact.instructionPC 1999 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2024 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2025 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2026 : cachedArtifact.instructionPC 2001 = 2560 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2027 : cachedArtifact.instructionPC 2002 = 2561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2028 : cachedArtifact.instructionPC 2003 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2029 : cachedArtifact.instructionPC 2004 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2030 : cachedArtifact.instructionPC 2005 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2031 : cachedArtifact.instructionPC 2006 = 2567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2032 : cachedArtifact.instructionPC 2007 = 2568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2033 : cachedArtifact.instructionPC 2008 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2034 : cachedArtifact.instructionPC 2009 = 2571 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2035 : cachedArtifact.instructionPC 2010 = 2574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2036 : cachedArtifact.instructionPC 2011 = 2575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2037 : cachedArtifact.instructionPC 2012 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2038 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2039 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2040 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2041 : cachedArtifact.instructionPC 2015 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2042 : cachedArtifact.instructionPC 2016 = 2582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2043 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2044 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2045 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2046 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2047 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2048 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2049 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2050 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2051 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2052 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2053 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2054 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2055 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2056 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2057 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2058 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2059 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2060 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2061 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2062 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2063 : cachedArtifact.instructionPC 2037 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2064 : cachedArtifact.instructionPC 2038 = 2626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2065 : cachedArtifact.instructionPC 2038 = 2626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2009 : cachedArtifact.instructionPC 1986 = 2536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2010 : cachedArtifact.instructionPC 1987 = 2537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2011 : cachedArtifact.instructionPC 1988 = 2538 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2012 : cachedArtifact.instructionPC 1989 = 2539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2013 : cachedArtifact.instructionPC 1990 = 2542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2014 : cachedArtifact.instructionPC 1991 = 2543 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2015 : cachedArtifact.instructionPC 1992 = 2544 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2016 : cachedArtifact.instructionPC 1993 = 2545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2017 : cachedArtifact.instructionPC 1994 = 2546 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2018 : cachedArtifact.instructionPC 1995 = 2549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2019 : cachedArtifact.instructionPC 1996 = 2550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2020 : cachedArtifact.instructionPC 1997 = 2553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2021 : cachedArtifact.instructionPC 1998 = 2554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2022 : cachedArtifact.instructionPC 1999 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2023 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2024 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2025 : cachedArtifact.instructionPC 2001 = 2560 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2026 : cachedArtifact.instructionPC 2002 = 2561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2027 : cachedArtifact.instructionPC 2003 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2028 : cachedArtifact.instructionPC 2004 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2029 : cachedArtifact.instructionPC 2005 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2030 : cachedArtifact.instructionPC 2006 = 2567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2031 : cachedArtifact.instructionPC 2007 = 2568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2032 : cachedArtifact.instructionPC 2008 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2033 : cachedArtifact.instructionPC 2009 = 2571 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2034 : cachedArtifact.instructionPC 2010 = 2574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2035 : cachedArtifact.instructionPC 2011 = 2575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2036 : cachedArtifact.instructionPC 2012 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2037 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2038 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2039 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2040 : cachedArtifact.instructionPC 2015 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2041 : cachedArtifact.instructionPC 2016 = 2582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2042 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2043 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2044 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2045 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2046 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2047 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2048 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2049 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2050 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2051 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2052 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2053 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2054 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2055 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2056 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2057 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2058 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2059 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2060 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2061 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2062 : cachedArtifact.instructionPC 2037 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2063 : cachedArtifact.instructionPC 2038 = 2626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2064 : cachedArtifact.instructionPC 2038 = 2626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2009 : cachedArtifact.instructionPC 1986 = 2536 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2010 : cachedArtifact.instructionPC 1987 = 2537 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2011 : cachedArtifact.instructionPC 1988 = 2538 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2012 : cachedArtifact.instructionPC 1989 = 2539 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2013 : cachedArtifact.instructionPC 1990 = 2542 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2014 : cachedArtifact.instructionPC 1991 = 2543 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2015 : cachedArtifact.instructionPC 1992 = 2544 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2016 : cachedArtifact.instructionPC 1993 = 2545 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2017 : cachedArtifact.instructionPC 1994 = 2546 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2018 : cachedArtifact.instructionPC 1995 = 2549 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2019 : cachedArtifact.instructionPC 1996 = 2550 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2020 : cachedArtifact.instructionPC 1997 = 2553 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2021 : cachedArtifact.instructionPC 1998 = 2554 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2022 : cachedArtifact.instructionPC 1999 = 2556 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2023 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2024 : cachedArtifact.instructionPC 2000 = 2557 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2025 : cachedArtifact.instructionPC 2001 = 2560 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2026 : cachedArtifact.instructionPC 2002 = 2561 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2027 : cachedArtifact.instructionPC 2003 = 2564 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2028 : cachedArtifact.instructionPC 2004 = 2565 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2029 : cachedArtifact.instructionPC 2005 = 2566 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2030 : cachedArtifact.instructionPC 2006 = 2567 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2031 : cachedArtifact.instructionPC 2007 = 2568 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2032 : cachedArtifact.instructionPC 2008 = 2570 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2033 : cachedArtifact.instructionPC 2009 = 2571 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2034 : cachedArtifact.instructionPC 2010 = 2574 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2035 : cachedArtifact.instructionPC 2011 = 2575 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2036 : cachedArtifact.instructionPC 2012 = 2576 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2037 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2038 : cachedArtifact.instructionPC 2013 = 2577 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2039 : cachedArtifact.instructionPC 2014 = 2579 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2040 : cachedArtifact.instructionPC 2015 = 2580 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2041 : cachedArtifact.instructionPC 2016 = 2582 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2042 : cachedArtifact.instructionPC 2017 = 2583 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2043 : cachedArtifact.instructionPC 2018 = 2586 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2044 : cachedArtifact.instructionPC 2019 = 2587 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2045 : cachedArtifact.instructionPC 2020 = 2590 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2046 : cachedArtifact.instructionPC 2021 = 2591 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2047 : cachedArtifact.instructionPC 2022 = 2594 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2048 : cachedArtifact.instructionPC 2023 = 2595 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2049 : cachedArtifact.instructionPC 2024 = 2598 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2050 : cachedArtifact.instructionPC 2025 = 2599 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2051 : cachedArtifact.instructionPC 2026 = 2602 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2052 : cachedArtifact.instructionPC 2027 = 2603 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2053 : cachedArtifact.instructionPC 2028 = 2606 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2054 : cachedArtifact.instructionPC 2029 = 2607 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2055 : cachedArtifact.instructionPC 2030 = 2610 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2056 : cachedArtifact.instructionPC 2031 = 2611 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2057 : cachedArtifact.instructionPC 2032 = 2614 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2058 : cachedArtifact.instructionPC 2033 = 2615 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2059 : cachedArtifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2060 : cachedArtifact.instructionPC 2035 = 2619 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2061 : cachedArtifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2062 : cachedArtifact.instructionPC 2037 = 2623 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2063 : cachedArtifact.instructionPC 2038 = 2626 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2064 : cachedArtifact.instructionPC 2039 = 2627 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
end CycleSubmission.Global.ShiftPCs

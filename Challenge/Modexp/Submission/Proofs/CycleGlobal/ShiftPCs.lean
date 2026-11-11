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

@[simp] theorem pc2545 : IPC 1855 = 2357 := by pc_by_len

@[simp] theorem pc2546 : IPC 1856 = 2358 := by pc_by_len

@[simp] theorem pc2547 : IPC 1857 = 2359 := by pc_by_len

@[simp] theorem pc2548 : IPC 1858 = 2360 := by pc_by_len

@[simp] theorem pc2556 : IPC 1859 = 2361 := by pc_by_len

@[simp] theorem pc2559 : IPC 1860 = 2363 := by pc_by_len

@[simp] theorem pc2560 : IPC 1861 = 2364 := by pc_by_len

@[simp] theorem pc2561 : IPC 1862 = 2365 := by pc_by_len

@[simp] theorem pc2563 : IPC 1863 = 2367 := by pc_by_len

@[simp] theorem pc2566 : IPC 1864 = 2370 := by pc_by_len


@[simp] theorem pc2567 : IPC 1865 = 2371 := by pc_by_len

@[simp] theorem pc2570 : IPC 1866 = 2374 := by pc_by_len

@[simp] theorem pc2574 : IPC 1868 = 2378 := by pc_by_len

@[simp] theorem pc2586 : IPC 1879 = 2397 := by pc_by_len

@[simp] theorem pc2591 : IPC 1885 = 2406 := by pc_by_len

@[simp] theorem pc2592 : IPC 1886 = 2407 := by pc_by_len



@[simp] theorem pc2600 : IPC 1914 = 2452 := by pc_by_len

@[simp] theorem pc2604 : IPC 1916 = 2454 := by pc_by_len



@[simp] theorem pc2618 : IPC 1920 = 2460 := by pc_by_len

@[simp] theorem pc2619 : IPC 1921 = 2461 := by pc_by_len

@[simp] theorem pc2620 : IPC 1922 = 2462 := by pc_by_len

@[simp] theorem pc2621 : IPC 1923 = 2463 := by pc_by_len

@[simp] theorem pc2622 : IPC 1924 = 2464 := by pc_by_len

@[simp] theorem pc2623 : IPC 1925 = 2465 := by pc_by_len

@[simp] theorem pc2624 : IPC 1926 = 2466 := by pc_by_len

@[simp] theorem pc2625 : IPC 1927 = 2467 := by pc_by_len

@[simp] theorem pc2628 : IPC 1928 = 2468 := by pc_by_len

@[simp] theorem pc2629 : IPC 1929 = 2469 := by pc_by_len

@[simp] theorem pc2631 : IPC 1930 = 2471 := by pc_by_len

@[simp] theorem pc2632 : IPC 1931 = 2472 := by pc_by_len

@[simp] theorem pc2633 : IPC 1932 = 2475 := by pc_by_len

@[simp] theorem pc2636 : IPC 1933 = 2476 := by pc_by_len

@[simp] theorem pc2637 : IPC 1934 = 2478 := by pc_by_len

@[simp] theorem pc2638 : IPC 1935 = 2479 := by pc_by_len

@[simp] theorem pc2639 : IPC 1936 = 2482 := by pc_by_len

@[simp] theorem pc2641 : IPC 1937 = 2483 := by pc_by_len

@[simp] theorem pc2642 : IPC 1938 = 2484 := by pc_by_len

@[simp] theorem pc2644 : IPC 1939 = 2485 := by pc_by_len

@[simp] theorem pc2645 : IPC 1940 = 2486 := by pc_by_len

@[simp] theorem pc2648 : IPC 1941 = 2489 := by pc_by_len

@[simp] theorem pc2649 : IPC 1942 = 2490 := by pc_by_len

@[simp] theorem pc2650 : IPC 1943 = 2491 := by pc_by_len

@[simp] theorem pc2651 : IPC 1944 = 2492 := by pc_by_len

@[simp] theorem pc2652 : IPC 1945 = 2493 := by pc_by_len

@[simp] theorem pc2653 : IPC 1946 = 2494 := by pc_by_len

@[simp] theorem pc2654 : IPC 1947 = 2495 := by pc_by_len

@[simp] theorem pc2657 : IPC 1948 = 2498 := by pc_by_len

@[simp] theorem pc2658 : IPC 1949 = 2499 := by pc_by_len

@[simp] theorem pc2659 : IPC 1950 = 2502 := by pc_by_len

@[simp] theorem pc2695 : IPC 1996 = 2556 := by pc_by_len

@[simp] theorem pc2696 : IPC 1997 = 2557 := by pc_by_len

@[simp] theorem pc2698 : IPC 1998 = 2558 := by pc_by_len

@[simp] theorem pc2699 : IPC 1999 = 2559 := by pc_by_len





@[simp] theorem pc2702 : IPC 2000 = 2562 := by pc_by_len

@[simp] theorem pc2703 : IPC 2001 = 2563 := by pc_by_len

@[simp] theorem pc2705 : IPC 2002 = 2564 := by pc_by_len

@[simp] theorem pc2706 : IPC 2003 = 2565 := by pc_by_len

@[simp] theorem pc2713 : IPC 2006 = 2570 := by pc_by_len

@[simp] theorem pc3009 : IPC 2190 = 2848 := by pc_by_len

@[simp] theorem pc3010 : IPC 2191 = 2849 := by pc_by_len

@[simp] theorem pc3011 : IPC 2192 = 2850 := by pc_by_len

@[simp] theorem pc3012 : IPC 2193 = 2851 := by pc_by_len

@[simp] theorem pc3013 : IPC 2194 = 2852 := by pc_by_len





@[simp] theorem pc2712 : IPC 2005 = 2569 := by pc_by_len

@[simp] theorem pc3125 : IPC 2286 = 2960 := by pc_by_len







@[simp] theorem pc3171 : IPC 2323 = 3003 := by pc_by_len

@[simp] theorem pc3174 : IPC 2324 = 3006 := by pc_by_len

@[simp] theorem pc3175 : IPC 2325 = 3007 := by pc_by_len

@[simp] theorem pc3176 : IPC 2326 = 3008 := by pc_by_len

@[simp] theorem pc3177 : IPC 2327 = 3009 := by pc_by_len

@[simp] theorem pc3178 : IPC 2328 = 3010 := by pc_by_len

@[simp] theorem pc3179 : IPC 2329 = 3013 := by pc_by_len

@[simp] theorem pc3180 : IPC 2330 = 3014 := by pc_by_len

@[simp] theorem pc3181 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3182 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3183 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3184 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3185 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3186 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3187 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3188 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3191 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pc3192 : IPC 2331 = 3045 := by pc_by_len




@[simp] theorem pcSaturate2992 : IPC 2271 = 2941 := by pc_by_len

@[simp] theorem pcSaturate2993 : IPC 2272 = 2942 := by pc_by_len

@[simp] theorem earlyExtraPC2883 : IPC 2582 = 3414 := by pc_by_len

@[simp] theorem earlyExtraPC2884 : IPC 2583 = 3415 := by pc_by_len

@[simp] theorem earlyExtraPC2885 : IPC 2584 = 3416 := by pc_by_len

@[simp] theorem earlyExtraPC2886 : IPC 2585 = 3417 := by pc_by_len

@[simp] theorem earlyExtraPC2888 : IPC 2586 = 3418 := by pc_by_len

@[simp] theorem earlyExtraPC2889 : IPC 2587 = 3419 := by pc_by_len

@[simp] theorem earlyExtraPC2890 : IPC 2588 = 3420 := by pc_by_len

@[simp] theorem earlyExtraPC2891 : IPC 2589 = 3423 := by pc_by_len

@[simp] theorem earlyExtraPC2892 : IPC 2590 = 3424 := by pc_by_len

@[simp] theorem earlyExtraPC2893 : IPC 2590 = 3424 := by pc_by_len

@[simp] theorem earlyExtraPC2894 : IPC 2591 = 3427 := by pc_by_len

@[simp] theorem earlyExtraPC2895 : IPC 2592 = 3428 := by pc_by_len

@[simp] theorem earlyExtraPC2896 : IPC 2604 = 3448 := by pc_by_len

@[simp] theorem earlyExtraPC2930 : IPC 2604 = 3448 := by pc_by_len

@[simp] theorem earlyExtraPC2931 : IPC 2604 = 3448 := by pc_by_len

@[simp] theorem earlyExtraPC2932 : IPC 2605 = 3451 := by pc_by_len

@[simp] theorem earlyExtraPC2933 : IPC 2606 = 3452 := by pc_by_len

@[simp] theorem earlyExtraPC2934 : IPC 2607 = 3453 := by pc_by_len

@[simp] theorem earlyExtraPC2935 : IPC 2608 = 3454 := by pc_by_len

@[simp] theorem earlyExtraPC2936 : IPC 2609 = 3457 := by pc_by_len

@[simp] theorem earlyExtraPC2937 : IPC 2610 = 3458 := by pc_by_len

@[simp] theorem earlyExtraPC2938 : IPC 2611 = 3460 := by pc_by_len

@[simp] theorem earlyExtraPC2939 : IPC 2612 = 3461 := by pc_by_len

@[simp] theorem earlyExtraPC2940 : IPC 2613 = 3462 := by pc_by_len

@[simp] theorem earlyExtraPC2941 : IPC 2614 = 3463 := by pc_by_len

@[simp] theorem earlyExtraPC2942 : IPC 2615 = 3464 := by pc_by_len

@[simp] theorem earlyExtraPC2943 : IPC 2616 = 3467 := by pc_by_len


@[simp] theorem pcC3009 : IPC 2328 = 3010 := by pc_by_len

@[simp] theorem pcC3010 : IPC 2329 = 3013 := by pc_by_len

@[simp] theorem pcC3011 : IPC 2330 = 3014 := by pc_by_len

@[simp] theorem pcC3019 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pcC3020 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pcC3021 : IPC 2331 = 3045 := by pc_by_len



/-! Program counters of the retained-T blocks the head-start table did not carry (generated from the artifact). -/

@[simp] theorem pcT2106 : IPC 1869 = 2379 := by pc_by_len

@[simp] theorem pcT2329 : IPC 2274 = 2944 := by pc_by_len

@[simp] theorem pcT2330 : IPC 2275 = 2945 := by pc_by_len

@[simp] theorem pcT2331 : IPC 2276 = 2946 := by pc_by_len

@[simp] theorem pcT2332 : IPC 2277 = 2947 := by pc_by_len

@[simp] theorem pcT2336 : IPC 2281 = 2953 := by pc_by_len

@[simp] theorem pcT2337 : IPC 2282 = 2954 := by pc_by_len

@[simp] theorem pcT2338 : IPC 2283 = 2955 := by pc_by_len

@[simp] theorem pcT2339 : IPC 2284 = 2956 := by pc_by_len

@[simp] theorem pcT2340 : IPC 2285 = 2959 := by pc_by_len

@[simp] theorem pcT2341 : IPC 2286 = 2960 := by pc_by_len

@[simp] theorem pcT2342 : IPC 2287 = 2961 := by pc_by_len

@[simp] theorem pcT2343 : IPC 2288 = 2962 := by pc_by_len

@[simp] theorem pcT2344 : IPC 2289 = 2963 := by pc_by_len

@[simp] theorem pcT2345 : IPC 2290 = 2964 := by pc_by_len

@[simp] theorem pcT2346 : IPC 2291 = 2965 := by pc_by_len

@[simp] theorem pcT2347 : IPC 2292 = 2966 := by pc_by_len

@[simp] theorem pcT2348 : IPC 2293 = 2967 := by pc_by_len

@[simp] theorem pcT2349 : IPC 2294 = 2970 := by pc_by_len

@[simp] theorem pcT2350 : IPC 2295 = 2971 := by pc_by_len

@[simp] theorem pcT2351 : IPC 2296 = 2972 := by pc_by_len

@[simp] theorem pcT2352 : IPC 2297 = 2973 := by pc_by_len

@[simp] theorem pcT2353 : IPC 2298 = 2974 := by pc_by_len

@[simp] theorem pcT2354 : IPC 2299 = 2975 := by pc_by_len

@[simp] theorem pcT2355 : IPC 2300 = 2976 := by pc_by_len

@[simp] theorem pcT2356 : IPC 2301 = 2977 := by pc_by_len

@[simp] theorem pcT2357 : IPC 2302 = 2978 := by pc_by_len

@[simp] theorem pcT2358 : IPC 2303 = 2979 := by pc_by_len

@[simp] theorem pcT2359 : IPC 2304 = 2980 := by pc_by_len

@[simp] theorem pcT2360 : IPC 2305 = 2981 := by pc_by_len

@[simp] theorem pcT2361 : IPC 2306 = 2982 := by pc_by_len

@[simp] theorem pcT2362 : IPC 2307 = 2983 := by pc_by_len

@[simp] theorem pcT2363 : IPC 2308 = 2984 := by pc_by_len

@[simp] theorem pcT2364 : IPC 2309 = 2985 := by pc_by_len

@[simp] theorem pcT2365 : IPC 2310 = 2988 := by pc_by_len

@[simp] theorem pcT2366 : IPC 2311 = 2989 := by pc_by_len

@[simp] theorem pcT2367 : IPC 2312 = 2990 := by pc_by_len

@[simp] theorem pcT2368 : IPC 2313 = 2991 := by pc_by_len

@[simp] theorem pcT2369 : IPC 2314 = 2992 := by pc_by_len

@[simp] theorem pcT2370 : IPC 2315 = 2995 := by pc_by_len

@[simp] theorem pcT2371 : IPC 2316 = 2996 := by pc_by_len

@[simp] theorem pcT2372 : IPC 2317 = 2997 := by pc_by_len

@[simp] theorem pcT2522 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pcI2013 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2014 : IPC 1814 = 2285 := by pc_by_len

@[simp] theorem pcI2015 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2016 : IPC 1816 = 2288 := by pc_by_len

@[simp] theorem pcI2017 : IPC 1817 = 2289 := by pc_by_len

@[simp] theorem pcI2018 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2032 : IPC 1822 = 2298 := by pc_by_len

@[simp] theorem pcI2033 : IPC 1823 = 2299 := by pc_by_len

@[simp] theorem pcI2034 : IPC 1824 = 2300 := by pc_by_len

@[simp] theorem pcI2035 : IPC 1825 = 2304 := by pc_by_len

@[simp] theorem pcI2036 : IPC 1835 = 2315 := by pc_by_len

@[simp] theorem pcI2037 : IPC 1836 = 2316 := by pc_by_len

@[simp] theorem pcI2038 : IPC 1838 = 2319 := by pc_by_len

@[simp] theorem pcI2039 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2040 : IPC 1813 = 2284 := by pc_by_len

@[simp] theorem pcI2041 : IPC 1839 = 2323 := by pc_by_len

@[simp] theorem pcI2042 : IPC 1840 = 2324 := by pc_by_len

@[simp] theorem pcI2043 : IPC 1844 = 2330 := by pc_by_len

@[simp] theorem pcI2044 : IPC 1845 = 2331 := by pc_by_len

@[simp] theorem pcI2045 : IPC 1846 = 2333 := by pc_by_len

@[simp] theorem pcI2046 : IPC 1847 = 2334 := by pc_by_len

@[simp] theorem pcI2047 : IPC 1848 = 2336 := by pc_by_len

@[simp] theorem pcI2048 : IPC 1849 = 2337 := by pc_by_len

@[simp] theorem pcI2049 : IPC 1849 = 2337 := by pc_by_len

@[simp] theorem pcI2050 : IPC 1850 = 2338 := by pc_by_len

@[simp] theorem pcI2051 : IPC 1850 = 2338 := by pc_by_len

@[simp] theorem pcI2052 : IPC 1850 = 2338 := by pc_by_len

@[simp] theorem pcI2053 : IPC 1850 = 2338 := by pc_by_len

@[simp] theorem pcI2054 : IPC 1851 = 2347 := by pc_by_len

@[simp] theorem pcI2055 : IPC 1852 = 2350 := by pc_by_len

@[simp] theorem pcI2056 : IPC 1853 = 2353 := by pc_by_len

@[simp] theorem pcI2057 : IPC 1854 = 2356 := by pc_by_len

@[simp] theorem pcI2093 : IPC 1870 = 2380 := by pc_by_len

@[simp] theorem pcI2094 : IPC 1871 = 2383 := by pc_by_len

@[simp] theorem pcI2095 : IPC 1872 = 2386 := by pc_by_len

@[simp] theorem pcI2156 : IPC 1951 = 2503 := by pc_by_len

@[simp] theorem pcI2200 : IPC 2006 = 2570 := by pc_by_len

@[simp] theorem pcI2201 : IPC 2007 = 2575 := by pc_by_len

@[simp] theorem pcI2202 : IPC 2018 = 2590 := by pc_by_len

@[simp] theorem pcI2203 : IPC 2019 = 2591 := by pc_by_len

@[simp] theorem pcI2204 : IPC 2020 = 2592 := by pc_by_len

@[simp] theorem pcI2205 : IPC 2024 = 2601 := by pc_by_len

@[simp] theorem pcI2206 : IPC 2025 = 2604 := by pc_by_len

@[simp] theorem pcI2207 : IPC 2026 = 2605 := by pc_by_len

@[simp] theorem pcI2208 : IPC 2027 = 2608 := by pc_by_len

@[simp] theorem pcI2209 : IPC 2028 = 2609 := by pc_by_len

@[simp] theorem pcI2210 : IPC 2029 = 2612 := by pc_by_len

@[simp] theorem pcI2211 : IPC 2030 = 2613 := by pc_by_len

@[simp] theorem pcI2212 : IPC 2031 = 2616 := by pc_by_len

@[simp] theorem pcI2213 : IPC 2032 = 2617 := by pc_by_len

@[simp] theorem pcI2214 : IPC 2033 = 2620 := by pc_by_len

@[simp] theorem pcI2215 : IPC 2034 = 2621 := by pc_by_len

@[simp] theorem pcI2216 : IPC 2035 = 2624 := by pc_by_len

@[simp] theorem pcI2217 : IPC 2036 = 2625 := by pc_by_len

@[simp] theorem pcI2218 : IPC 2037 = 2628 := by pc_by_len

@[simp] theorem pcI2219 : IPC 2038 = 2629 := by pc_by_len

@[simp] theorem pcI2220 : IPC 2039 = 2632 := by pc_by_len

@[simp] theorem pcI2221 : IPC 2040 = 2633 := by pc_by_len

@[simp] theorem pcI2222 : IPC 2041 = 2636 := by pc_by_len

@[simp] theorem pcI2223 : IPC 2042 = 2637 := by pc_by_len

@[simp] theorem pcI2224 : IPC 2043 = 2640 := by pc_by_len

@[simp] theorem pcI2225 : IPC 2044 = 2641 := by pc_by_len

@[simp] theorem pcI2226 : IPC 2045 = 2644 := by pc_by_len

@[simp] theorem pcI2330 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2332 : IPC 2109 = 2757 := by pc_by_len

@[simp] theorem pcI2333 : IPC 2110 = 2758 := by pc_by_len

@[simp] theorem pcI2334 : IPC 2111 = 2759 := by pc_by_len

@[simp] theorem pcI2335 : IPC 2112 = 2760 := by pc_by_len

@[simp] theorem pcI2336 : IPC 2113 = 2761 := by pc_by_len

@[simp] theorem pcI2337 : IPC 2114 = 2762 := by pc_by_len

@[simp] theorem pcI2338 : IPC 2115 = 2763 := by pc_by_len

@[simp] theorem pcI2339 : IPC 2116 = 2764 := by pc_by_len

@[simp] theorem pcI2340 : IPC 2117 = 2765 := by pc_by_len

@[simp] theorem pcI2341 : IPC 2118 = 2768 := by pc_by_len

@[simp] theorem pcI2342 : IPC 2119 = 2769 := by pc_by_len

@[simp] theorem pcI2343 : IPC 2120 = 2770 := by pc_by_len

@[simp] theorem pcI2344 : IPC 2121 = 2771 := by pc_by_len

@[simp] theorem pcI2345 : IPC 2122 = 2772 := by pc_by_len

@[simp] theorem pcI2346 : IPC 2123 = 2773 := by pc_by_len

@[simp] theorem pcI2347 : IPC 2124 = 2774 := by pc_by_len

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

@[simp] theorem pcI2360 : IPC 2125 = 2775 := by pc_by_len

@[simp] theorem pcI2361 : IPC 2126 = 2776 := by pc_by_len

@[simp] theorem pcI2362 : IPC 2127 = 2777 := by pc_by_len

@[simp] theorem pcI2363 : IPC 2128 = 2778 := by pc_by_len

@[simp] theorem pcI2364 : IPC 2129 = 2779 := by pc_by_len

@[simp] theorem pcI2365 : IPC 2130 = 2780 := by pc_by_len

@[simp] theorem pcI2366 : IPC 2131 = 2781 := by pc_by_len

@[simp] theorem pcI2367 : IPC 2132 = 2782 := by pc_by_len

@[simp] theorem pcI2368 : IPC 2133 = 2783 := by pc_by_len

@[simp] theorem pcI2369 : IPC 2134 = 2784 := by pc_by_len

@[simp] theorem pcI2370 : IPC 2135 = 2785 := by pc_by_len

@[simp] theorem pcI2371 : IPC 2136 = 2786 := by pc_by_len

@[simp] theorem pcI2372 : IPC 2137 = 2787 := by pc_by_len

@[simp] theorem pcI2373 : IPC 2138 = 2788 := by pc_by_len

@[simp] theorem pcI2374 : IPC 2139 = 2789 := by pc_by_len

@[simp] theorem pcI2375 : IPC 2140 = 2792 := by pc_by_len

@[simp] theorem pcI2376 : IPC 2141 = 2793 := by pc_by_len

@[simp] theorem pcI2377 : IPC 2142 = 2794 := by pc_by_len

@[simp] theorem pcI2378 : IPC 2143 = 2795 := by pc_by_len

@[simp] theorem pcI2379 : IPC 2144 = 2796 := by pc_by_len

@[simp] theorem pcI2380 : IPC 2145 = 2799 := by pc_by_len

@[simp] theorem pcI2381 : IPC 2146 = 2800 := by pc_by_len

@[simp] theorem pcI2382 : IPC 2147 = 2801 := by pc_by_len

@[simp] theorem pcI2383 : IPC 2148 = 2802 := by pc_by_len

@[simp] theorem pcI2384 : IPC 2149 = 2803 := by pc_by_len

@[simp] theorem pcI2385 : IPC 2150 = 2804 := by pc_by_len

@[simp] theorem pcI2386 : IPC 2151 = 2805 := by pc_by_len

@[simp] theorem pcI2387 : IPC 2152 = 2806 := by pc_by_len

@[simp] theorem pcI2388 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2389 : IPC 2153 = 2807 := by pc_by_len

@[simp] theorem pcI2390 : IPC 2154 = 2808 := by pc_by_len

@[simp] theorem pcI2391 : IPC 2155 = 2809 := by pc_by_len

@[simp] theorem pcI2392 : IPC 2156 = 2810 := by pc_by_len

@[simp] theorem pcI2393 : IPC 2157 = 2811 := by pc_by_len

@[simp] theorem pcI2394 : IPC 2158 = 2812 := by pc_by_len

@[simp] theorem pcI2395 : IPC 2159 = 2813 := by pc_by_len

@[simp] theorem pcI2396 : IPC 2160 = 2814 := by pc_by_len

@[simp] theorem pcI2397 : IPC 2161 = 2815 := by pc_by_len

@[simp] theorem pcI2398 : IPC 2162 = 2816 := by pc_by_len

@[simp] theorem pcI2399 : IPC 2163 = 2817 := by pc_by_len

@[simp] theorem pcI2400 : IPC 2164 = 2818 := by pc_by_len

@[simp] theorem pcI2401 : IPC 2165 = 2819 := by pc_by_len

@[simp] theorem pcI2402 : IPC 2166 = 2820 := by pc_by_len

@[simp] theorem pcI2403 : IPC 2167 = 2821 := by pc_by_len

@[simp] theorem pcI2404 : IPC 2168 = 2824 := by pc_by_len

@[simp] theorem pcI2405 : IPC 2169 = 2825 := by pc_by_len

@[simp] theorem pcI2406 : IPC 2170 = 2826 := by pc_by_len

@[simp] theorem pcI2407 : IPC 2171 = 2827 := by pc_by_len

@[simp] theorem pcI2408 : IPC 2172 = 2828 := by pc_by_len

@[simp] theorem pcI2409 : IPC 2173 = 2831 := by pc_by_len

@[simp] theorem pcI2410 : IPC 2174 = 2832 := by pc_by_len

@[simp] theorem pcI2411 : IPC 2175 = 2833 := by pc_by_len

@[simp] theorem pcI2412 : IPC 2176 = 2834 := by pc_by_len

@[simp] theorem pcI2413 : IPC 2177 = 2835 := by pc_by_len

@[simp] theorem pcI2414 : IPC 2178 = 2836 := by pc_by_len

@[simp] theorem pcI2415 : IPC 2179 = 2837 := by pc_by_len

@[simp] theorem pcI2416 : IPC 2180 = 2838 := by pc_by_len

@[simp] theorem pcI2417 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2418 : IPC 2181 = 2839 := by pc_by_len

@[simp] theorem pcI2419 : IPC 2182 = 2840 := by pc_by_len

@[simp] theorem pcI2420 : IPC 2183 = 2841 := by pc_by_len

@[simp] theorem pcI2421 : IPC 2184 = 2842 := by pc_by_len

@[simp] theorem pcI2422 : IPC 2185 = 2843 := by pc_by_len

@[simp] theorem pcI2423 : IPC 2186 = 2844 := by pc_by_len

@[simp] theorem pcI2424 : IPC 2187 = 2845 := by pc_by_len

@[simp] theorem pcI2425 : IPC 2188 = 2846 := by pc_by_len

@[simp] theorem pcI2426 : IPC 2189 = 2847 := by pc_by_len

@[simp] theorem pcI2432 : IPC 2195 = 2853 := by pc_by_len

@[simp] theorem pcI2433 : IPC 2196 = 2856 := by pc_by_len

@[simp] theorem pcI2434 : IPC 2197 = 2857 := by pc_by_len

@[simp] theorem pcI2435 : IPC 2198 = 2858 := by pc_by_len

@[simp] theorem pcI2436 : IPC 2199 = 2859 := by pc_by_len

@[simp] theorem pcI2437 : IPC 2200 = 2860 := by pc_by_len

@[simp] theorem pcI2438 : IPC 2201 = 2863 := by pc_by_len

@[simp] theorem pcI2439 : IPC 2202 = 2864 := by pc_by_len

@[simp] theorem pcI2440 : IPC 2203 = 2865 := by pc_by_len

@[simp] theorem pcI2441 : IPC 2204 = 2866 := by pc_by_len

@[simp] theorem pcI2442 : IPC 2205 = 2867 := by pc_by_len

@[simp] theorem pcI2443 : IPC 2206 = 2868 := by pc_by_len

@[simp] theorem pcI2444 : IPC 2207 = 2869 := by pc_by_len

@[simp] theorem pcI2445 : IPC 2208 = 2870 := by pc_by_len

@[simp] theorem pcI2446 : IPC 2209 = 2871 := by pc_by_len

@[simp] theorem pcI2447 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2448 : IPC 2210 = 2872 := by pc_by_len

@[simp] theorem pcI2449 : IPC 2211 = 2873 := by pc_by_len

@[simp] theorem pcI2450 : IPC 2212 = 2874 := by pc_by_len

@[simp] theorem pcI2451 : IPC 2213 = 2875 := by pc_by_len

@[simp] theorem pcI2452 : IPC 2214 = 2876 := by pc_by_len

@[simp] theorem pcI2453 : IPC 2215 = 2877 := by pc_by_len

@[simp] theorem pcI2454 : IPC 2216 = 2878 := by pc_by_len

@[simp] theorem pcI2455 : IPC 2217 = 2879 := by pc_by_len

@[simp] theorem pcI2456 : IPC 2218 = 2880 := by pc_by_len

@[simp] theorem pcI2457 : IPC 2219 = 2881 := by pc_by_len

@[simp] theorem pcI2458 : IPC 2220 = 2882 := by pc_by_len

@[simp] theorem pcI2459 : IPC 2221 = 2883 := by pc_by_len

@[simp] theorem pcI2460 : IPC 2222 = 2884 := by pc_by_len

@[simp] theorem pcI2461 : IPC 2223 = 2885 := by pc_by_len

@[simp] theorem pcI2462 : IPC 2224 = 2888 := by pc_by_len

@[simp] theorem pcI2463 : IPC 2225 = 2889 := by pc_by_len

@[simp] theorem pcI2464 : IPC 2226 = 2890 := by pc_by_len

@[simp] theorem pcI2465 : IPC 2227 = 2891 := by pc_by_len

@[simp] theorem pcI2466 : IPC 2228 = 2892 := by pc_by_len

@[simp] theorem pcI2467 : IPC 2229 = 2895 := by pc_by_len

@[simp] theorem pcI2468 : IPC 2230 = 2896 := by pc_by_len

@[simp] theorem pcI2469 : IPC 2231 = 2897 := by pc_by_len

@[simp] theorem pcI2470 : IPC 2232 = 2898 := by pc_by_len

@[simp] theorem pcI2471 : IPC 2233 = 2899 := by pc_by_len

@[simp] theorem pcI2472 : IPC 2234 = 2900 := by pc_by_len

@[simp] theorem pcI2473 : IPC 2235 = 2901 := by pc_by_len

@[simp] theorem pcI2474 : IPC 2236 = 2902 := by pc_by_len

@[simp] theorem pcI2475 : IPC 2237 = 2903 := by pc_by_len

@[simp] theorem pcI2476 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2477 : IPC 2238 = 2904 := by pc_by_len

@[simp] theorem pcI2478 : IPC 2239 = 2905 := by pc_by_len

@[simp] theorem pcI2479 : IPC 2240 = 2906 := by pc_by_len

@[simp] theorem pcI2480 : IPC 2241 = 2907 := by pc_by_len

@[simp] theorem pcI2481 : IPC 2242 = 2908 := by pc_by_len

@[simp] theorem pcI2482 : IPC 2243 = 2909 := by pc_by_len

@[simp] theorem pcI2483 : IPC 2244 = 2910 := by pc_by_len

@[simp] theorem pcI2484 : IPC 2245 = 2911 := by pc_by_len

@[simp] theorem pcI2485 : IPC 2246 = 2912 := by pc_by_len

@[simp] theorem pcI2486 : IPC 2247 = 2913 := by pc_by_len

@[simp] theorem pcI2487 : IPC 2248 = 2914 := by pc_by_len

@[simp] theorem pcI2488 : IPC 2249 = 2915 := by pc_by_len

@[simp] theorem pcI2489 : IPC 2250 = 2916 := by pc_by_len

@[simp] theorem pcI2490 : IPC 2251 = 2917 := by pc_by_len

@[simp] theorem pcI2492 : IPC 2252 = 2920 := by pc_by_len

@[simp] theorem pcI2493 : IPC 2253 = 2921 := by pc_by_len

@[simp] theorem pcI2494 : IPC 2254 = 2922 := by pc_by_len

@[simp] theorem pcI2495 : IPC 2255 = 2923 := by pc_by_len

@[simp] theorem pcI2496 : IPC 2256 = 2924 := by pc_by_len

@[simp] theorem pcI2497 : IPC 2257 = 2927 := by pc_by_len

@[simp] theorem pcI2498 : IPC 2258 = 2928 := by pc_by_len

@[simp] theorem pcI2499 : IPC 2259 = 2929 := by pc_by_len

@[simp] theorem pcI2500 : IPC 2260 = 2930 := by pc_by_len

@[simp] theorem pcI2501 : IPC 2261 = 2931 := by pc_by_len

@[simp] theorem pcI2502 : IPC 2262 = 2932 := by pc_by_len

@[simp] theorem pcI2503 : IPC 2263 = 2933 := by pc_by_len

@[simp] theorem pcI2504 : IPC 2264 = 2934 := by pc_by_len

@[simp] theorem pcI2505 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2506 : IPC 2265 = 2935 := by pc_by_len

@[simp] theorem pcI2507 : IPC 2266 = 2936 := by pc_by_len

@[simp] theorem pcI2508 : IPC 2267 = 2937 := by pc_by_len

@[simp] theorem pcI2509 : IPC 2268 = 2938 := by pc_by_len

@[simp] theorem pcI2510 : IPC 2269 = 2939 := by pc_by_len

@[simp] theorem pcI2511 : IPC 2270 = 2940 := by pc_by_len

@[simp] theorem pcI2514 : IPC 2273 = 2943 := by pc_by_len

@[simp] theorem pcI2519 : IPC 2278 = 2948 := by pc_by_len

@[simp] theorem pcI2520 : IPC 2279 = 2949 := by pc_by_len

@[simp] theorem pcI2521 : IPC 2280 = 2952 := by pc_by_len

@[simp] theorem pcI2559 : IPC 2318 = 2998 := by pc_by_len

@[simp] theorem pcI2560 : IPC 2319 = 2999 := by pc_by_len

@[simp] theorem pcI2561 : IPC 2320 = 3000 := by pc_by_len

@[simp] theorem pcI2562 : IPC 2321 = 3001 := by pc_by_len

@[simp] theorem pcI2563 : IPC 2322 = 3002 := by pc_by_len

@[simp] theorem pcI2564 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2565 : IPC 2323 = 3003 := by pc_by_len

@[simp] theorem pcI2566 : IPC 2324 = 3006 := by pc_by_len

@[simp] theorem pcI2585 : IPC 2331 = 3045 := by pc_by_len

/-! ## The straight-line negation and the inline Newton chain (negun, inl693) -/

@[simp] theorem negunPC0 (i : Nat) (hi : 1813 ≤ i) (hii : i ≤ 1821) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2284, 2285, 2287, 2288, 2289, 2290, 2293, 2294, 2297] : List Nat)[i - 1813]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem negunPC1 (i : Nat) (hi : 1873 ≤ i) (hii : i ≤ 1919) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2387, 2388, 2390, 2391, 2394, 2395, 2397, 2398, 2399, 2400, 2403, 2404, 2406, 2407, 2408, 2411, 2412, 2414, 2415, 2416, 2419, 2420, 2422, 2423, 2424, 2427, 2428, 2430, 2431, 2432, 2435, 2436, 2437, 2439, 2440, 2441, 2444, 2445, 2447, 2448, 2449, 2452, 2453, 2454, 2455, 2456, 2457] : List Nat)[i - 1873]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem negunPC2 (i : Nat) (hi : 1952 ≤ i) (hii : i ≤ 1995) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2504, 2505, 2506, 2507, 2508, 2510, 2511, 2513, 2514, 2515, 2516, 2517, 2519, 2520, 2521, 2522, 2523, 2524, 2526, 2527, 2528, 2529, 2530, 2531, 2533, 2534, 2535, 2536, 2537, 2538, 2540, 2541, 2542, 2543, 2544, 2545, 2547, 2548, 2549, 2550, 2551, 2552, 2554, 2555] : List Nat)[i - 1952]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-! ## Directly stated pcs: E5 and the eight-limb loop head (2056 .. 2146), the bottom test,
the exit / E3 phase blocks and the repair loop (2381 .. 2465), and the appended four-limb
loop head (8548 .. 8610). -/

@[simp] theorem pcDual2056 : IPC 2046 = 2645 := by pc_by_len

@[simp] theorem pcDual2057 : IPC 2020 = 2592 := by pc_by_len

@[simp] theorem pcDual2065 : IPC 2021 = 2594 := by pc_by_len

@[simp] theorem pcDual2066 : IPC 2022 = 2595 := by pc_by_len

@[simp] theorem pcDual2067 : IPC 2023 = 2600 := by pc_by_len

@[simp] theorem pcDual2068 : IPC 2046 = 2645 := by pc_by_len

@[simp] theorem pcDual2069 : IPC 2008 = 2576 := by pc_by_len

@[simp] theorem pcDual2070 : IPC 2009 = 2578 := by pc_by_len

@[simp] theorem pcDual2071 : IPC 2010 = 2579 := by pc_by_len

@[simp] theorem pcDual2072 : IPC 2011 = 2582 := by pc_by_len

@[simp] theorem pcDual2073 : IPC 2012 = 2583 := by pc_by_len

@[simp] theorem pcDual2074 : IPC 2013 = 2584 := by pc_by_len

@[simp] theorem pcDual2075 : IPC 2014 = 2585 := by pc_by_len

@[simp] theorem pcDual2076 : IPC 2015 = 2586 := by pc_by_len

@[simp] theorem pcDual2077 : IPC 2016 = 2588 := by pc_by_len

@[simp] theorem pcDual2078 : IPC 2017 = 2589 := by pc_by_len

@[simp] theorem pcDual2079 : IPC 2046 = 2645 := by pc_by_len

@[simp] theorem pcDual2080 : IPC 2046 = 2645 := by pc_by_len

@[simp] theorem pcDual2081 : IPC 2047 = 2646 := by pc_by_len

@[simp] theorem pcDual2082 : IPC 2048 = 2647 := by pc_by_len

@[simp] theorem pcDual2083 : IPC 2049 = 2648 := by pc_by_len

@[simp] theorem pcDual2084 : IPC 2050 = 2649 := by pc_by_len

@[simp] theorem pcDual2085 : IPC 2051 = 2652 := by pc_by_len

@[simp] theorem pcDual2086 : IPC 2052 = 2653 := by pc_by_len

@[simp] theorem pcDual2087 : IPC 2053 = 2656 := by pc_by_len

@[simp] theorem pcDual2088 : IPC 2054 = 2657 := by pc_by_len

@[simp] theorem pcDual2089 : IPC 2055 = 2658 := by pc_by_len

@[simp] theorem pcDual2090 : IPC 2056 = 2659 := by pc_by_len

@[simp] theorem pcDual2091 : IPC 2057 = 2660 := by pc_by_len

@[simp] theorem pcDual2092 : IPC 2058 = 2661 := by pc_by_len

@[simp] theorem pcDual2093 : IPC 2059 = 2662 := by pc_by_len

@[simp] theorem pcDual2094 : IPC 2060 = 2665 := by pc_by_len

@[simp] theorem pcDual2095 : IPC 2061 = 2668 := by pc_by_len

@[simp] theorem pcDual2096 : IPC 2062 = 2669 := by pc_by_len

@[simp] theorem pcDual2100 : IPC 2063 = 2672 := by pc_by_len

@[simp] theorem pcDual2101 : IPC 2064 = 2673 := by pc_by_len

@[simp] theorem pcDual2102 : IPC 2065 = 2674 := by pc_by_len

@[simp] theorem pcDual2103 : IPC 2066 = 2675 := by pc_by_len

@[simp] theorem pcDual2104 : IPC 2067 = 2676 := by pc_by_len

@[simp] theorem pcDual2105 : IPC 2068 = 2677 := by pc_by_len

@[simp] theorem pcDual2106 : IPC 2069 = 2680 := by pc_by_len

@[simp] theorem pcDual2107 : IPC 2070 = 2681 := by pc_by_len

@[simp] theorem pcDual2108 : IPC 2071 = 2682 := by pc_by_len

@[simp] theorem pcDual2109 : IPC 2072 = 2685 := by pc_by_len

@[simp] theorem pcDual2110 : IPC 2073 = 2686 := by pc_by_len

@[simp] theorem pcDual2111 : IPC 2074 = 2687 := by pc_by_len

@[simp] theorem pcDual2112 : IPC 2075 = 2688 := by pc_by_len

@[simp] theorem pcDual2113 : IPC 2076 = 2689 := by pc_by_len

@[simp] theorem pcDual2114 : IPC 2077 = 2690 := by pc_by_len

@[simp] theorem pcDual2115 : IPC 2078 = 2691 := by pc_by_len

@[simp] theorem pcDual2116 : IPC 2079 = 2692 := by pc_by_len

@[simp] theorem pcDual2117 : IPC 2080 = 2693 := by pc_by_len

@[simp] theorem pcDual2118 : IPC 2081 = 2694 := by pc_by_len

@[simp] theorem pcDual2119 : IPC 2082 = 2695 := by pc_by_len

@[simp] theorem pcDual2120 : IPC 2083 = 2696 := by pc_by_len

@[simp] theorem pcDual2121 : IPC 2084 = 2697 := by pc_by_len

@[simp] theorem pcDual2122 : IPC 2085 = 2698 := by pc_by_len

@[simp] theorem pcDual2123 : IPC 2086 = 2699 := by pc_by_len

@[simp] theorem pcDual2124 : IPC 2087 = 2700 := by pc_by_len

@[simp] theorem pcDual2125 : IPC 2088 = 2701 := by pc_by_len

@[simp] theorem pcDual2126 : IPC 2089 = 2702 := by pc_by_len

@[simp] theorem pcDual2127 : IPC 2090 = 2704 := by pc_by_len

@[simp] theorem pcDual2128 : IPC 2091 = 2705 := by pc_by_len

@[simp] theorem pcDual2129 : IPC 2092 = 2706 := by pc_by_len

@[simp] theorem pcDual2130 : IPC 2093 = 2707 := by pc_by_len

@[simp] theorem pcDual2131 : IPC 2094 = 2708 := by pc_by_len

@[simp] theorem pcDual2132 : IPC 2095 = 2709 := by pc_by_len

@[simp] theorem pcDual2133 : IPC 2096 = 2710 := by pc_by_len

@[simp] theorem pcDual2134 : IPC 2097 = 2713 := by pc_by_len

@[simp] theorem pcDual2135 : IPC 2098 = 2714 := by pc_by_len

@[simp] theorem pcDual2136 : IPC 2099 = 2715 := by pc_by_len

@[simp] theorem pcDual2137 : IPC 2100 = 2716 := by pc_by_len

@[simp] theorem pcDual2138 : IPC 2101 = 2717 := by pc_by_len

@[simp] theorem pcDual2139 : IPC 2102 = 2718 := by pc_by_len

@[simp] theorem pcDual2141 : IPC 2103 = 2751 := by pc_by_len

@[simp] theorem pcDual2142 : IPC 2104 = 2752 := by pc_by_len

@[simp] theorem pcDual2143 : IPC 2105 = 2753 := by pc_by_len

@[simp] theorem pcDual2144 : IPC 2106 = 2754 := by pc_by_len

@[simp] theorem pcDual2145 : IPC 2107 = 2755 := by pc_by_len

@[simp] theorem pcDual2146 : IPC 2108 = 2756 := by pc_by_len

@[simp] theorem pcDual2381 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pcDual2382 : IPC 2331 = 3045 := by pc_by_len

@[simp] theorem pcDual2383 : IPC 2332 = 3046 := by pc_by_len

@[simp] theorem pcDual2384 : IPC 2333 = 3047 := by pc_by_len

@[simp] theorem pcDual2385 : IPC 2334 = 3048 := by pc_by_len

@[simp] theorem pcDual2386 : IPC 2335 = 3049 := by pc_by_len

@[simp] theorem pcDual2387 : IPC 2336 = 3050 := by pc_by_len

@[simp] theorem pcDual2388 : IPC 2338 = 3052 := by pc_by_len

@[simp] theorem pcDual2389 : IPC 2338 = 3052 := by pc_by_len

@[simp] theorem pcDual2390 : IPC 2339 = 3053 := by pc_by_len

@[simp] theorem pcDual2391 : IPC 2340 = 3054 := by pc_by_len

@[simp] theorem pcDual2392 : IPC 2340 = 3054 := by pc_by_len

@[simp] theorem pcDual2393 : IPC 2340 = 3054 := by pc_by_len

@[simp] theorem pcDual2394 : IPC 2340 = 3054 := by pc_by_len

@[simp] theorem pcDual2395 : IPC 2341 = 3062 := by pc_by_len

@[simp] theorem pcDual2396 : IPC 8388 = 10972 := by pc_by_len

@[simp] theorem pcDual2397 : IPC 8389 = 10973 := by pc_by_len

@[simp] theorem pcDual2398 : IPC 8390 = 10974 := by pc_by_len

@[simp] theorem pcDual2399 : IPC 8390 = 10974 := by pc_by_len

@[simp] theorem pcDual2400 : IPC 8391 = 10979 := by pc_by_len

@[simp] theorem pcDual2401 : IPC 8392 = 10980 := by pc_by_len

@[simp] theorem pcDual2402 : IPC 8393 = 10981 := by pc_by_len

@[simp] theorem pcDual2403 : IPC 8394 = 10984 := by pc_by_len

@[simp] theorem pcDual2404 : IPC 8395 = 10987 := by pc_by_len

@[simp] theorem pcDual2405 : IPC 8396 = 10988 := by pc_by_len

@[simp] theorem pcDual2406 : IPC 8397 = 10989 := by pc_by_len

@[simp] theorem pcDual2407 : IPC 8398 = 10991 := by pc_by_len

@[simp] theorem pcDual2408 : IPC 8399 = 10992 := by pc_by_len

@[simp] theorem pcDual2409 : IPC 8400 = 10993 := by pc_by_len

@[simp] theorem pcDual2410 : IPC 2347 = 3069 := by pc_by_len

@[simp] theorem pcDual2411 : IPC 2348 = 3070 := by pc_by_len

@[simp] theorem pcDual2412 : IPC 2349 = 3071 := by pc_by_len

@[simp] theorem pcDual2413 : IPC 2350 = 3072 := by pc_by_len

@[simp] theorem pcDual2414 : IPC 2351 = 3073 := by pc_by_len

@[simp] theorem pcDual2415 : IPC 2352 = 3076 := by pc_by_len

@[simp] theorem pcDual2416 : IPC 2353 = 3077 := by pc_by_len

@[simp] theorem pcDual2417 : IPC 2354 = 3078 := by pc_by_len

@[simp] theorem pcDual2418 : IPC 2355 = 3079 := by pc_by_len

@[simp] theorem pcDual2419 : IPC 2356 = 3080 := by pc_by_len

@[simp] theorem pcDual2420 : IPC 2357 = 3083 := by pc_by_len

@[simp] theorem pcDual2421 : IPC 2358 = 3084 := by pc_by_len

@[simp] theorem pcDual2422 : IPC 2359 = 3085 := by pc_by_len

@[simp] theorem pcDual2423 : IPC 2360 = 3086 := by pc_by_len

@[simp] theorem pcDual2424 : IPC 2361 = 3087 := by pc_by_len

@[simp] theorem pcDual2425 : IPC 2362 = 3088 := by pc_by_len

@[simp] theorem pcDual2426 : IPC 2363 = 3089 := by pc_by_len

@[simp] theorem pcDual2427 : IPC 2364 = 3090 := by pc_by_len

@[simp] theorem pcDual2428 : IPC 2365 = 3091 := by pc_by_len

@[simp] theorem pcDual2429 : IPC 2366 = 3092 := by pc_by_len

@[simp] theorem pcDual2430 : IPC 2367 = 3093 := by pc_by_len

@[simp] theorem pcDual2431 : IPC 2368 = 3094 := by pc_by_len

@[simp] theorem pcDual2432 : IPC 2369 = 3095 := by pc_by_len

@[simp] theorem pcDual2433 : IPC 2370 = 3096 := by pc_by_len

@[simp] theorem pcDual2434 : IPC 2371 = 3097 := by pc_by_len

@[simp] theorem pcDual2435 : IPC 2372 = 3098 := by pc_by_len

@[simp] theorem pcDual2436 : IPC 2373 = 3099 := by pc_by_len

@[simp] theorem pcDual2437 : IPC 2374 = 3100 := by pc_by_len

@[simp] theorem pcDual2438 : IPC 2375 = 3101 := by pc_by_len

@[simp] theorem pcDual2439 : IPC 2376 = 3103 := by pc_by_len

@[simp] theorem pcDual2440 : IPC 2377 = 3104 := by pc_by_len

@[simp] theorem pcDual2441 : IPC 2378 = 3105 := by pc_by_len

@[simp] theorem pcDual2442 : IPC 2379 = 3108 := by pc_by_len

@[simp] theorem pcDual2443 : IPC 2380 = 3109 := by pc_by_len

@[simp] theorem pcDual2444 : IPC 2381 = 3110 := by pc_by_len

@[simp] theorem pcDual2445 : IPC 2382 = 3113 := by pc_by_len

@[simp] theorem pcDual2446 : IPC 2383 = 3114 := by pc_by_len

@[simp] theorem pcDual2447 : IPC 2384 = 3115 := by pc_by_len

@[simp] theorem pcDual2448 : IPC 2385 = 3118 := by pc_by_len

@[simp] theorem pcDual2449 : IPC 2386 = 3119 := by pc_by_len

@[simp] theorem pcDual2450 : IPC 2387 = 3120 := by pc_by_len

@[simp] theorem pcDual2451 : IPC 2388 = 3121 := by pc_by_len

@[simp] theorem pcDual2452 : IPC 2389 = 3122 := by pc_by_len

@[simp] theorem pcDual2453 : IPC 2390 = 3125 := by pc_by_len

@[simp] theorem pcDual2454 : IPC 2391 = 3126 := by pc_by_len

@[simp] theorem pcDual2455 : IPC 2392 = 3127 := by pc_by_len

@[simp] theorem pcDual2456 : IPC 2393 = 3128 := by pc_by_len

@[simp] theorem pcDual2457 : IPC 2394 = 3131 := by pc_by_len

@[simp] theorem pcDual2458 : IPC 2395 = 3132 := by pc_by_len

@[simp] theorem pcDual2459 : IPC 2396 = 3133 := by pc_by_len

@[simp] theorem pcDual2460 : IPC 2397 = 3134 := by pc_by_len

@[simp] theorem pcDual2461 : IPC 2398 = 3141 := by pc_by_len

@[simp] theorem pcDual2462 : IPC 2398 = 3141 := by pc_by_len

@[simp] theorem pcDual2463 : IPC 2398 = 3141 := by pc_by_len

@[simp] theorem pcDual2464 : IPC 2399 = 3142 := by pc_by_len

@[simp] theorem pcDual2465 : IPC 2400 = 3145 := by pc_by_len

@[simp] theorem pcDual8548 : IPC 8212 = 10692 := by pc_by_len

@[simp] theorem pcDual8549 : IPC 8212 = 10692 := by pc_by_len

@[simp] theorem pcDual8550 : IPC 8212 = 10692 := by pc_by_len

@[simp] theorem pcDual8551 : IPC 8213 = 10693 := by pc_by_len

@[simp] theorem pcDual8552 : IPC 8214 = 10694 := by pc_by_len

@[simp] theorem pcDual8553 : IPC 8215 = 10697 := by pc_by_len

@[simp] theorem pcDual8554 : IPC 8216 = 10700 := by pc_by_len

@[simp] theorem pcDual8555 : IPC 8217 = 10701 := by pc_by_len

@[simp] theorem pcDual8559 : IPC 8218 = 10704 := by pc_by_len

@[simp] theorem pcDual8560 : IPC 8219 = 10705 := by pc_by_len

@[simp] theorem pcDual8561 : IPC 8220 = 10706 := by pc_by_len

@[simp] theorem pcDual8562 : IPC 8221 = 10707 := by pc_by_len

@[simp] theorem pcDual8563 : IPC 8222 = 10708 := by pc_by_len

@[simp] theorem pcDual8564 : IPC 8223 = 10709 := by pc_by_len

@[simp] theorem pcDual8565 : IPC 8224 = 10712 := by pc_by_len

@[simp] theorem pcDual8566 : IPC 8225 = 10713 := by pc_by_len

@[simp] theorem pcDual8567 : IPC 8226 = 10714 := by pc_by_len

@[simp] theorem pcDual8568 : IPC 8227 = 10717 := by pc_by_len

@[simp] theorem pcDual8569 : IPC 8228 = 10718 := by pc_by_len

@[simp] theorem pcDual8570 : IPC 8229 = 10719 := by pc_by_len

@[simp] theorem pcDual8571 : IPC 8230 = 10720 := by pc_by_len

@[simp] theorem pcDual8572 : IPC 8231 = 10721 := by pc_by_len

@[simp] theorem pcDual8573 : IPC 8232 = 10722 := by pc_by_len

@[simp] theorem pcDual8574 : IPC 8233 = 10723 := by pc_by_len

@[simp] theorem pcDual8575 : IPC 8234 = 10724 := by pc_by_len

@[simp] theorem pcDual8576 : IPC 8235 = 10725 := by pc_by_len

@[simp] theorem pcDual8577 : IPC 8236 = 10726 := by pc_by_len

@[simp] theorem pcDual8578 : IPC 8237 = 10727 := by pc_by_len

@[simp] theorem pcDual8579 : IPC 8238 = 10728 := by pc_by_len

@[simp] theorem pcDual8580 : IPC 8239 = 10729 := by pc_by_len

@[simp] theorem pcDual8581 : IPC 8240 = 10730 := by pc_by_len

@[simp] theorem pcDual8582 : IPC 8241 = 10731 := by pc_by_len

@[simp] theorem pcDual8583 : IPC 8242 = 10732 := by pc_by_len

@[simp] theorem pcDual8584 : IPC 8243 = 10733 := by pc_by_len

@[simp] theorem pcDual8585 : IPC 8244 = 10734 := by pc_by_len

@[simp] theorem pcDual8586 : IPC 8245 = 10736 := by pc_by_len

@[simp] theorem pcDual8587 : IPC 8246 = 10737 := by pc_by_len

@[simp] theorem pcDual8588 : IPC 8247 = 10738 := by pc_by_len

@[simp] theorem pcDual8589 : IPC 8248 = 10739 := by pc_by_len

@[simp] theorem pcDual8590 : IPC 8249 = 10740 := by pc_by_len

@[simp] theorem pcDual8591 : IPC 8250 = 10741 := by pc_by_len

@[simp] theorem pcDual8592 : IPC 8251 = 10742 := by pc_by_len

@[simp] theorem pcDual8593 : IPC 8252 = 10745 := by pc_by_len

@[simp] theorem pcDual8594 : IPC 8253 = 10746 := by pc_by_len

@[simp] theorem pcDual8595 : IPC 8254 = 10747 := by pc_by_len

@[simp] theorem pcDual8596 : IPC 8255 = 10748 := by pc_by_len

@[simp] theorem pcDual8597 : IPC 8256 = 10749 := by pc_by_len

@[simp] theorem pcDual8598 : IPC 8257 = 10750 := by pc_by_len

@[simp] theorem pcDual8600 : IPC 8258 = 10783 := by pc_by_len

@[simp] theorem pcDual8601 : IPC 8259 = 10784 := by pc_by_len

@[simp] theorem pcDual8602 : IPC 8260 = 10785 := by pc_by_len

@[simp] theorem pcDual8603 : IPC 8261 = 10786 := by pc_by_len

@[simp] theorem pcDual8604 : IPC 8262 = 10787 := by pc_by_len

@[simp] theorem pcDual8605 : IPC 8263 = 10788 := by pc_by_len

@[simp] theorem pcDual8606 : IPC 8264 = 10789 := by pc_by_len

@[simp] theorem pcDual8607 : IPC 8265 = 10790 := by pc_by_len

@[simp] theorem pcDual8608 : IPC 8266 = 10791 := by pc_by_len

@[simp] theorem pcDual8609 : IPC 8267 = 10792 := by pc_by_len

@[simp] theorem pcDual8610 : IPC 8268 = 10793 := by pc_by_len

@[simp] theorem pcDual8611 : IPC 8269 = 10794 := by pc_by_len

@[simp] theorem pcDual8612 : IPC 8270 = 10795 := by pc_by_len

@[simp] theorem pcDual8613 : IPC 8271 = 10796 := by pc_by_len

@[simp] theorem pcDual8614 : IPC 8272 = 10797 := by pc_by_len

@[simp] theorem pcDual8615 : IPC 8273 = 10800 := by pc_by_len

@[simp] theorem pcDual8616 : IPC 8274 = 10801 := by pc_by_len

@[simp] theorem pcDual8617 : IPC 8275 = 10802 := by pc_by_len

@[simp] theorem pcDual8618 : IPC 8276 = 10803 := by pc_by_len

@[simp] theorem pcDual8619 : IPC 8277 = 10804 := by pc_by_len

@[simp] theorem pcDual8620 : IPC 8278 = 10805 := by pc_by_len

@[simp] theorem pcDual8621 : IPC 8279 = 10806 := by pc_by_len

@[simp] theorem pcDual8622 : IPC 8280 = 10807 := by pc_by_len

@[simp] theorem pcDual8623 : IPC 8281 = 10808 := by pc_by_len

@[simp] theorem pcDual8624 : IPC 8282 = 10809 := by pc_by_len

@[simp] theorem pcDual8625 : IPC 8283 = 10810 := by pc_by_len

@[simp] theorem pcDual8626 : IPC 8284 = 10811 := by pc_by_len

@[simp] theorem pcDual8627 : IPC 8285 = 10812 := by pc_by_len

@[simp] theorem pcDual8628 : IPC 8286 = 10813 := by pc_by_len

@[simp] theorem pcDual8629 : IPC 8287 = 10814 := by pc_by_len

@[simp] theorem pcDual8630 : IPC 8288 = 10815 := by pc_by_len

@[simp] theorem pcDual8631 : IPC 8289 = 10816 := by pc_by_len

@[simp] theorem pcDual8632 : IPC 8290 = 10817 := by pc_by_len

@[simp] theorem pcDual8633 : IPC 8291 = 10818 := by pc_by_len

@[simp] theorem pcDual8634 : IPC 8292 = 10819 := by pc_by_len

@[simp] theorem pcDual8635 : IPC 8293 = 10820 := by pc_by_len

@[simp] theorem pcDual8636 : IPC 8294 = 10821 := by pc_by_len

@[simp] theorem pcDual8637 : IPC 8295 = 10824 := by pc_by_len

@[simp] theorem pcDual8638 : IPC 8296 = 10825 := by pc_by_len

@[simp] theorem pcDual8639 : IPC 8297 = 10826 := by pc_by_len

@[simp] theorem pcDual8640 : IPC 8298 = 10827 := by pc_by_len

@[simp] theorem pcDual8641 : IPC 8299 = 10828 := by pc_by_len

@[simp] theorem pcDual8642 : IPC 8300 = 10831 := by pc_by_len

@[simp] theorem pcDual8643 : IPC 8301 = 10832 := by pc_by_len

@[simp] theorem pcDual8644 : IPC 8302 = 10833 := by pc_by_len

@[simp] theorem pcDual8645 : IPC 8303 = 10834 := by pc_by_len

@[simp] theorem pcDual8646 : IPC 8304 = 10835 := by pc_by_len

@[simp] theorem pcDual8647 : IPC 8305 = 10836 := by pc_by_len

@[simp] theorem pcDual8648 : IPC 8306 = 10837 := by pc_by_len

@[simp] theorem pcDual8649 : IPC 8307 = 10838 := by pc_by_len

@[simp] theorem pcDual8650 : IPC 8308 = 10839 := by pc_by_len

@[simp] theorem pcDual8651 : IPC 8309 = 10840 := by pc_by_len

@[simp] theorem pcDual8652 : IPC 8310 = 10841 := by pc_by_len

@[simp] theorem pcDual8653 : IPC 8311 = 10842 := by pc_by_len

@[simp] theorem pcDual8654 : IPC 8312 = 10843 := by pc_by_len

@[simp] theorem pcDual8655 : IPC 8313 = 10844 := by pc_by_len

@[simp] theorem pcDual8656 : IPC 8314 = 10845 := by pc_by_len

@[simp] theorem pcDual8657 : IPC 8315 = 10846 := by pc_by_len

@[simp] theorem pcDual8658 : IPC 8316 = 10847 := by pc_by_len

@[simp] theorem pcDual8659 : IPC 8317 = 10848 := by pc_by_len

@[simp] theorem pcDual8660 : IPC 8318 = 10849 := by pc_by_len

@[simp] theorem pcDual8661 : IPC 8319 = 10850 := by pc_by_len

@[simp] theorem pcDual8662 : IPC 8320 = 10851 := by pc_by_len

@[simp] theorem pcDual8663 : IPC 8321 = 10852 := by pc_by_len

@[simp] theorem pcDual8664 : IPC 8322 = 10853 := by pc_by_len

@[simp] theorem pcDual8665 : IPC 8323 = 10856 := by pc_by_len

@[simp] theorem pcDual8666 : IPC 8324 = 10857 := by pc_by_len

@[simp] theorem pcDual8667 : IPC 8325 = 10858 := by pc_by_len

@[simp] theorem pcDual8668 : IPC 8326 = 10859 := by pc_by_len

@[simp] theorem pcDual8669 : IPC 8327 = 10860 := by pc_by_len

@[simp] theorem pcDual8670 : IPC 8328 = 10863 := by pc_by_len

@[simp] theorem pcDual8671 : IPC 8329 = 10864 := by pc_by_len

@[simp] theorem pcDual8672 : IPC 8330 = 10865 := by pc_by_len

@[simp] theorem pcDual8673 : IPC 8331 = 10866 := by pc_by_len

@[simp] theorem pcDual8674 : IPC 8332 = 10867 := by pc_by_len

@[simp] theorem pcDual8675 : IPC 8333 = 10868 := by pc_by_len

@[simp] theorem pcDual8676 : IPC 8334 = 10869 := by pc_by_len

@[simp] theorem pcDual8677 : IPC 8335 = 10870 := by pc_by_len

@[simp] theorem pcDual8678 : IPC 8336 = 10871 := by pc_by_len

@[simp] theorem pcDual8679 : IPC 8337 = 10874 := by pc_by_len

@[simp] theorem pcDual8680 : IPC 8338 = 10875 := by pc_by_len

@[simp] theorem pcDual8681 : IPC 8339 = 10876 := by pc_by_len

@[simp] theorem pcDual8682 : IPC 8340 = 10877 := by pc_by_len

@[simp] theorem pcDual8683 : IPC 8341 = 10878 := by pc_by_len

@[simp] theorem pcDual8684 : IPC 8342 = 10879 := by pc_by_len

@[simp] theorem pcDual8685 : IPC 8343 = 10880 := by pc_by_len

@[simp] theorem pcDual8686 : IPC 8344 = 10881 := by pc_by_len

@[simp] theorem pcDual8687 : IPC 8345 = 10882 := by pc_by_len

@[simp] theorem pcDual8688 : IPC 8346 = 10883 := by pc_by_len

@[simp] theorem pcDual8689 : IPC 8347 = 10884 := by pc_by_len

@[simp] theorem pcDual8690 : IPC 8348 = 10885 := by pc_by_len

@[simp] theorem pcDual8691 : IPC 8349 = 10886 := by pc_by_len

@[simp] theorem pcDual8692 : IPC 8350 = 10887 := by pc_by_len

@[simp] theorem pcDual8693 : IPC 8351 = 10888 := by pc_by_len

@[simp] theorem pcDual8694 : IPC 8352 = 10889 := by pc_by_len

@[simp] theorem pcDual8695 : IPC 8353 = 10892 := by pc_by_len

@[simp] theorem pcDual8696 : IPC 8354 = 10893 := by pc_by_len

@[simp] theorem pcDual8697 : IPC 8355 = 10894 := by pc_by_len

@[simp] theorem pcDual8698 : IPC 8356 = 10895 := by pc_by_len

@[simp] theorem pcDual8699 : IPC 8357 = 10896 := by pc_by_len

@[simp] theorem pcDual8700 : IPC 8358 = 10899 := by pc_by_len

@[simp] theorem pcDual8701 : IPC 8359 = 10900 := by pc_by_len

@[simp] theorem pcDual8702 : IPC 8360 = 10901 := by pc_by_len

@[simp] theorem pcDual8703 : IPC 8361 = 10902 := by pc_by_len

@[simp] theorem pcDual8704 : IPC 8362 = 10903 := by pc_by_len

@[simp] theorem pcDual8705 : IPC 8363 = 10904 := by pc_by_len

@[simp] theorem pcDual8706 : IPC 8364 = 10905 := by pc_by_len

@[simp] theorem pcDual8707 : IPC 8365 = 10906 := by pc_by_len

@[simp] theorem pcDual8708 : IPC 8366 = 10907 := by pc_by_len

@[simp] theorem pcDual8709 : IPC 8367 = 10910 := by pc_by_len

@[simp] theorem pcDual8710 : IPC 8368 = 10911 := by pc_by_len

@[simp] theorem pcDual8711 : IPC 8369 = 10912 := by pc_by_len

@[simp] theorem pcDual8712 : IPC 8370 = 10913 := by pc_by_len

@[simp] theorem pcDual8713 : IPC 8371 = 10914 := by pc_by_len

@[simp] theorem pcDual8714 : IPC 8372 = 10917 := by pc_by_len

@[simp] theorem pcDual8715 : IPC 8373 = 10918 := by pc_by_len

@[simp] theorem pcDual8716 : IPC 8374 = 10951 := by pc_by_len

@[simp] theorem pcDual8717 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8718 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8719 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8720 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8721 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8722 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8723 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8724 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8725 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8726 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8727 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8728 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8729 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8730 : IPC 8375 = 10952 := by pc_by_len

@[simp] theorem pcDual8731 : IPC 8376 = 10953 := by pc_by_len

@[simp] theorem pcDual8732 : IPC 8377 = 10954 := by pc_by_len

@[simp] theorem pcDual8733 : IPC 8378 = 10955 := by pc_by_len

@[simp] theorem pcDual8734 : IPC 8379 = 10956 := by pc_by_len

@[simp] theorem pcDual8735 : IPC 8380 = 10957 := by pc_by_len

end CycleSubmission.Global.ShiftPCs

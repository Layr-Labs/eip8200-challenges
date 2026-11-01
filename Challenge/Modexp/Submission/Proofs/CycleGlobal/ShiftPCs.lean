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

@[simp] theorem pc2545 : IPC 1873 = 2390 := by pc_by_old eq_old_tail5 1873 pc2545

@[simp] theorem pc2546 : IPC 1874 = 2391 := by pc_by_old eq_old_tail5 1874 pc2546

@[simp] theorem pc2547 : IPC 1875 = 2392 := by pc_by_old eq_old_tail5 1875 pc2547

@[simp] theorem pc2548 : IPC 1876 = 2393 := by pc_by_old eq_old_tail5 1876 pc2548

@[simp] theorem pc2556 : IPC 1877 = 2394 := by pc_by_old eq_old_tail5 1877 pc2555

@[simp] theorem pc2559 : IPC 1878 = 2397 := by pc_by_old eq_old_tail6 1878 pc2559

@[simp] theorem pc2560 : IPC 1879 = 2398 := by pc_by_old eq_old_tail6 1879 pc2560

@[simp] theorem pc2561 : IPC 1880 = 2399 := by pc_by_old eq_old_tail6 1880 pc2561

@[simp] theorem pc2563 : IPC 1881 = 2401 := by pc_by_old eq_old_tail6 1881 pc2563

@[simp] theorem pc2566 : IPC 1882 = 2404 := by pc_by_old eq_old_tail6 1882 pc2566


@[simp] theorem pc2567 : IPC 1883 = 2405 := by pc_by_old eq_old_tail6 1883 pc2567

@[simp] theorem pc2570 : IPC 1884 = 2408 := by pc_by_old eq_old_tail6 1884 pc2570
@[simp] theorem pc2573 : IPC 1885 = 2411 := by pc_by_old eq_old_tail6 1885 pc2573

@[simp] theorem pc2574 : IPC 1886 = 2412 := by pc_by_old eq_old_tail6 1886 pc2574

@[simp] theorem pc2586 : IPC 1897 = 2431 := by pc_by_old eq_old_tail6 1897 pc2586

@[simp] theorem pc2591 : IPC 1903 = 2440 := by pc_by_old eq_old_tail6 1903 pc2591

@[simp] theorem pc2592 : IPC 1904 = 2441 := by pc_by_old eq_old_tail6 1904 pc2592

@[simp] theorem pc2599 : IPC 1932 = 2486 := by pc_by_old eq_old_tail6 1932 pc2599

@[simp] theorem pc2600 : IPC 1933 = 2487 := by pc_by_old eq_old_tail6 1933 pc2600

@[simp] theorem pc2604 : IPC 1935 = 2489 := by pc_by_old eq_old_tail6 1935 pc2604

@[simp] theorem pc2617 : IPC 1938 = 2494 := by pc_by_old eq_old_tail6 1938 pc2617

@[simp] theorem pc2618 : IPC 1939 = 2495 := by pc_by_old eq_old_tail6 1939 pc2618

@[simp] theorem pc2619 : IPC 1940 = 2496 := by pc_by_old eq_old_tail6 1940 pc2619

@[simp] theorem pc2620 : IPC 1941 = 2497 := by pc_by_old eq_old_tail6 1941 pc2620

@[simp] theorem pc2621 : IPC 1942 = 2498 := by pc_by_old eq_old_tail6 1942 pc2621

@[simp] theorem pc2622 : IPC 1943 = 2499 := by pc_by_old eq_old_tail6 1943 pc2622

@[simp] theorem pc2623 : IPC 1944 = 2500 := by pc_by_old eq_old_tail6 1944 pc2623

@[simp] theorem pc2624 : IPC 1945 = 2501 := by pc_by_old eq_old_tail6 1945 pc2624

@[simp] theorem pc2625 : IPC 1946 = 2502 := by pc_by_old eq_old_tail6 1946 pc2625

@[simp] theorem pc2628 : IPC 1947 = 2503 := by pc_by_old eq_old_tail6 1947 pc2628

@[simp] theorem pc2629 : IPC 1948 = 2504 := by pc_by_old eq_old_tail6 1948 pc2629

@[simp] theorem pc2631 : IPC 1949 = 2506 := by pc_by_old eq_old_tail7 1949 pc2631

@[simp] theorem pc2632 : IPC 1950 = 2507 := by pc_by_old eq_old_tail7 1950 pc2632

@[simp] theorem pc2633 : IPC 1951 = 2510 := by pc_by_old eq_old_tail7 1951 pc2633

@[simp] theorem pc2636 : IPC 1952 = 2511 := by pc_by_old eq_old_tail7 1952 pc2636

@[simp] theorem pc2637 : IPC 1953 = 2513 := by pc_by_old eq_old_tail7 1953 pc2637

@[simp] theorem pc2638 : IPC 1954 = 2514 := by pc_by_old eq_old_tail7 1954 pc2638

@[simp] theorem pc2639 : IPC 1955 = 2518 := by pc_by_old eq_old_tail8 1955 pc2640

@[simp] theorem pc2641 : IPC 1956 = 2519 := by pc_by_old eq_old_tail8 1956 pc2641

@[simp] theorem pc2642 : IPC 1957 = 2520 := by pc_by_old eq_old_tail8 1957 pc2642

@[simp] theorem pc2644 : IPC 1958 = 2521 := by pc_by_old eq_old_tail8 1958 pc2644

@[simp] theorem pc2645 : IPC 1959 = 2522 := by pc_by_old eq_old_tail8 1959 pc2645

@[simp] theorem pc2648 : IPC 1960 = 2525 := by pc_by_old eq_old_tail8 1960 pc2648

@[simp] theorem pc2649 : IPC 1961 = 2526 := by pc_by_old eq_old_tail8 1961 pc2649

@[simp] theorem pc2650 : IPC 1962 = 2527 := by pc_by_old eq_old_tail8 1962 pc2650

@[simp] theorem pc2651 : IPC 1963 = 2528 := by pc_by_old eq_old_tail8 1963 pc2651

@[simp] theorem pc2652 : IPC 1964 = 2529 := by pc_by_old eq_old_tail8 1964 pc2652

@[simp] theorem pc2653 : IPC 1965 = 2530 := by pc_by_old eq_old_tail8 1965 pc2653

@[simp] theorem pc2654 : IPC 1966 = 2531 := by pc_by_old eq_old_tail8 1966 pc2654

@[simp] theorem pc2657 : IPC 1967 = 2534 := by pc_by_old eq_old_tail8 1967 pc2657

@[simp] theorem pc2658 : IPC 1968 = 2535 := by pc_by_old eq_old_tail8 1968 pc2658

@[simp] theorem pc2659 : IPC 1969 = 2538 := by pc_by_old eq_old_tail8 1969 pc2659

@[simp] theorem pc2695 : IPC 2015 = 2594 := by pc_by_old eq_old_tail10 2015 pc2695

@[simp] theorem pc2696 : IPC 2016 = 2595 := by pc_by_old eq_old_tail10 2016 pc2696

@[simp] theorem pc2698 : IPC 2017 = 2596 := by pc_by_old eq_old_tail10 2017 pc2698

@[simp] theorem pc2699 : IPC 2018 = 2597 := by pc_by_old eq_old_tail10 2018 pc2699

@[simp] theorem pc2700 : IPC 2019 = 2600 := by pc_by_old eq_old_tail10 2019 pc2700

@[simp] theorem pc2701 : IPC 2020 = 2601 := by pc_by_old eq_old_tail10 2020 pc2701

@[simp] theorem pc2702 : IPC 2021 = 2602 := by pc_by_old eq_old_tail10 2021 pc2702

@[simp] theorem pc2703 : IPC 2022 = 2603 := by pc_by_old eq_old_tail10 2022 pc2703

@[simp] theorem pc2705 : IPC 2023 = 2604 := by pc_by_old eq_old_tail10 2023 pc2705

@[simp] theorem pc2706 : IPC 2024 = 2605 := by pc_by_old eq_old_tail10 2024 pc2706

@[simp] theorem pc2713 : IPC 2028 = 2612 := by pc_by_old eq_old_tail11 2028 pc2713

@[simp] theorem pc3009 : IPC 2218 = 2878 := by pc_by_old eq_old_tail12 2218 pc3009

@[simp] theorem pc3010 : IPC 2219 = 2879 := by pc_by_old eq_old_tail12 2219 pc3010

@[simp] theorem pc3011 : IPC 2220 = 2880 := by pc_by_old eq_old_tail12 2220 pc3011

@[simp] theorem pc3012 : IPC 2221 = 2881 := by pc_by_old eq_old_tail12 2221 pc3012

@[simp] theorem pc3013 : IPC 2222 = 2882 := by pc_by_old eq_old_tail12 2222 pc3013

@[simp] theorem pc2707 : IPC 2025 = 2609 := by pc_by_old eq_old_tail11 2025 pc2710

@[simp] theorem pc2711 : IPC 2026 = 2610 := by pc_by_old eq_old_tail11 2026 pc2711

@[simp] theorem pc2712 : IPC 2027 = 2611 := by pc_by_old eq_old_tail11 2027 pc2712

@[simp] theorem pc3125 : IPC 2314 = 2991 := by pc_by_len







@[simp] theorem pc3171 : IPC 2351 = 3034 := by pc_by_len

@[simp] theorem pc3174 : IPC 2352 = 3037 := by pc_by_len

@[simp] theorem pc3175 : IPC 2353 = 3038 := by pc_by_len

@[simp] theorem pc3176 : IPC 2354 = 3039 := by pc_by_len

@[simp] theorem pc3177 : IPC 2355 = 3040 := by pc_by_len

@[simp] theorem pc3178 : IPC 2356 = 3041 := by pc_by_len

@[simp] theorem pc3179 : IPC 2357 = 3042 := by pc_by_len

@[simp] theorem pc3180 : IPC 2358 = 3043 := by pc_by_len

@[simp] theorem pc3181 : IPC 2359 = 3044 := by pc_by_len

@[simp] theorem pc3182 : IPC 2360 = 3045 := by pc_by_len

@[simp] theorem pc3183 : IPC 2361 = 3046 := by pc_by_len

@[simp] theorem pc3184 : IPC 2362 = 3047 := by pc_by_len

@[simp] theorem pc3185 : IPC 2363 = 3048 := by pc_by_len

@[simp] theorem pc3186 : IPC 2364 = 3049 := by pc_by_len

@[simp] theorem pc3187 : IPC 2365 = 3050 := by pc_by_len

@[simp] theorem pc3188 : IPC 2366 = 3051 := by pc_by_len

@[simp] theorem pc3191 : IPC 2367 = 3054 := by pc_by_len

@[simp] theorem pc3192 : IPC 2368 = 3055 := by pc_by_len




@[simp] theorem pcSaturate2992 : IPC 2299 = 2972 := by pc_by_len

@[simp] theorem pcSaturate2993 : IPC 2300 = 2973 := by pc_by_len

@[simp] theorem earlyExtraPC2883 : IPC 2642 = 3423 := by pc_by_len

@[simp] theorem earlyExtraPC2884 : IPC 2643 = 3424 := by pc_by_len

@[simp] theorem earlyExtraPC2885 : IPC 2644 = 3425 := by pc_by_len

@[simp] theorem earlyExtraPC2886 : IPC 2645 = 3426 := by pc_by_len

@[simp] theorem earlyExtraPC2888 : IPC 2646 = 3427 := by pc_by_len

@[simp] theorem earlyExtraPC2889 : IPC 2647 = 3428 := by pc_by_len

@[simp] theorem earlyExtraPC2890 : IPC 2648 = 3429 := by pc_by_len

@[simp] theorem earlyExtraPC2891 : IPC 2649 = 3432 := by pc_by_len

@[simp] theorem earlyExtraPC2892 : IPC 2650 = 3433 := by pc_by_len

@[simp] theorem earlyExtraPC2893 : IPC 2650 = 3433 := by pc_by_len

@[simp] theorem earlyExtraPC2894 : IPC 2651 = 3436 := by pc_by_len

@[simp] theorem earlyExtraPC2895 : IPC 2652 = 3437 := by pc_by_len

@[simp] theorem earlyExtraPC2896 : IPC 2672 = 3457 := by pc_by_len

@[simp] theorem earlyExtraPC2930 : IPC 2673 = 3458 := by pc_by_len

@[simp] theorem earlyExtraPC2931 : IPC 2674 = 3459 := by pc_by_len

@[simp] theorem earlyExtraPC2932 : IPC 2675 = 3460 := by pc_by_len

@[simp] theorem earlyExtraPC2933 : IPC 2676 = 3461 := by pc_by_len

@[simp] theorem earlyExtraPC2934 : IPC 2677 = 3462 := by pc_by_len

@[simp] theorem earlyExtraPC2935 : IPC 2678 = 3463 := by pc_by_len

@[simp] theorem earlyExtraPC2936 : IPC 2679 = 3466 := by pc_by_len

@[simp] theorem earlyExtraPC2937 : IPC 2680 = 3467 := by pc_by_len

@[simp] theorem earlyExtraPC2938 : IPC 2681 = 3469 := by pc_by_len

@[simp] theorem earlyExtraPC2939 : IPC 2682 = 3470 := by pc_by_len

@[simp] theorem earlyExtraPC2940 : IPC 2683 = 3471 := by pc_by_len

@[simp] theorem earlyExtraPC2941 : IPC 2684 = 3472 := by pc_by_len

@[simp] theorem earlyExtraPC2942 : IPC 2685 = 3473 := by pc_by_len

@[simp] theorem earlyExtraPC2943 : IPC 2686 = 3476 := by pc_by_len


@[simp] theorem pcC3009 : IPC 2356 = 3041 := by pc_by_len

@[simp] theorem pcC3010 : IPC 2357 = 3042 := by pc_by_len

@[simp] theorem pcC3011 : IPC 2358 = 3043 := by pc_by_len

@[simp] theorem pcC3019 : IPC 2365 = 3050 := by pc_by_len

@[simp] theorem pcC3020 : IPC 2366 = 3051 := by pc_by_len

@[simp] theorem pcC3021 : IPC 2367 = 3054 := by pc_by_len



/-! Program counters of the retained-T blocks the head-start table did not carry (generated from the artifact). -/

@[simp] theorem pcT2106 : IPC 1887 = 2413 := by pc_by_old eq_old_tail6 1887 pcT2106

@[simp] theorem pcT2329 : IPC 2302 = 2975 := by pc_by_len

@[simp] theorem pcT2330 : IPC 2303 = 2976 := by pc_by_len

@[simp] theorem pcT2331 : IPC 2304 = 2977 := by pc_by_len

@[simp] theorem pcT2332 : IPC 2305 = 2978 := by pc_by_len

@[simp] theorem pcT2336 : IPC 2309 = 2984 := by pc_by_len

@[simp] theorem pcT2337 : IPC 2310 = 2985 := by pc_by_len

@[simp] theorem pcT2338 : IPC 2311 = 2986 := by pc_by_len

@[simp] theorem pcT2339 : IPC 2312 = 2987 := by pc_by_len

@[simp] theorem pcT2340 : IPC 2313 = 2990 := by pc_by_len

@[simp] theorem pcT2341 : IPC 2314 = 2991 := by pc_by_len

@[simp] theorem pcT2342 : IPC 2315 = 2992 := by pc_by_len

@[simp] theorem pcT2343 : IPC 2316 = 2993 := by pc_by_len

@[simp] theorem pcT2344 : IPC 2317 = 2994 := by pc_by_len

@[simp] theorem pcT2345 : IPC 2318 = 2995 := by pc_by_len

@[simp] theorem pcT2346 : IPC 2319 = 2996 := by pc_by_len

@[simp] theorem pcT2347 : IPC 2320 = 2997 := by pc_by_len

@[simp] theorem pcT2348 : IPC 2321 = 2998 := by pc_by_len

@[simp] theorem pcT2349 : IPC 2322 = 3001 := by pc_by_len

@[simp] theorem pcT2350 : IPC 2323 = 3002 := by pc_by_len

@[simp] theorem pcT2351 : IPC 2324 = 3003 := by pc_by_len

@[simp] theorem pcT2352 : IPC 2325 = 3004 := by pc_by_len

@[simp] theorem pcT2353 : IPC 2326 = 3005 := by pc_by_len

@[simp] theorem pcT2354 : IPC 2327 = 3006 := by pc_by_len

@[simp] theorem pcT2355 : IPC 2328 = 3007 := by pc_by_len

@[simp] theorem pcT2356 : IPC 2329 = 3008 := by pc_by_len

@[simp] theorem pcT2357 : IPC 2330 = 3009 := by pc_by_len

@[simp] theorem pcT2358 : IPC 2331 = 3010 := by pc_by_len

@[simp] theorem pcT2359 : IPC 2332 = 3011 := by pc_by_len

@[simp] theorem pcT2360 : IPC 2333 = 3012 := by pc_by_len

@[simp] theorem pcT2361 : IPC 2334 = 3013 := by pc_by_len

@[simp] theorem pcT2362 : IPC 2335 = 3014 := by pc_by_len

@[simp] theorem pcT2363 : IPC 2336 = 3015 := by pc_by_len

@[simp] theorem pcT2364 : IPC 2337 = 3016 := by pc_by_len

@[simp] theorem pcT2365 : IPC 2338 = 3019 := by pc_by_len

@[simp] theorem pcT2366 : IPC 2339 = 3020 := by pc_by_len

@[simp] theorem pcT2367 : IPC 2340 = 3021 := by pc_by_len

@[simp] theorem pcT2368 : IPC 2341 = 3022 := by pc_by_len

@[simp] theorem pcT2369 : IPC 2342 = 3023 := by pc_by_len

@[simp] theorem pcT2370 : IPC 2343 = 3026 := by pc_by_len

@[simp] theorem pcT2371 : IPC 2344 = 3027 := by pc_by_len

@[simp] theorem pcT2372 : IPC 2345 = 3028 := by pc_by_len

@[simp] theorem pcT2522 : IPC 2368 = 3055 := by pc_by_len

@[simp] theorem pcI2013 : IPC 1831 = 2317 := by pc_by_old eq_old4 1831 pcI2013

@[simp] theorem pcI2014 : IPC 1832 = 2318 := by pc_by_old eq_old4 1832 pcI2014

@[simp] theorem pcI2015 : IPC 1833 = 2319 := by pc_by_old eq_old4 1833 pcI2015

@[simp] theorem pcI2016 : IPC 1834 = 2321 := by pc_by_old eq_old4 1834 pcI2016

@[simp] theorem pcI2017 : IPC 1835 = 2322 := by pc_by_old eq_old4 1835 pcI2017

@[simp] theorem pcI2018 : IPC 1836 = 2325 := by pc_by_old eq_old4 1836 pcI2018

@[simp] theorem pcI2032 : IPC 1839 = 2329 := by pc_by_old eq_old4 1839 pcI2032

@[simp] theorem pcI2033 : IPC 1840 = 2330 := by pc_by_old eq_old4 1840 pcI2033

@[simp] theorem pcI2034 : IPC 1841 = 2332 := by pc_by_old eq_old4 1841 pcI2034

@[simp] theorem pcI2035 : IPC 1842 = 2335 := by pc_by_old eq_old4 1842 pcI2035

@[simp] theorem pcI2036 : IPC 1852 = 2350 := by pc_by_old eq_old4 1852 pcI2036

@[simp] theorem pcI2037 : IPC 1853 = 2351 := by pc_by_old eq_old4 1853 pcI2037

@[simp] theorem pcI2038 : IPC 1854 = 2354 := by pc_by_old eq_old4 1854 pcI2038

@[simp] theorem pcI2039 : IPC 1855 = 2355 := by pc_by_old eq_old4 1855 pcI2039

@[simp] theorem pcI2040 : IPC 1856 = 2356 := by pc_by_old eq_old4 1856 pcI2040

@[simp] theorem pcI2041 : IPC 1857 = 2358 := by pc_by_old eq_old4 1857 pcI2041

@[simp] theorem pcI2042 : IPC 1858 = 2359 := by pc_by_old eq_old4 1858 pcI2042

@[simp] theorem pcI2043 : IPC 1859 = 2363 := by pc_by_old eq_old4 1859 pcI2043

@[simp] theorem pcI2044 : IPC 1860 = 2364 := by pc_by_old eq_old4 1860 pcI2044

@[simp] theorem pcI2045 : IPC 1861 = 2366 := by pc_by_old eq_old4 1861 pcI2045

@[simp] theorem pcI2046 : IPC 1862 = 2367 := by pc_by_old eq_old4 1862 pcI2046

@[simp] theorem pcI2047 : IPC 1863 = 2369 := by pc_by_old eq_old4 1863 pcI2047

@[simp] theorem pcI2048 : IPC 1864 = 2370 := by pc_by_old eq_old4 1864 pcI2048

@[simp] theorem pcI2049 : IPC 1865 = 2373 := by pc_by_old eq_old4 1865 pcI2049

@[simp] theorem pcI2050 : IPC 1866 = 2375 := by pc_by_len

@[simp] theorem pcI2051 : IPC 1867 = 2376 := by pc_by_len

@[simp] theorem pcI2052 : IPC 1867 = 2376 := by pc_by_len

@[simp] theorem pcI2053 : IPC 1868 = 2377 := by pc_by_old eq_old_tail5 1868 pcI2053

@[simp] theorem pcI2054 : IPC 1869 = 2380 := by pc_by_old eq_old_tail5 1869 pcI2054

@[simp] theorem pcI2055 : IPC 1870 = 2383 := by pc_by_old eq_old_tail5 1870 pcI2055

@[simp] theorem pcI2056 : IPC 1871 = 2386 := by pc_by_old eq_old_tail5 1871 pcI2056

@[simp] theorem pcI2057 : IPC 1872 = 2389 := by pc_by_old eq_old_tail5 1872 pcI2057

@[simp] theorem pcI2093 : IPC 1888 = 2414 := by pc_by_old eq_old_tail6 1888 pcI2093

@[simp] theorem pcI2094 : IPC 1889 = 2417 := by pc_by_old eq_old_tail6 1889 pcI2094

@[simp] theorem pcI2095 : IPC 1890 = 2420 := by pc_by_old eq_old_tail6 1890 pcI2095

@[simp] theorem pcI2156 : IPC 1970 = 2539 := by pc_by_old eq_old_tail8 1970 pcI2156

@[simp] theorem pcI2200 : IPC 2029 = 2613 := by pc_by_old eq_old_tail11 2029 pcI2200

@[simp] theorem pcI2201 : IPC 2030 = 2614 := by pc_by_old eq_old_tail11 2030 pcI2201

@[simp] theorem pcI2202 : IPC 2031 = 2615 := by pc_by_old eq_old_tail11 2031 pcI2202

@[simp] theorem pcI2203 : IPC 2032 = 2616 := by pc_by_old eq_old_tail11 2032 pcI2203

@[simp] theorem pcI2204 : IPC 2033 = 2617 := by pc_by_old eq_old_tail11 2033 pcI2204

@[simp] theorem pcI2205 : IPC 2034 = 2618 := by pc_by_old eq_old_tail11 2034 pcI2205

@[simp] theorem pcI2206 : IPC 2035 = 2621 := by pc_by_old eq_old_tail11 2035 pcI2206

@[simp] theorem pcI2207 : IPC 2036 = 2622 := by pc_by_old eq_old_tail11 2036 pcI2207

@[simp] theorem pcI2208 : IPC 2037 = 2625 := by pc_by_old eq_old_tail11 2037 pcI2208

@[simp] theorem pcI2209 : IPC 2038 = 2626 := by pc_by_old eq_old_tail11 2038 pcI2209

@[simp] theorem pcI2210 : IPC 2039 = 2629 := by pc_by_old eq_old_tail11 2039 pcI2210

@[simp] theorem pcI2211 : IPC 2040 = 2630 := by pc_by_old eq_old_tail11 2040 pcI2211

@[simp] theorem pcI2212 : IPC 2041 = 2633 := by pc_by_old eq_old_tail11 2041 pcI2212

@[simp] theorem pcI2213 : IPC 2042 = 2634 := by pc_by_old eq_old_tail11 2042 pcI2213

@[simp] theorem pcI2214 : IPC 2043 = 2637 := by pc_by_old eq_old_tail11 2043 pcI2214

@[simp] theorem pcI2215 : IPC 2044 = 2638 := by pc_by_old eq_old_tail11 2044 pcI2215

@[simp] theorem pcI2216 : IPC 2045 = 2641 := by pc_by_old eq_old_tail11 2045 pcI2216

@[simp] theorem pcI2217 : IPC 2046 = 2642 := by pc_by_old eq_old_tail11 2046 pcI2217

@[simp] theorem pcI2218 : IPC 2047 = 2645 := by pc_by_old eq_old_tail11 2047 pcI2218

@[simp] theorem pcI2219 : IPC 2048 = 2646 := by pc_by_old eq_old_tail11 2048 pcI2219

@[simp] theorem pcI2220 : IPC 2049 = 2649 := by pc_by_old eq_old_tail11 2049 pcI2220

@[simp] theorem pcI2221 : IPC 2050 = 2650 := by pc_by_old eq_old_tail11 2050 pcI2221

@[simp] theorem pcI2222 : IPC 2051 = 2653 := by pc_by_old eq_old_tail11 2051 pcI2222

@[simp] theorem pcI2223 : IPC 2052 = 2654 := by pc_by_old eq_old_tail11 2052 pcI2223

@[simp] theorem pcI2224 : IPC 2053 = 2657 := by pc_by_old eq_old_tail11 2053 pcI2224

@[simp] theorem pcI2225 : IPC 2054 = 2658 := by pc_by_old eq_old_tail11 2054 pcI2225

@[simp] theorem pcI2226 : IPC 2055 = 2661 := by pc_by_old eq_old_tail11 2055 pcI2226

@[simp] theorem pcI2330 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2332 : IPC 2137 = 2787 := by pc_by_old eq_old_tail12 2137 pcI2332

@[simp] theorem pcI2333 : IPC 2138 = 2788 := by pc_by_old eq_old_tail12 2138 pcI2333

@[simp] theorem pcI2334 : IPC 2139 = 2789 := by pc_by_old eq_old_tail12 2139 pcI2334

@[simp] theorem pcI2335 : IPC 2140 = 2790 := by pc_by_old eq_old_tail12 2140 pcI2335

@[simp] theorem pcI2336 : IPC 2141 = 2791 := by pc_by_old eq_old_tail12 2141 pcI2336

@[simp] theorem pcI2337 : IPC 2142 = 2792 := by pc_by_old eq_old_tail12 2142 pcI2337

@[simp] theorem pcI2338 : IPC 2143 = 2793 := by pc_by_old eq_old_tail12 2143 pcI2338

@[simp] theorem pcI2339 : IPC 2144 = 2794 := by pc_by_old eq_old_tail12 2144 pcI2339

@[simp] theorem pcI2340 : IPC 2145 = 2795 := by pc_by_old eq_old_tail12 2145 pcI2340

@[simp] theorem pcI2341 : IPC 2146 = 2798 := by pc_by_old eq_old_tail12 2146 pcI2341

@[simp] theorem pcI2342 : IPC 2147 = 2799 := by pc_by_old eq_old_tail12 2147 pcI2342

@[simp] theorem pcI2343 : IPC 2148 = 2800 := by pc_by_old eq_old_tail12 2148 pcI2343

@[simp] theorem pcI2344 : IPC 2149 = 2801 := by pc_by_old eq_old_tail12 2149 pcI2344

@[simp] theorem pcI2345 : IPC 2150 = 2802 := by pc_by_old eq_old_tail12 2150 pcI2345

@[simp] theorem pcI2346 : IPC 2151 = 2803 := by pc_by_old eq_old_tail12 2151 pcI2346

@[simp] theorem pcI2347 : IPC 2152 = 2804 := by pc_by_old eq_old_tail12 2152 pcI2347

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

@[simp] theorem pcI2360 : IPC 2153 = 2805 := by pc_by_old eq_old_tail12 2153 pcI2360

@[simp] theorem pcI2361 : IPC 2154 = 2806 := by pc_by_old eq_old_tail12 2154 pcI2361

@[simp] theorem pcI2362 : IPC 2155 = 2807 := by pc_by_old eq_old_tail12 2155 pcI2362

@[simp] theorem pcI2363 : IPC 2156 = 2808 := by pc_by_old eq_old_tail12 2156 pcI2363

@[simp] theorem pcI2364 : IPC 2157 = 2809 := by pc_by_old eq_old_tail12 2157 pcI2364

@[simp] theorem pcI2365 : IPC 2158 = 2810 := by pc_by_old eq_old_tail12 2158 pcI2365

@[simp] theorem pcI2366 : IPC 2159 = 2811 := by pc_by_old eq_old_tail12 2159 pcI2366

@[simp] theorem pcI2367 : IPC 2160 = 2812 := by pc_by_old eq_old_tail12 2160 pcI2367

@[simp] theorem pcI2368 : IPC 2161 = 2813 := by pc_by_old eq_old_tail12 2161 pcI2368

@[simp] theorem pcI2369 : IPC 2162 = 2814 := by pc_by_old eq_old_tail12 2162 pcI2369

@[simp] theorem pcI2370 : IPC 2163 = 2815 := by pc_by_old eq_old_tail12 2163 pcI2370

@[simp] theorem pcI2371 : IPC 2164 = 2816 := by pc_by_old eq_old_tail12 2164 pcI2371

@[simp] theorem pcI2372 : IPC 2165 = 2817 := by pc_by_old eq_old_tail12 2165 pcI2372

@[simp] theorem pcI2373 : IPC 2166 = 2818 := by pc_by_old eq_old_tail12 2166 pcI2373

@[simp] theorem pcI2374 : IPC 2167 = 2819 := by pc_by_old eq_old_tail12 2167 pcI2374

@[simp] theorem pcI2375 : IPC 2168 = 2822 := by pc_by_old eq_old_tail12 2168 pcI2375

@[simp] theorem pcI2376 : IPC 2169 = 2823 := by pc_by_old eq_old_tail12 2169 pcI2376

@[simp] theorem pcI2377 : IPC 2170 = 2824 := by pc_by_old eq_old_tail12 2170 pcI2377

@[simp] theorem pcI2378 : IPC 2171 = 2825 := by pc_by_old eq_old_tail12 2171 pcI2378

@[simp] theorem pcI2379 : IPC 2172 = 2826 := by pc_by_old eq_old_tail12 2172 pcI2379

@[simp] theorem pcI2380 : IPC 2173 = 2829 := by pc_by_old eq_old_tail12 2173 pcI2380

@[simp] theorem pcI2381 : IPC 2174 = 2830 := by pc_by_old eq_old_tail12 2174 pcI2381

@[simp] theorem pcI2382 : IPC 2175 = 2831 := by pc_by_old eq_old_tail12 2175 pcI2382

@[simp] theorem pcI2383 : IPC 2176 = 2832 := by pc_by_old eq_old_tail12 2176 pcI2383

@[simp] theorem pcI2384 : IPC 2177 = 2833 := by pc_by_old eq_old_tail12 2177 pcI2384

@[simp] theorem pcI2385 : IPC 2178 = 2834 := by pc_by_old eq_old_tail12 2178 pcI2385

@[simp] theorem pcI2386 : IPC 2179 = 2835 := by pc_by_old eq_old_tail12 2179 pcI2386

@[simp] theorem pcI2387 : IPC 2180 = 2836 := by pc_by_old eq_old_tail12 2180 pcI2387

@[simp] theorem pcI2388 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2389 : IPC 2181 = 2837 := by pc_by_old eq_old_tail12 2181 pcI2389

@[simp] theorem pcI2390 : IPC 2182 = 2838 := by pc_by_old eq_old_tail12 2182 pcI2390

@[simp] theorem pcI2391 : IPC 2183 = 2839 := by pc_by_old eq_old_tail12 2183 pcI2391

@[simp] theorem pcI2392 : IPC 2184 = 2840 := by pc_by_old eq_old_tail12 2184 pcI2392

@[simp] theorem pcI2393 : IPC 2185 = 2841 := by pc_by_old eq_old_tail12 2185 pcI2393

@[simp] theorem pcI2394 : IPC 2186 = 2842 := by pc_by_old eq_old_tail12 2186 pcI2394

@[simp] theorem pcI2395 : IPC 2187 = 2843 := by pc_by_old eq_old_tail12 2187 pcI2395

@[simp] theorem pcI2396 : IPC 2188 = 2844 := by pc_by_old eq_old_tail12 2188 pcI2396

@[simp] theorem pcI2397 : IPC 2189 = 2845 := by pc_by_old eq_old_tail12 2189 pcI2397

@[simp] theorem pcI2398 : IPC 2190 = 2846 := by pc_by_old eq_old_tail12 2190 pcI2398

@[simp] theorem pcI2399 : IPC 2191 = 2847 := by pc_by_old eq_old_tail12 2191 pcI2399

@[simp] theorem pcI2400 : IPC 2192 = 2848 := by pc_by_old eq_old_tail12 2192 pcI2400

@[simp] theorem pcI2401 : IPC 2193 = 2849 := by pc_by_old eq_old_tail12 2193 pcI2401

@[simp] theorem pcI2402 : IPC 2194 = 2850 := by pc_by_old eq_old_tail12 2194 pcI2402

@[simp] theorem pcI2403 : IPC 2195 = 2851 := by pc_by_old eq_old_tail12 2195 pcI2403

@[simp] theorem pcI2404 : IPC 2196 = 2854 := by pc_by_old eq_old_tail12 2196 pcI2404

@[simp] theorem pcI2405 : IPC 2197 = 2855 := by pc_by_old eq_old_tail12 2197 pcI2405

@[simp] theorem pcI2406 : IPC 2198 = 2856 := by pc_by_old eq_old_tail12 2198 pcI2406

@[simp] theorem pcI2407 : IPC 2199 = 2857 := by pc_by_old eq_old_tail12 2199 pcI2407

@[simp] theorem pcI2408 : IPC 2200 = 2858 := by pc_by_old eq_old_tail12 2200 pcI2408

@[simp] theorem pcI2409 : IPC 2201 = 2861 := by pc_by_old eq_old_tail12 2201 pcI2409

@[simp] theorem pcI2410 : IPC 2202 = 2862 := by pc_by_old eq_old_tail12 2202 pcI2410

@[simp] theorem pcI2411 : IPC 2203 = 2863 := by pc_by_old eq_old_tail12 2203 pcI2411

@[simp] theorem pcI2412 : IPC 2204 = 2864 := by pc_by_old eq_old_tail12 2204 pcI2412

@[simp] theorem pcI2413 : IPC 2205 = 2865 := by pc_by_old eq_old_tail12 2205 pcI2413

@[simp] theorem pcI2414 : IPC 2206 = 2866 := by pc_by_old eq_old_tail12 2206 pcI2414

@[simp] theorem pcI2415 : IPC 2207 = 2867 := by pc_by_old eq_old_tail12 2207 pcI2415

@[simp] theorem pcI2416 : IPC 2208 = 2868 := by pc_by_old eq_old_tail12 2208 pcI2416

@[simp] theorem pcI2417 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2418 : IPC 2209 = 2869 := by pc_by_old eq_old_tail12 2209 pcI2418

@[simp] theorem pcI2419 : IPC 2210 = 2870 := by pc_by_old eq_old_tail12 2210 pcI2419

@[simp] theorem pcI2420 : IPC 2211 = 2871 := by pc_by_old eq_old_tail12 2211 pcI2420

@[simp] theorem pcI2421 : IPC 2212 = 2872 := by pc_by_old eq_old_tail12 2212 pcI2421

@[simp] theorem pcI2422 : IPC 2213 = 2873 := by pc_by_old eq_old_tail12 2213 pcI2422

@[simp] theorem pcI2423 : IPC 2214 = 2874 := by pc_by_old eq_old_tail12 2214 pcI2423

@[simp] theorem pcI2424 : IPC 2215 = 2875 := by pc_by_old eq_old_tail12 2215 pcI2424

@[simp] theorem pcI2425 : IPC 2216 = 2876 := by pc_by_old eq_old_tail12 2216 pcI2425

@[simp] theorem pcI2426 : IPC 2217 = 2877 := by pc_by_old eq_old_tail12 2217 pcI2426

@[simp] theorem pcI2432 : IPC 2223 = 2883 := by pc_by_old eq_old_tail12 2223 pcI2432

@[simp] theorem pcI2433 : IPC 2224 = 2886 := by pc_by_old eq_old_tail12 2224 pcI2433

@[simp] theorem pcI2434 : IPC 2225 = 2887 := by pc_by_old eq_old_tail12 2225 pcI2434

@[simp] theorem pcI2435 : IPC 2226 = 2888 := by pc_by_old eq_old_tail12 2226 pcI2435

@[simp] theorem pcI2436 : IPC 2227 = 2889 := by pc_by_old eq_old_tail12 2227 pcI2436

@[simp] theorem pcI2437 : IPC 2228 = 2890 := by pc_by_old eq_old_tail12 2228 pcI2437

@[simp] theorem pcI2438 : IPC 2229 = 2893 := by pc_by_old eq_old_tail12 2229 pcI2438

@[simp] theorem pcI2439 : IPC 2230 = 2894 := by pc_by_old eq_old_tail12 2230 pcI2439

@[simp] theorem pcI2440 : IPC 2231 = 2895 := by pc_by_old eq_old_tail12 2231 pcI2440

@[simp] theorem pcI2441 : IPC 2232 = 2896 := by pc_by_old eq_old_tail12 2232 pcI2441

@[simp] theorem pcI2442 : IPC 2233 = 2897 := by pc_by_old eq_old_tail12 2233 pcI2442

@[simp] theorem pcI2443 : IPC 2234 = 2898 := by pc_by_old eq_old_tail12 2234 pcI2443

@[simp] theorem pcI2444 : IPC 2235 = 2899 := by pc_by_old eq_old_tail12 2235 pcI2444

@[simp] theorem pcI2445 : IPC 2236 = 2900 := by pc_by_old eq_old_tail12 2236 pcI2445

@[simp] theorem pcI2446 : IPC 2237 = 2901 := by pc_by_old eq_old_tail12 2237 pcI2446

@[simp] theorem pcI2447 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2448 : IPC 2238 = 2902 := by pc_by_len

@[simp] theorem pcI2449 : IPC 2239 = 2903 := by pc_by_len

@[simp] theorem pcI2450 : IPC 2240 = 2904 := by pc_by_len

@[simp] theorem pcI2451 : IPC 2241 = 2905 := by pc_by_len

@[simp] theorem pcI2452 : IPC 2242 = 2906 := by pc_by_len

@[simp] theorem pcI2453 : IPC 2243 = 2907 := by pc_by_len

@[simp] theorem pcI2454 : IPC 2244 = 2908 := by pc_by_len

@[simp] theorem pcI2455 : IPC 2245 = 2909 := by pc_by_len

@[simp] theorem pcI2456 : IPC 2246 = 2910 := by pc_by_len

@[simp] theorem pcI2457 : IPC 2247 = 2911 := by pc_by_len

@[simp] theorem pcI2458 : IPC 2248 = 2912 := by pc_by_len

@[simp] theorem pcI2459 : IPC 2249 = 2913 := by pc_by_len

@[simp] theorem pcI2460 : IPC 2250 = 2914 := by pc_by_len

@[simp] theorem pcI2461 : IPC 2251 = 2915 := by pc_by_len

@[simp] theorem pcI2462 : IPC 2252 = 2918 := by pc_by_len

@[simp] theorem pcI2463 : IPC 2253 = 2919 := by pc_by_len

@[simp] theorem pcI2464 : IPC 2254 = 2920 := by pc_by_len

@[simp] theorem pcI2465 : IPC 2255 = 2921 := by pc_by_len

@[simp] theorem pcI2466 : IPC 2256 = 2922 := by pc_by_len

@[simp] theorem pcI2467 : IPC 2257 = 2925 := by pc_by_len

@[simp] theorem pcI2468 : IPC 2258 = 2926 := by pc_by_len

@[simp] theorem pcI2469 : IPC 2259 = 2927 := by pc_by_len

@[simp] theorem pcI2470 : IPC 2260 = 2928 := by pc_by_len

@[simp] theorem pcI2471 : IPC 2261 = 2929 := by pc_by_len

@[simp] theorem pcI2472 : IPC 2262 = 2930 := by pc_by_len

@[simp] theorem pcI2473 : IPC 2263 = 2931 := by pc_by_len

@[simp] theorem pcI2474 : IPC 2264 = 2932 := by pc_by_len

@[simp] theorem pcI2475 : IPC 2265 = 2933 := by pc_by_len

@[simp] theorem pcI2476 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2477 : IPC 2266 = 2934 := by pc_by_len

@[simp] theorem pcI2478 : IPC 2267 = 2935 := by pc_by_len

@[simp] theorem pcI2479 : IPC 2268 = 2936 := by pc_by_len

@[simp] theorem pcI2480 : IPC 2269 = 2937 := by pc_by_len

@[simp] theorem pcI2481 : IPC 2270 = 2938 := by pc_by_len

@[simp] theorem pcI2482 : IPC 2271 = 2939 := by pc_by_len

@[simp] theorem pcI2483 : IPC 2272 = 2940 := by pc_by_len

@[simp] theorem pcI2484 : IPC 2273 = 2941 := by pc_by_len

@[simp] theorem pcI2485 : IPC 2274 = 2942 := by pc_by_len

@[simp] theorem pcI2486 : IPC 2275 = 2943 := by pc_by_len

@[simp] theorem pcI2487 : IPC 2276 = 2944 := by pc_by_len

@[simp] theorem pcI2488 : IPC 2277 = 2945 := by pc_by_len

@[simp] theorem pcI2489 : IPC 2278 = 2946 := by pc_by_len

@[simp] theorem pcI2490 : IPC 2279 = 2947 := by pc_by_len

@[simp] theorem pcI2492 : IPC 2280 = 2951 := by pc_by_len

@[simp] theorem pcI2493 : IPC 2281 = 2952 := by pc_by_len

@[simp] theorem pcI2494 : IPC 2282 = 2953 := by pc_by_len

@[simp] theorem pcI2495 : IPC 2283 = 2954 := by pc_by_len

@[simp] theorem pcI2496 : IPC 2284 = 2955 := by pc_by_len

@[simp] theorem pcI2497 : IPC 2285 = 2958 := by pc_by_len

@[simp] theorem pcI2498 : IPC 2286 = 2959 := by pc_by_len

@[simp] theorem pcI2499 : IPC 2287 = 2960 := by pc_by_len

@[simp] theorem pcI2500 : IPC 2288 = 2961 := by pc_by_len

@[simp] theorem pcI2501 : IPC 2289 = 2962 := by pc_by_len

@[simp] theorem pcI2502 : IPC 2290 = 2963 := by pc_by_len

@[simp] theorem pcI2503 : IPC 2291 = 2964 := by pc_by_len

@[simp] theorem pcI2504 : IPC 2292 = 2965 := by pc_by_len

@[simp] theorem pcI2505 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2506 : IPC 2293 = 2966 := by pc_by_len

@[simp] theorem pcI2507 : IPC 2294 = 2967 := by pc_by_len

@[simp] theorem pcI2508 : IPC 2295 = 2968 := by pc_by_len

@[simp] theorem pcI2509 : IPC 2296 = 2969 := by pc_by_len

@[simp] theorem pcI2510 : IPC 2297 = 2970 := by pc_by_len

@[simp] theorem pcI2511 : IPC 2298 = 2971 := by pc_by_len

@[simp] theorem pcI2514 : IPC 2301 = 2974 := by pc_by_len

@[simp] theorem pcI2519 : IPC 2306 = 2979 := by pc_by_len

@[simp] theorem pcI2520 : IPC 2307 = 2980 := by pc_by_len

@[simp] theorem pcI2521 : IPC 2308 = 2983 := by pc_by_len

@[simp] theorem pcI2559 : IPC 2346 = 3029 := by pc_by_len

@[simp] theorem pcI2560 : IPC 2347 = 3030 := by pc_by_len

@[simp] theorem pcI2561 : IPC 2348 = 3031 := by pc_by_len

@[simp] theorem pcI2562 : IPC 2349 = 3032 := by pc_by_len

@[simp] theorem pcI2563 : IPC 2350 = 3033 := by pc_by_len

@[simp] theorem pcI2564 : IPC 0 = 0 := by pc_by_len

@[simp] theorem pcI2565 : IPC 2351 = 3034 := by pc_by_len

@[simp] theorem pcI2566 : IPC 2352 = 3037 := by pc_by_len

@[simp] theorem pcI2585 : IPC 2369 = 3056 := by pc_by_len

/-! ## The straight-line negation and the inline Newton chain (negun, inl693) -/

@[simp] theorem negunPC0 (i : Nat) (hi : 1843 ≤ i) (hii : i ≤ 1851) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2336,2337,2339,2340,2341,2342,2345,2346,2349] : List Nat)[i - 1843]! := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 i (by omega) (by omega)]
  have h := Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.negunPC0 (i+4) (by omega) (by omega)
  simpa only [show i+4-1847 = i-1843 by omega] using h

@[simp] theorem negunPC1 (i : Nat) (hi : 1891 ≤ i) (hii : i ≤ 1937) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2421,2422,2424,2425,2428,2429,2431,2432,2433,2434,2437,2438,2440,2441,2442,2445,2446,2448,2449,2450,2453,2454,2456,2457,2458,2461,2462,2464,2465,2466,2469,2470,2471,2473,2474,2475,2478,2479,2481,2482,2483,2486,2487,2488,2489,2490,2493] : List Nat)[i - 1891]! := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 i (by omega) (by omega)]
  have h := Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.negunPC1 (i+6) (by omega) (by omega)
  simpa only [show i+6-1897 = i-1891 by omega] using h

@[simp] theorem negunPC2 (i : Nat) (hi : 1971 ≤ i) (hii : i ≤ 2014) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([2540,2541,2542,2543,2544,2546,2547,2549,2550,2551,2552,2553,2555,2556,2557,2558,2559,2560,2562,2563,2564,2565,2566,2567,2569,2570,2571,2572,2573,2574,2576,2577,2578,2579,2580,2581,2583,2584,2585,2586,2587,2588,2592,2593] : List Nat)[i - 1971]! := by
  by_cases h0 : i ≤ 2012
  · have hl0 : 1971 ≤ i := by omega
    have hh0 : i ≤ 2012 := by omega
    rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 i (by omega) (by omega),
      Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.negunPC2 (i+8) (by omega) (by omega)]
    interval_cases i <;> rfl
  · have hl1 : 2013 ≤ i := by omega
    have hh1 : i ≤ 2014 := by omega
    rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 i (by omega) (by omega),
      Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.negunPC2 (i+10) (by omega) (by omega)]
    interval_cases i <;> rfl

/-! ## Directly stated pcs: E5 and the eight-limb loop head (2056 .. 2146), the bottom test,
the exit / E3 phase blocks and the repair loop (2381 .. 2465), and the appended four-limb
loop head (8548 .. 8610). -/

@[simp] theorem pcDual2056 : IPC 2056 = 2662 := by pc_by_len

@[simp] theorem pcDual2057 : IPC 2057 = 2663 := by pc_by_len

@[simp] theorem pcDual2065 : IPC 2058 = 2677 := by pc_by_len

@[simp] theorem pcDual2066 : IPC 2059 = 2678 := by pc_by_len

@[simp] theorem pcDual2067 : IPC 2060 = 2680 := by pc_by_len

@[simp] theorem pcDual2068 : IPC 2061 = 2681 := by pc_by_len

@[simp] theorem pcDual2069 : IPC 2062 = 2682 := by pc_by_len

@[simp] theorem pcDual2070 : IPC 2063 = 2684 := by pc_by_len

@[simp] theorem pcDual2071 : IPC 2064 = 2685 := by pc_by_len

@[simp] theorem pcDual2072 : IPC 2065 = 2688 := by pc_by_len

@[simp] theorem pcDual2073 : IPC 2066 = 2689 := by pc_by_len

@[simp] theorem pcDual2074 : IPC 2067 = 2690 := by pc_by_len

@[simp] theorem pcDual2075 : IPC 2068 = 2691 := by pc_by_len

@[simp] theorem pcDual2076 : IPC 2069 = 2692 := by pc_by_len

@[simp] theorem pcDual2077 : IPC 2070 = 2694 := by pc_by_len

@[simp] theorem pcDual2078 : IPC 2071 = 2695 := by pc_by_len

@[simp] theorem pcDual2079 : IPC 2072 = 2696 := by pc_by_len

@[simp] theorem pcDual2080 : IPC 2073 = 2697 := by pc_by_len

@[simp] theorem pcDual2081 : IPC 2074 = 2700 := by pc_by_len

@[simp] theorem pcDual2082 : IPC 2075 = 2701 := by pc_by_len

@[simp] theorem pcDual2083 : IPC 2076 = 2702 := by pc_by_len

@[simp] theorem pcDual2084 : IPC 2077 = 2703 := by pc_by_len

@[simp] theorem pcDual2085 : IPC 2078 = 2706 := by pc_by_len

@[simp] theorem pcDual2086 : IPC 2079 = 2707 := by pc_by_len

@[simp] theorem pcDual2087 : IPC 2080 = 2710 := by pc_by_len

@[simp] theorem pcDual2088 : IPC 2081 = 2711 := by pc_by_len

@[simp] theorem pcDual2089 : IPC 2082 = 2712 := by pc_by_len

@[simp] theorem pcDual2090 : IPC 2083 = 2713 := by pc_by_len

@[simp] theorem pcDual2091 : IPC 2084 = 2714 := by pc_by_len

@[simp] theorem pcDual2092 : IPC 2085 = 2715 := by pc_by_len

@[simp] theorem pcDual2093 : IPC 2086 = 2716 := by pc_by_len

@[simp] theorem pcDual2094 : IPC 2087 = 2719 := by pc_by_len

@[simp] theorem pcDual2095 : IPC 2088 = 2722 := by pc_by_len

@[simp] theorem pcDual2096 : IPC 2089 = 2723 := by pc_by_len

@[simp] theorem pcDual2100 : IPC 2090 = 2731 := by pc_by_len

@[simp] theorem pcDual2101 : IPC 2091 = 2732 := by pc_by_len

@[simp] theorem pcDual2102 : IPC 2092 = 2733 := by pc_by_len

@[simp] theorem pcDual2103 : IPC 2093 = 2734 := by pc_by_len

@[simp] theorem pcDual2104 : IPC 2094 = 2735 := by pc_by_len

@[simp] theorem pcDual2105 : IPC 2095 = 2736 := by pc_by_len

@[simp] theorem pcDual2106 : IPC 2096 = 2739 := by pc_by_len

@[simp] theorem pcDual2107 : IPC 2097 = 2740 := by pc_by_len

@[simp] theorem pcDual2108 : IPC 2098 = 2741 := by pc_by_len

@[simp] theorem pcDual2109 : IPC 2099 = 2744 := by pc_by_len

@[simp] theorem pcDual2110 : IPC 2100 = 2745 := by pc_by_len

@[simp] theorem pcDual2111 : IPC 2101 = 2746 := by pc_by_len

@[simp] theorem pcDual2112 : IPC 2102 = 2747 := by pc_by_len

@[simp] theorem pcDual2113 : IPC 2103 = 2748 := by pc_by_len

@[simp] theorem pcDual2114 : IPC 2104 = 2749 := by pc_by_len

@[simp] theorem pcDual2115 : IPC 2105 = 2750 := by pc_by_len

@[simp] theorem pcDual2116 : IPC 2106 = 2751 := by pc_by_len

@[simp] theorem pcDual2117 : IPC 2107 = 2752 := by pc_by_len

@[simp] theorem pcDual2118 : IPC 2108 = 2753 := by pc_by_len

@[simp] theorem pcDual2119 : IPC 2109 = 2754 := by pc_by_len

@[simp] theorem pcDual2120 : IPC 2110 = 2755 := by pc_by_len

@[simp] theorem pcDual2121 : IPC 2111 = 2756 := by pc_by_len

@[simp] theorem pcDual2122 : IPC 2112 = 2757 := by pc_by_len

@[simp] theorem pcDual2123 : IPC 2113 = 2758 := by pc_by_len

@[simp] theorem pcDual2124 : IPC 2114 = 2759 := by pc_by_len

@[simp] theorem pcDual2125 : IPC 2115 = 2760 := by pc_by_len

@[simp] theorem pcDual2126 : IPC 2116 = 2761 := by pc_by_len

@[simp] theorem pcDual2127 : IPC 2117 = 2765 := by pc_by_len

@[simp] theorem pcDual2128 : IPC 2118 = 2766 := by pc_by_len

@[simp] theorem pcDual2129 : IPC 2119 = 2767 := by pc_by_len

@[simp] theorem pcDual2130 : IPC 2120 = 2768 := by pc_by_len

@[simp] theorem pcDual2131 : IPC 2121 = 2769 := by pc_by_len

@[simp] theorem pcDual2132 : IPC 2122 = 2770 := by pc_by_len

@[simp] theorem pcDual2133 : IPC 2123 = 2771 := by pc_by_len

@[simp] theorem pcDual2134 : IPC 2124 = 2774 := by pc_by_len

@[simp] theorem pcDual2135 : IPC 2125 = 2775 := by pc_by_len

@[simp] theorem pcDual2136 : IPC 2126 = 2776 := by pc_by_len

@[simp] theorem pcDual2137 : IPC 2127 = 2777 := by pc_by_len

@[simp] theorem pcDual2138 : IPC 2128 = 2778 := by pc_by_len

@[simp] theorem pcDual2139 : IPC 2129 = 2779 := by pc_by_len

@[simp] theorem pcDual2140 : IPC 2130 = 2780 := by pc_by_len

@[simp] theorem pcDual2141 : IPC 2131 = 2781 := by pc_by_len

@[simp] theorem pcDual2142 : IPC 2132 = 2782 := by pc_by_len

@[simp] theorem pcDual2143 : IPC 2133 = 2783 := by pc_by_len

@[simp] theorem pcDual2144 : IPC 2134 = 2784 := by pc_by_len

@[simp] theorem pcDual2145 : IPC 2135 = 2785 := by pc_by_len

@[simp] theorem pcDual2146 : IPC 2136 = 2786 := by pc_by_len

@[simp] theorem pcDual2381 : IPC 2370 = 3057 := by pc_by_len

@[simp] theorem pcDual2382 : IPC 2371 = 3062 := by pc_by_len

@[simp] theorem pcDual2383 : IPC 2372 = 3063 := by pc_by_len

@[simp] theorem pcDual2384 : IPC 2373 = 3064 := by pc_by_len

@[simp] theorem pcDual2385 : IPC 2374 = 3065 := by pc_by_len

@[simp] theorem pcDual2386 : IPC 2375 = 3066 := by pc_by_len

@[simp] theorem pcDual2387 : IPC 2376 = 3067 := by pc_by_len

@[simp] theorem pcDual2388 : IPC 2377 = 3068 := by pc_by_len

@[simp] theorem pcDual2389 : IPC 2378 = 3069 := by pc_by_len

@[simp] theorem pcDual2390 : IPC 2379 = 3070 := by pc_by_len

@[simp] theorem pcDual2391 : IPC 2380 = 3071 := by pc_by_len

@[simp] theorem pcDual2392 : IPC 2381 = 3074 := by pc_by_len

@[simp] theorem pcDual2393 : IPC 2382 = 3075 := by pc_by_len

@[simp] theorem pcDual2394 : IPC 2383 = 3076 := by pc_by_len

@[simp] theorem pcDual2395 : IPC 2384 = 3079 := by pc_by_len

@[simp] theorem pcDual2396 : IPC 2385 = 3080 := by pc_by_len

@[simp] theorem pcDual2397 : IPC 2386 = 3081 := by pc_by_len

@[simp] theorem pcDual2398 : IPC 2387 = 3084 := by pc_by_len

@[simp] theorem pcDual2399 : IPC 2388 = 3085 := by pc_by_len

@[simp] theorem pcDual2400 : IPC 2389 = 3089 := by pc_by_len

@[simp] theorem pcDual2401 : IPC 2390 = 3090 := by pc_by_len

@[simp] theorem pcDual2402 : IPC 2391 = 3091 := by pc_by_len

@[simp] theorem pcDual2403 : IPC 2392 = 3094 := by pc_by_len

@[simp] theorem pcDual2404 : IPC 2393 = 3097 := by pc_by_len

@[simp] theorem pcDual2405 : IPC 2394 = 3098 := by pc_by_len

@[simp] theorem pcDual2406 : IPC 2395 = 3099 := by pc_by_len

@[simp] theorem pcDual2407 : IPC 2396 = 3101 := by pc_by_len

@[simp] theorem pcDual2408 : IPC 2397 = 3102 := by pc_by_len

@[simp] theorem pcDual2409 : IPC 2398 = 3103 := by pc_by_len

@[simp] theorem pcDual2410 : IPC 2399 = 3104 := by pc_by_len

@[simp] theorem pcDual2411 : IPC 2400 = 3105 := by pc_by_len

@[simp] theorem pcDual2412 : IPC 2401 = 3106 := by pc_by_len

@[simp] theorem pcDual2413 : IPC 2402 = 3107 := by pc_by_len

@[simp] theorem pcDual2414 : IPC 2403 = 3108 := by pc_by_len

@[simp] theorem pcDual2415 : IPC 2404 = 3111 := by pc_by_len

@[simp] theorem pcDual2416 : IPC 2405 = 3112 := by pc_by_len

@[simp] theorem pcDual2417 : IPC 2406 = 3113 := by pc_by_len

@[simp] theorem pcDual2418 : IPC 2407 = 3114 := by pc_by_len

@[simp] theorem pcDual2419 : IPC 2408 = 3115 := by pc_by_len

@[simp] theorem pcDual2420 : IPC 2409 = 3118 := by pc_by_len

@[simp] theorem pcDual2421 : IPC 2410 = 3119 := by pc_by_len

@[simp] theorem pcDual2422 : IPC 2411 = 3120 := by pc_by_len

@[simp] theorem pcDual2423 : IPC 2412 = 3121 := by pc_by_len

@[simp] theorem pcDual2424 : IPC 2413 = 3122 := by pc_by_len

@[simp] theorem pcDual2425 : IPC 2414 = 3123 := by pc_by_len

@[simp] theorem pcDual2426 : IPC 2415 = 3124 := by pc_by_len

@[simp] theorem pcDual2427 : IPC 2416 = 3125 := by pc_by_len

@[simp] theorem pcDual2428 : IPC 2417 = 3126 := by pc_by_len

@[simp] theorem pcDual2429 : IPC 2418 = 3127 := by pc_by_len

@[simp] theorem pcDual2430 : IPC 2419 = 3128 := by pc_by_len

@[simp] theorem pcDual2431 : IPC 2420 = 3129 := by pc_by_len

@[simp] theorem pcDual2432 : IPC 2421 = 3130 := by pc_by_len

@[simp] theorem pcDual2433 : IPC 2422 = 3131 := by pc_by_len

@[simp] theorem pcDual2434 : IPC 2423 = 3132 := by pc_by_len

@[simp] theorem pcDual2435 : IPC 2424 = 3133 := by pc_by_len

@[simp] theorem pcDual2436 : IPC 2425 = 3134 := by pc_by_len

@[simp] theorem pcDual2437 : IPC 2426 = 3135 := by pc_by_len

@[simp] theorem pcDual2438 : IPC 2427 = 3136 := by pc_by_len

@[simp] theorem pcDual2439 : IPC 2428 = 3138 := by pc_by_len

@[simp] theorem pcDual2440 : IPC 2429 = 3139 := by pc_by_len

@[simp] theorem pcDual2441 : IPC 2430 = 3140 := by pc_by_len

@[simp] theorem pcDual2442 : IPC 2431 = 3143 := by pc_by_len

@[simp] theorem pcDual2443 : IPC 2432 = 3144 := by pc_by_len

@[simp] theorem pcDual2444 : IPC 2433 = 3145 := by pc_by_len

@[simp] theorem pcDual2445 : IPC 2434 = 3148 := by pc_by_len

@[simp] theorem pcDual2446 : IPC 2435 = 3149 := by pc_by_len

@[simp] theorem pcDual2447 : IPC 2436 = 3150 := by pc_by_len

@[simp] theorem pcDual2448 : IPC 2437 = 3153 := by pc_by_len

@[simp] theorem pcDual2449 : IPC 2438 = 3154 := by pc_by_len

@[simp] theorem pcDual2450 : IPC 2439 = 3155 := by pc_by_len

@[simp] theorem pcDual2451 : IPC 2440 = 3156 := by pc_by_len

@[simp] theorem pcDual2452 : IPC 2441 = 3157 := by pc_by_len

@[simp] theorem pcDual2453 : IPC 2442 = 3160 := by pc_by_len

@[simp] theorem pcDual2454 : IPC 2443 = 3161 := by pc_by_len

@[simp] theorem pcDual2455 : IPC 2444 = 3162 := by pc_by_len

@[simp] theorem pcDual2456 : IPC 2445 = 3163 := by pc_by_len

@[simp] theorem pcDual2457 : IPC 2446 = 3166 := by pc_by_len

@[simp] theorem pcDual2458 : IPC 2447 = 3167 := by pc_by_len

@[simp] theorem pcDual2459 : IPC 2448 = 3170 := by pc_by_len

@[simp] theorem pcDual2460 : IPC 2449 = 3171 := by pc_by_len

@[simp] theorem pcDual2461 : IPC 2450 = 3172 := by pc_by_len

@[simp] theorem pcDual2462 : IPC 2451 = 3173 := by pc_by_len

@[simp] theorem pcDual2463 : IPC 2452 = 3176 := by pc_by_len

@[simp] theorem pcDual2464 : IPC 2453 = 3177 := by pc_by_len

@[simp] theorem pcDual2465 : IPC 2454 = 3180 := by pc_by_len

@[simp] theorem pcDual8548 : IPC 8453 = 10752 := by pc_by_len

@[simp] theorem pcDual8549 : IPC 8454 = 10753 := by pc_by_len

@[simp] theorem pcDual8550 : IPC 8455 = 10754 := by pc_by_len

@[simp] theorem pcDual8551 : IPC 8456 = 10755 := by pc_by_len

@[simp] theorem pcDual8552 : IPC 8457 = 10756 := by pc_by_len

@[simp] theorem pcDual8553 : IPC 8458 = 10759 := by pc_by_len

@[simp] theorem pcDual8554 : IPC 8459 = 10762 := by pc_by_len

@[simp] theorem pcDual8555 : IPC 8460 = 10763 := by pc_by_len

@[simp] theorem pcDual8559 : IPC 8461 = 10771 := by pc_by_len

@[simp] theorem pcDual8560 : IPC 8462 = 10772 := by pc_by_len

@[simp] theorem pcDual8561 : IPC 8463 = 10773 := by pc_by_len

@[simp] theorem pcDual8562 : IPC 8464 = 10774 := by pc_by_len

@[simp] theorem pcDual8563 : IPC 8465 = 10775 := by pc_by_len

@[simp] theorem pcDual8564 : IPC 8466 = 10776 := by pc_by_len

@[simp] theorem pcDual8565 : IPC 8467 = 10779 := by pc_by_len

@[simp] theorem pcDual8566 : IPC 8468 = 10780 := by pc_by_len

@[simp] theorem pcDual8567 : IPC 8469 = 10781 := by pc_by_len

@[simp] theorem pcDual8568 : IPC 8470 = 10784 := by pc_by_len

@[simp] theorem pcDual8569 : IPC 8471 = 10785 := by pc_by_len

@[simp] theorem pcDual8570 : IPC 8472 = 10786 := by pc_by_len

@[simp] theorem pcDual8571 : IPC 8473 = 10787 := by pc_by_len

@[simp] theorem pcDual8572 : IPC 8474 = 10788 := by pc_by_len

@[simp] theorem pcDual8573 : IPC 8475 = 10789 := by pc_by_len

@[simp] theorem pcDual8574 : IPC 8476 = 10790 := by pc_by_len

@[simp] theorem pcDual8575 : IPC 8477 = 10791 := by pc_by_len

@[simp] theorem pcDual8576 : IPC 8478 = 10792 := by pc_by_len

@[simp] theorem pcDual8577 : IPC 8479 = 10793 := by pc_by_len

@[simp] theorem pcDual8578 : IPC 8480 = 10794 := by pc_by_len

@[simp] theorem pcDual8579 : IPC 8481 = 10795 := by pc_by_len

@[simp] theorem pcDual8580 : IPC 8482 = 10796 := by pc_by_len

@[simp] theorem pcDual8581 : IPC 8483 = 10797 := by pc_by_len

@[simp] theorem pcDual8582 : IPC 8484 = 10798 := by pc_by_len

@[simp] theorem pcDual8583 : IPC 8485 = 10799 := by pc_by_len

@[simp] theorem pcDual8584 : IPC 8486 = 10800 := by pc_by_len

@[simp] theorem pcDual8585 : IPC 8487 = 10801 := by pc_by_len

@[simp] theorem pcDual8586 : IPC 8488 = 10805 := by pc_by_len

@[simp] theorem pcDual8587 : IPC 8489 = 10806 := by pc_by_len

@[simp] theorem pcDual8588 : IPC 8490 = 10807 := by pc_by_len

@[simp] theorem pcDual8589 : IPC 8491 = 10808 := by pc_by_len

@[simp] theorem pcDual8590 : IPC 8492 = 10809 := by pc_by_len

@[simp] theorem pcDual8591 : IPC 8493 = 10810 := by pc_by_len

@[simp] theorem pcDual8592 : IPC 8494 = 10811 := by pc_by_len

@[simp] theorem pcDual8593 : IPC 8495 = 10814 := by pc_by_len

@[simp] theorem pcDual8594 : IPC 8496 = 10815 := by pc_by_len

@[simp] theorem pcDual8595 : IPC 8497 = 10816 := by pc_by_len

@[simp] theorem pcDual8596 : IPC 8498 = 10817 := by pc_by_len

@[simp] theorem pcDual8597 : IPC 8499 = 10818 := by pc_by_len

@[simp] theorem pcDual8598 : IPC 8500 = 10819 := by pc_by_len

@[simp] theorem pcDual8599 : IPC 8501 = 10820 := by pc_by_len

@[simp] theorem pcDual8600 : IPC 8502 = 10821 := by pc_by_len

@[simp] theorem pcDual8601 : IPC 8503 = 10822 := by pc_by_len

@[simp] theorem pcDual8602 : IPC 8504 = 10823 := by pc_by_len

@[simp] theorem pcDual8603 : IPC 8505 = 10824 := by pc_by_len

@[simp] theorem pcDual8604 : IPC 8506 = 10825 := by pc_by_len

@[simp] theorem pcDual8605 : IPC 8507 = 10826 := by pc_by_len

@[simp] theorem pcDual8606 : IPC 8508 = 10827 := by pc_by_len

@[simp] theorem pcDual8607 : IPC 8509 = 10828 := by pc_by_len

@[simp] theorem pcDual8608 : IPC 8510 = 10829 := by pc_by_len

@[simp] theorem pcDual8609 : IPC 8511 = 10830 := by pc_by_len

@[simp] theorem pcDual8610 : IPC 8512 = 10831 := by pc_by_len

@[simp] theorem pcDual8611 : IPC 8513 = 10832 := by pc_by_len

@[simp] theorem pcDual8612 : IPC 8514 = 10833 := by pc_by_len

@[simp] theorem pcDual8613 : IPC 8515 = 10834 := by pc_by_len

@[simp] theorem pcDual8614 : IPC 8516 = 10835 := by pc_by_len

@[simp] theorem pcDual8615 : IPC 8517 = 10838 := by pc_by_len

@[simp] theorem pcDual8616 : IPC 8518 = 10839 := by pc_by_len

@[simp] theorem pcDual8617 : IPC 8519 = 10840 := by pc_by_len

@[simp] theorem pcDual8618 : IPC 8520 = 10841 := by pc_by_len

@[simp] theorem pcDual8619 : IPC 8521 = 10842 := by pc_by_len

@[simp] theorem pcDual8620 : IPC 8522 = 10843 := by pc_by_len

@[simp] theorem pcDual8621 : IPC 8523 = 10844 := by pc_by_len

@[simp] theorem pcDual8622 : IPC 8524 = 10845 := by pc_by_len

@[simp] theorem pcDual8623 : IPC 8525 = 10846 := by pc_by_len

@[simp] theorem pcDual8624 : IPC 8526 = 10847 := by pc_by_len

@[simp] theorem pcDual8625 : IPC 8527 = 10848 := by pc_by_len

@[simp] theorem pcDual8626 : IPC 8528 = 10849 := by pc_by_len

@[simp] theorem pcDual8627 : IPC 8529 = 10850 := by pc_by_len

@[simp] theorem pcDual8628 : IPC 8530 = 10851 := by pc_by_len

@[simp] theorem pcDual8629 : IPC 8531 = 10852 := by pc_by_len

@[simp] theorem pcDual8630 : IPC 8532 = 10853 := by pc_by_len

@[simp] theorem pcDual8631 : IPC 8533 = 10854 := by pc_by_len

@[simp] theorem pcDual8632 : IPC 8534 = 10855 := by pc_by_len

@[simp] theorem pcDual8633 : IPC 8535 = 10856 := by pc_by_len

@[simp] theorem pcDual8634 : IPC 8536 = 10857 := by pc_by_len

@[simp] theorem pcDual8635 : IPC 8537 = 10858 := by pc_by_len

@[simp] theorem pcDual8636 : IPC 8538 = 10859 := by pc_by_len

@[simp] theorem pcDual8637 : IPC 8539 = 10862 := by pc_by_len

@[simp] theorem pcDual8638 : IPC 8540 = 10863 := by pc_by_len

@[simp] theorem pcDual8639 : IPC 8541 = 10864 := by pc_by_len

@[simp] theorem pcDual8640 : IPC 8542 = 10865 := by pc_by_len

@[simp] theorem pcDual8641 : IPC 8543 = 10866 := by pc_by_len

@[simp] theorem pcDual8642 : IPC 8544 = 10869 := by pc_by_len

@[simp] theorem pcDual8643 : IPC 8545 = 10870 := by pc_by_len

@[simp] theorem pcDual8644 : IPC 8546 = 10871 := by pc_by_len

@[simp] theorem pcDual8645 : IPC 8547 = 10872 := by pc_by_len

@[simp] theorem pcDual8646 : IPC 8548 = 10873 := by pc_by_len

@[simp] theorem pcDual8647 : IPC 8549 = 10874 := by pc_by_len

@[simp] theorem pcDual8648 : IPC 8550 = 10875 := by pc_by_len

@[simp] theorem pcDual8649 : IPC 8551 = 10876 := by pc_by_len

@[simp] theorem pcDual8650 : IPC 8552 = 10877 := by pc_by_len

@[simp] theorem pcDual8651 : IPC 8553 = 10878 := by pc_by_len

@[simp] theorem pcDual8652 : IPC 8554 = 10879 := by pc_by_len

@[simp] theorem pcDual8653 : IPC 8555 = 10880 := by pc_by_len

@[simp] theorem pcDual8654 : IPC 8556 = 10881 := by pc_by_len

@[simp] theorem pcDual8655 : IPC 8557 = 10882 := by pc_by_len

@[simp] theorem pcDual8656 : IPC 8558 = 10883 := by pc_by_len

@[simp] theorem pcDual8657 : IPC 8559 = 10884 := by pc_by_len

@[simp] theorem pcDual8658 : IPC 8560 = 10885 := by pc_by_len

@[simp] theorem pcDual8659 : IPC 8561 = 10886 := by pc_by_len

@[simp] theorem pcDual8660 : IPC 8562 = 10887 := by pc_by_len

@[simp] theorem pcDual8661 : IPC 8563 = 10888 := by pc_by_len

@[simp] theorem pcDual8662 : IPC 8564 = 10889 := by pc_by_len

@[simp] theorem pcDual8663 : IPC 8565 = 10890 := by pc_by_len

@[simp] theorem pcDual8664 : IPC 8566 = 10891 := by pc_by_len

@[simp] theorem pcDual8665 : IPC 8567 = 10894 := by pc_by_len

@[simp] theorem pcDual8666 : IPC 8568 = 10895 := by pc_by_len

@[simp] theorem pcDual8667 : IPC 8569 = 10896 := by pc_by_len

@[simp] theorem pcDual8668 : IPC 8570 = 10897 := by pc_by_len

@[simp] theorem pcDual8669 : IPC 8571 = 10898 := by pc_by_len

@[simp] theorem pcDual8670 : IPC 8572 = 10901 := by pc_by_len

@[simp] theorem pcDual8671 : IPC 8573 = 10902 := by pc_by_len

@[simp] theorem pcDual8672 : IPC 8574 = 10903 := by pc_by_len

@[simp] theorem pcDual8673 : IPC 8575 = 10904 := by pc_by_len

@[simp] theorem pcDual8674 : IPC 8576 = 10905 := by pc_by_len

@[simp] theorem pcDual8675 : IPC 8577 = 10906 := by pc_by_len

@[simp] theorem pcDual8676 : IPC 8578 = 10907 := by pc_by_len

@[simp] theorem pcDual8677 : IPC 8579 = 10908 := by pc_by_len

@[simp] theorem pcDual8678 : IPC 8580 = 10909 := by pc_by_len

@[simp] theorem pcDual8679 : IPC 8581 = 10912 := by pc_by_len

@[simp] theorem pcDual8680 : IPC 8582 = 10913 := by pc_by_len

@[simp] theorem pcDual8681 : IPC 8583 = 10914 := by pc_by_len

@[simp] theorem pcDual8682 : IPC 8584 = 10915 := by pc_by_len

@[simp] theorem pcDual8683 : IPC 8585 = 10916 := by pc_by_len

@[simp] theorem pcDual8684 : IPC 8586 = 10917 := by pc_by_len

@[simp] theorem pcDual8685 : IPC 8587 = 10918 := by pc_by_len

@[simp] theorem pcDual8686 : IPC 8588 = 10919 := by pc_by_len

@[simp] theorem pcDual8687 : IPC 8589 = 10920 := by pc_by_len

@[simp] theorem pcDual8688 : IPC 8590 = 10921 := by pc_by_len

@[simp] theorem pcDual8689 : IPC 8591 = 10922 := by pc_by_len

@[simp] theorem pcDual8690 : IPC 8592 = 10923 := by pc_by_len

@[simp] theorem pcDual8691 : IPC 8593 = 10924 := by pc_by_len

@[simp] theorem pcDual8692 : IPC 8594 = 10925 := by pc_by_len

@[simp] theorem pcDual8693 : IPC 8595 = 10926 := by pc_by_len

@[simp] theorem pcDual8694 : IPC 8596 = 10927 := by pc_by_len

@[simp] theorem pcDual8695 : IPC 8597 = 10930 := by pc_by_len

@[simp] theorem pcDual8696 : IPC 8598 = 10931 := by pc_by_len

@[simp] theorem pcDual8697 : IPC 8599 = 10932 := by pc_by_len

@[simp] theorem pcDual8698 : IPC 8600 = 10933 := by pc_by_len

@[simp] theorem pcDual8699 : IPC 8601 = 10934 := by pc_by_len

@[simp] theorem pcDual8700 : IPC 8602 = 10937 := by pc_by_len

@[simp] theorem pcDual8701 : IPC 8603 = 10938 := by pc_by_len

@[simp] theorem pcDual8702 : IPC 8604 = 10939 := by pc_by_len

@[simp] theorem pcDual8703 : IPC 8605 = 10940 := by pc_by_len

@[simp] theorem pcDual8704 : IPC 8606 = 10941 := by pc_by_len

@[simp] theorem pcDual8705 : IPC 8607 = 10942 := by pc_by_len

@[simp] theorem pcDual8706 : IPC 8608 = 10943 := by pc_by_len

@[simp] theorem pcDual8707 : IPC 8609 = 10944 := by pc_by_len

@[simp] theorem pcDual8708 : IPC 8610 = 10945 := by pc_by_len

@[simp] theorem pcDual8709 : IPC 8611 = 10948 := by pc_by_len

@[simp] theorem pcDual8710 : IPC 8612 = 10949 := by pc_by_len

@[simp] theorem pcDual8711 : IPC 8613 = 10950 := by pc_by_len

@[simp] theorem pcDual8712 : IPC 8614 = 10951 := by pc_by_len

@[simp] theorem pcDual8713 : IPC 8615 = 10952 := by pc_by_len

@[simp] theorem pcDual8714 : IPC 8616 = 10953 := by pc_by_len

@[simp] theorem pcDual8715 : IPC 8617 = 10954 := by pc_by_len

@[simp] theorem pcDual8716 : IPC 8618 = 10955 := by pc_by_len

@[simp] theorem pcDual8717 : IPC 8619 = 10956 := by pc_by_len

@[simp] theorem pcDual8718 : IPC 8620 = 10957 := by pc_by_len

@[simp] theorem pcDual8719 : IPC 8621 = 10958 := by pc_by_len

@[simp] theorem pcDual8720 : IPC 8622 = 10959 := by pc_by_len

@[simp] theorem pcDual8721 : IPC 8623 = 10960 := by pc_by_len

@[simp] theorem pcDual8722 : IPC 8624 = 10961 := by pc_by_len

@[simp] theorem pcDual8723 : IPC 8625 = 10962 := by pc_by_len

@[simp] theorem pcDual8724 : IPC 8626 = 10965 := by pc_by_len

@[simp] theorem pcDual8725 : IPC 8627 = 10966 := by pc_by_len

@[simp] theorem pcDual8726 : IPC 8628 = 10967 := by pc_by_len

@[simp] theorem pcDual8727 : IPC 8629 = 10968 := by pc_by_len

@[simp] theorem pcDual8728 : IPC 8630 = 10973 := by pc_by_len

@[simp] theorem pcDual8729 : IPC 8631 = 10974 := by pc_by_len

@[simp] theorem pcDual8730 : IPC 8632 = 10975 := by pc_by_len

@[simp] theorem pcDual8731 : IPC 8633 = 10976 := by pc_by_len

@[simp] theorem pcDual8732 : IPC 8634 = 10977 := by pc_by_len

@[simp] theorem pcDual8733 : IPC 8635 = 10978 := by pc_by_len

@[simp] theorem pcDual8734 : IPC 8636 = 10979 := by pc_by_len

@[simp] theorem pcDual8735 : IPC 8637 = 10982 := by pc_by_len

end CycleSubmission.Global.ShiftPCs

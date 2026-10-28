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

@[simp] theorem pc2545 : CycleSubmission.Artifact.artifact.instructionPC 1873 = 2390 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1873 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2545

@[simp] theorem pc2546 : CycleSubmission.Artifact.artifact.instructionPC 1874 = 2391 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1874 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2546

@[simp] theorem pc2547 : CycleSubmission.Artifact.artifact.instructionPC 1875 = 2392 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1875 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2547

@[simp] theorem pc2548 : CycleSubmission.Artifact.artifact.instructionPC 1876 = 2393 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1876 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2548

@[simp] theorem pc2556 : CycleSubmission.Artifact.artifact.instructionPC 1877 = 2394 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1877 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2555

@[simp] theorem pc2559 : CycleSubmission.Artifact.artifact.instructionPC 1878 = 2397 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1878 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2559

@[simp] theorem pc2560 : CycleSubmission.Artifact.artifact.instructionPC 1879 = 2398 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1879 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2560

@[simp] theorem pc2561 : CycleSubmission.Artifact.artifact.instructionPC 1880 = 2399 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1880 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2561

@[simp] theorem pc2563 : CycleSubmission.Artifact.artifact.instructionPC 1881 = 2401 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1881 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2563

@[simp] theorem pc2566 : CycleSubmission.Artifact.artifact.instructionPC 1882 = 2404 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1882 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2566


@[simp] theorem pc2567 : CycleSubmission.Artifact.artifact.instructionPC 1883 = 2405 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1883 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2567

@[simp] theorem pc2570 : CycleSubmission.Artifact.artifact.instructionPC 1884 = 2408 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1884 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2570
@[simp] theorem pc2573 : CycleSubmission.Artifact.artifact.instructionPC 1885 = 2411 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1885 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2573

@[simp] theorem pc2574 : CycleSubmission.Artifact.artifact.instructionPC 1886 = 2412 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1886 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2574

@[simp] theorem pc2586 : CycleSubmission.Artifact.artifact.instructionPC 1897 = 2431 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1897 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2586

@[simp] theorem pc2591 : CycleSubmission.Artifact.artifact.instructionPC 1903 = 2440 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1903 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2591

@[simp] theorem pc2592 : CycleSubmission.Artifact.artifact.instructionPC 1904 = 2441 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1904 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2592

@[simp] theorem pc2599 : CycleSubmission.Artifact.artifact.instructionPC 1932 = 2486 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1932 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2599

@[simp] theorem pc2600 : CycleSubmission.Artifact.artifact.instructionPC 1933 = 2487 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1933 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2600

@[simp] theorem pc2604 : CycleSubmission.Artifact.artifact.instructionPC 1935 = 2489 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1935 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2604

@[simp] theorem pc2617 : CycleSubmission.Artifact.artifact.instructionPC 1938 = 2494 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1938 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2617

@[simp] theorem pc2618 : CycleSubmission.Artifact.artifact.instructionPC 1939 = 2495 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1939 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2618

@[simp] theorem pc2619 : CycleSubmission.Artifact.artifact.instructionPC 1940 = 2496 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1940 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2619

@[simp] theorem pc2620 : CycleSubmission.Artifact.artifact.instructionPC 1941 = 2497 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1941 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2620

@[simp] theorem pc2621 : CycleSubmission.Artifact.artifact.instructionPC 1942 = 2498 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1942 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2621

@[simp] theorem pc2622 : CycleSubmission.Artifact.artifact.instructionPC 1943 = 2499 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1943 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2622

@[simp] theorem pc2623 : CycleSubmission.Artifact.artifact.instructionPC 1944 = 2500 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1944 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2623

@[simp] theorem pc2624 : CycleSubmission.Artifact.artifact.instructionPC 1945 = 2501 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1945 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2624

@[simp] theorem pc2625 : CycleSubmission.Artifact.artifact.instructionPC 1946 = 2502 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1946 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2625

@[simp] theorem pc2628 : CycleSubmission.Artifact.artifact.instructionPC 1947 = 2503 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1947 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2628

@[simp] theorem pc2629 : CycleSubmission.Artifact.artifact.instructionPC 1948 = 2504 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1948 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2629

@[simp] theorem pc2631 : CycleSubmission.Artifact.artifact.instructionPC 1949 = 2506 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail7 1949 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2631

@[simp] theorem pc2632 : CycleSubmission.Artifact.artifact.instructionPC 1950 = 2507 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail7 1950 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2632

@[simp] theorem pc2633 : CycleSubmission.Artifact.artifact.instructionPC 1951 = 2510 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail7 1951 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2633

@[simp] theorem pc2636 : CycleSubmission.Artifact.artifact.instructionPC 1952 = 2511 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail7 1952 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2636

@[simp] theorem pc2637 : CycleSubmission.Artifact.artifact.instructionPC 1953 = 2513 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail7 1953 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2637

@[simp] theorem pc2638 : CycleSubmission.Artifact.artifact.instructionPC 1954 = 2514 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail7 1954 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2638

@[simp] theorem pc2639 : CycleSubmission.Artifact.artifact.instructionPC 1955 = 2518 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1955 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2640

@[simp] theorem pc2641 : CycleSubmission.Artifact.artifact.instructionPC 1956 = 2519 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1956 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2641

@[simp] theorem pc2642 : CycleSubmission.Artifact.artifact.instructionPC 1957 = 2520 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1957 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2642

@[simp] theorem pc2644 : CycleSubmission.Artifact.artifact.instructionPC 1958 = 2521 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1958 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2644

@[simp] theorem pc2645 : CycleSubmission.Artifact.artifact.instructionPC 1959 = 2522 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1959 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2645

@[simp] theorem pc2648 : CycleSubmission.Artifact.artifact.instructionPC 1960 = 2525 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1960 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2648

@[simp] theorem pc2649 : CycleSubmission.Artifact.artifact.instructionPC 1961 = 2526 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1961 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2649

@[simp] theorem pc2650 : CycleSubmission.Artifact.artifact.instructionPC 1962 = 2527 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1962 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2650

@[simp] theorem pc2651 : CycleSubmission.Artifact.artifact.instructionPC 1963 = 2528 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1963 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2651

@[simp] theorem pc2652 : CycleSubmission.Artifact.artifact.instructionPC 1964 = 2529 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1964 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2652

@[simp] theorem pc2653 : CycleSubmission.Artifact.artifact.instructionPC 1965 = 2530 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1965 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2653

@[simp] theorem pc2654 : CycleSubmission.Artifact.artifact.instructionPC 1966 = 2531 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1966 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2654

@[simp] theorem pc2657 : CycleSubmission.Artifact.artifact.instructionPC 1967 = 2534 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1967 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2657

@[simp] theorem pc2658 : CycleSubmission.Artifact.artifact.instructionPC 1968 = 2535 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1968 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2658

@[simp] theorem pc2659 : CycleSubmission.Artifact.artifact.instructionPC 1969 = 2538 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1969 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2659

@[simp] theorem pc2695 : CycleSubmission.Artifact.artifact.instructionPC 2015 = 2594 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2015 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2695

@[simp] theorem pc2696 : CycleSubmission.Artifact.artifact.instructionPC 2016 = 2595 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2016 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2696

@[simp] theorem pc2698 : CycleSubmission.Artifact.artifact.instructionPC 2017 = 2596 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2017 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2698

@[simp] theorem pc2699 : CycleSubmission.Artifact.artifact.instructionPC 2018 = 2597 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2018 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2699

@[simp] theorem pc2700 : CycleSubmission.Artifact.artifact.instructionPC 2019 = 2600 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2019 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2700

@[simp] theorem pc2701 : CycleSubmission.Artifact.artifact.instructionPC 2020 = 2601 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2020 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2701

@[simp] theorem pc2702 : CycleSubmission.Artifact.artifact.instructionPC 2021 = 2602 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2021 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2702

@[simp] theorem pc2703 : CycleSubmission.Artifact.artifact.instructionPC 2022 = 2603 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2022 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2703

@[simp] theorem pc2705 : CycleSubmission.Artifact.artifact.instructionPC 2023 = 2604 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2023 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2705

@[simp] theorem pc2706 : CycleSubmission.Artifact.artifact.instructionPC 2024 = 2605 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail10 2024 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2706

@[simp] theorem pc2713 : CycleSubmission.Artifact.artifact.instructionPC 2028 = 2612 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2028 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2713

@[simp] theorem pc3009 : CycleSubmission.Artifact.artifact.instructionPC 2228 = 2878 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2228 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3009

@[simp] theorem pc3010 : CycleSubmission.Artifact.artifact.instructionPC 2229 = 2879 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2229 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3010

@[simp] theorem pc3011 : CycleSubmission.Artifact.artifact.instructionPC 2230 = 2880 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2230 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3011

@[simp] theorem pc3012 : CycleSubmission.Artifact.artifact.instructionPC 2231 = 2881 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2231 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3012

@[simp] theorem pc3013 : CycleSubmission.Artifact.artifact.instructionPC 2232 = 2882 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2232 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3013

@[simp] theorem pc2707 : CycleSubmission.Artifact.artifact.instructionPC 2025 = 2609 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2025 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2710

@[simp] theorem pc2711 : CycleSubmission.Artifact.artifact.instructionPC 2026 = 2610 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2026 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2711

@[simp] theorem pc2712 : CycleSubmission.Artifact.artifact.instructionPC 2027 = 2611 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2027 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2712

@[simp] theorem pc2811 : CycleSubmission.Artifact.artifact.instructionPC 2082 = 2704 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2082 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2811

@[simp] theorem pcIdx2192 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2667 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2060 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcIdx2192

@[simp] theorem pcIdx2223 : CycleSubmission.Artifact.artifact.instructionPC 2084 = 2706 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2084 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcIdx2223

@[simp] theorem pcIdx2224 : CycleSubmission.Artifact.artifact.instructionPC 2085 = 2709 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2085 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcIdx2224

@[simp] theorem pcIdx2225 : CycleSubmission.Artifact.artifact.instructionPC 2086 = 2712 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2086 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcIdx2225

@[simp] theorem pc2826 : CycleSubmission.Artifact.artifact.instructionPC 2087 = 2713 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2087 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2826

@[simp] theorem pc2827 : CycleSubmission.Artifact.artifact.instructionPC 2088 = 2714 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2088 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2827

@[simp] theorem pc2830 : CycleSubmission.Artifact.artifact.instructionPC 2089 = 2717 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2089 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2830

@[simp] theorem pc2831 : CycleSubmission.Artifact.artifact.instructionPC 2090 = 2718 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2090 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2831

@[simp] theorem pc2832 : CycleSubmission.Artifact.artifact.instructionPC 2091 = 2719 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2091 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2832

@[simp] theorem pc2835 : CycleSubmission.Artifact.artifact.instructionPC 2092 = 2722 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2092 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2835

@[simp] theorem pc2837 : CycleSubmission.Artifact.artifact.instructionPC 2094 = 2724 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2094 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2837

@[simp] theorem pc2838 : CycleSubmission.Artifact.artifact.instructionPC 2095 = 2725 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2095 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2838

@[simp] theorem pc2839 : CycleSubmission.Artifact.artifact.instructionPC 2096 = 2726 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2096 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2839

@[simp] theorem pc2840 : CycleSubmission.Artifact.artifact.instructionPC 2097 = 2727 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2097 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2840

@[simp] theorem pc2843 : CycleSubmission.Artifact.artifact.instructionPC 2098 = 2730 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2098 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2843

@[simp] theorem pc2844 : CycleSubmission.Artifact.artifact.instructionPC 2099 = 2731 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2099 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2844

@[simp] theorem pc2846 : CycleSubmission.Artifact.artifact.instructionPC 2101 = 2735 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2101 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2846

@[simp] theorem pc2850 : CycleSubmission.Artifact.artifact.instructionPC 2103 = 2737 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2103 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2850

@[simp] theorem pc2851 : CycleSubmission.Artifact.artifact.instructionPC 2104 = 2738 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2104 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2851

@[simp] theorem pc2853 : CycleSubmission.Artifact.artifact.instructionPC 2106 = 2740 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2106 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2853

@[simp] theorem pc2855 : CycleSubmission.Artifact.artifact.instructionPC 2108 = 2742 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2108 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2855

@[simp] theorem pc2856 : CycleSubmission.Artifact.artifact.instructionPC 2109 = 2743 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2109 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2856

@[simp] theorem pc2857 : CycleSubmission.Artifact.artifact.instructionPC 2110 = 2744 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2110 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2857

@[simp] theorem pc2858 : CycleSubmission.Artifact.artifact.instructionPC 2111 = 2745 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2111 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2858

@[simp] theorem pc2859 : CycleSubmission.Artifact.artifact.instructionPC 2112 = 2746 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2112 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2859

@[simp] theorem pc2860 : CycleSubmission.Artifact.artifact.instructionPC 2113 = 2747 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2113 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2860

@[simp] theorem pc2862 : CycleSubmission.Artifact.artifact.instructionPC 2115 = 2749 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2115 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2862

@[simp] theorem pc2863 : CycleSubmission.Artifact.artifact.instructionPC 2116 = 2750 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2116 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2863

@[simp] theorem pc2864 : CycleSubmission.Artifact.artifact.instructionPC 2117 = 2751 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2117 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2864

@[simp] theorem pc2865 : CycleSubmission.Artifact.artifact.instructionPC 2118 = 2752 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2118 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2865

@[simp] theorem pc2888 : CycleSubmission.Artifact.artifact.instructionPC 2136 = 2776 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2136 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2319

@[simp] theorem pc3125 : CycleSubmission.Artifact.artifact.instructionPC 2325 = 2991 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2325 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3125







@[simp] theorem pc3171 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3034 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2362 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3171

@[simp] theorem pc3174 : CycleSubmission.Artifact.artifact.instructionPC 2363 = 3037 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2363 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3174

@[simp] theorem pc3175 : CycleSubmission.Artifact.artifact.instructionPC 2364 = 3038 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2364 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3175

@[simp] theorem pc3176 : CycleSubmission.Artifact.artifact.instructionPC 2365 = 3039 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2365 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3176

@[simp] theorem pc3177 : CycleSubmission.Artifact.artifact.instructionPC 2366 = 3040 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2366 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3177

@[simp] theorem pc3178 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3041 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2367 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3178

@[simp] theorem pc3179 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3042 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2368 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3179

@[simp] theorem pc3180 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3043 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2369 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3180

@[simp] theorem pc3181 : CycleSubmission.Artifact.artifact.instructionPC 2370 = 3044 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2370 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3181

@[simp] theorem pc3182 : CycleSubmission.Artifact.artifact.instructionPC 2371 = 3045 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2371 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3182

@[simp] theorem pc3183 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3046 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2372 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3183

@[simp] theorem pc3184 : CycleSubmission.Artifact.artifact.instructionPC 2373 = 3047 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2373 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3184

@[simp] theorem pc3185 : CycleSubmission.Artifact.artifact.instructionPC 2374 = 3048 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2374 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3185

@[simp] theorem pc3186 : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3049 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2375 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3186

@[simp] theorem pc3187 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3050 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2376 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3187

@[simp] theorem pc3188 : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3051 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2377 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3188

@[simp] theorem pc3191 : CycleSubmission.Artifact.artifact.instructionPC 2378 = 3054 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2378 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3191

@[simp] theorem pc3192 : CycleSubmission.Artifact.artifact.instructionPC 2379 = 3055 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2379 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3192

@[simp] theorem pc3214 : CycleSubmission.Artifact.artifact.instructionPC 2393 = 3075 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2393 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3214

@[simp] theorem pc3215 : CycleSubmission.Artifact.artifact.instructionPC 2394 = 3076 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2394 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3215

@[simp] theorem pc3216 : CycleSubmission.Artifact.artifact.instructionPC 2395 = 3077 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2395 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3216

@[simp] theorem pc3219 : CycleSubmission.Artifact.artifact.instructionPC 2396 = 3080 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2396 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3219

@[simp] theorem pc3220 : CycleSubmission.Artifact.artifact.instructionPC 2397 = 3081 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2397 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3220

@[simp] theorem pc3221 : CycleSubmission.Artifact.artifact.instructionPC 2398 = 3082 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2398 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3221

@[simp] theorem pc3222 : CycleSubmission.Artifact.artifact.instructionPC 2399 = 3083 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2399 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3222

@[simp] theorem pc3223 : CycleSubmission.Artifact.artifact.instructionPC 2400 = 3084 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2400 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3223

@[simp] theorem pc3226 : CycleSubmission.Artifact.artifact.instructionPC 2401 = 3087 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2401 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3226

@[simp] theorem pc3227 : CycleSubmission.Artifact.artifact.instructionPC 2402 = 3088 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2402 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3227


@[simp] theorem pc3228 : CycleSubmission.Artifact.artifact.instructionPC 2403 = 3089 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2403 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3228

@[simp] theorem pc3229 : CycleSubmission.Artifact.artifact.instructionPC 2404 = 3090 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2404 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3229

@[simp] theorem pc3230 : CycleSubmission.Artifact.artifact.instructionPC 2405 = 3091 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2405 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3230

@[simp] theorem pc3231 : CycleSubmission.Artifact.artifact.instructionPC 2406 = 3092 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2406 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3231

@[simp] theorem pc3232 : CycleSubmission.Artifact.artifact.instructionPC 2407 = 3093 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2407 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3232

@[simp] theorem pc3233 : CycleSubmission.Artifact.artifact.instructionPC 2408 = 3094 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2408 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3233

@[simp] theorem pc3234 : CycleSubmission.Artifact.artifact.instructionPC 2409 = 3095 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2409 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3234

@[simp] theorem pc3235 : CycleSubmission.Artifact.artifact.instructionPC 2410 = 3096 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2410 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3235

@[simp] theorem pc3236 : CycleSubmission.Artifact.artifact.instructionPC 2411 = 3097 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2411 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3236

@[simp] theorem pc3237 : CycleSubmission.Artifact.artifact.instructionPC 2412 = 3098 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2412 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3237

@[simp] theorem pc3238 : CycleSubmission.Artifact.artifact.instructionPC 2413 = 3099 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2413 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3238

@[simp] theorem pc3239 : CycleSubmission.Artifact.artifact.instructionPC 2414 = 3100 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2414 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3239

@[simp] theorem pc3240 : CycleSubmission.Artifact.artifact.instructionPC 2415 = 3101 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2415 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3240

@[simp] theorem pc3241 : CycleSubmission.Artifact.artifact.instructionPC 2416 = 3102 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2416 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3241

@[simp] theorem pc3242 : CycleSubmission.Artifact.artifact.instructionPC 2417 = 3103 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2417 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3242

@[simp] theorem pc3243 : CycleSubmission.Artifact.artifact.instructionPC 2418 = 3104 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2418 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3243

@[simp] theorem pc3244 : CycleSubmission.Artifact.artifact.instructionPC 2419 = 3105 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2419 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3244

@[simp] theorem pc3246 : CycleSubmission.Artifact.artifact.instructionPC 2420 = 3107 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2420 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3246

@[simp] theorem pc3247 : CycleSubmission.Artifact.artifact.instructionPC 2421 = 3108 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2421 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3247

@[simp] theorem pc3248 : CycleSubmission.Artifact.artifact.instructionPC 2422 = 3109 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2422 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3248

@[simp] theorem pc3251 : CycleSubmission.Artifact.artifact.instructionPC 2423 = 3112 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2423 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3251

@[simp] theorem pc3252 : CycleSubmission.Artifact.artifact.instructionPC 2424 = 3113 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2424 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3252

@[simp] theorem pc3185_compact : CycleSubmission.Artifact.artifact.instructionPC 2412 = 3098 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2412 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3237

@[simp] theorem pc3256 : CycleSubmission.Artifact.artifact.instructionPC 2426 = 3117 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2426 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3256

@[simp] theorem pc3257 : CycleSubmission.Artifact.artifact.instructionPC 2427 = 3118 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2427 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3257

@[simp] theorem pc3258 : CycleSubmission.Artifact.artifact.instructionPC 2428 = 3119 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2428 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3258

@[simp] theorem pc3261 : CycleSubmission.Artifact.artifact.instructionPC 2429 = 3122 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2429 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3261

@[simp] theorem pc3262 : CycleSubmission.Artifact.artifact.instructionPC 2430 = 3123 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2430 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3262

@[simp] theorem pc3263 : CycleSubmission.Artifact.artifact.instructionPC 2431 = 3124 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2431 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3263

@[simp] theorem pc3264 : CycleSubmission.Artifact.artifact.instructionPC 2432 = 3125 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2432 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3264

@[simp] theorem pc3265 : CycleSubmission.Artifact.artifact.instructionPC 2433 = 3126 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2433 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3265

@[simp] theorem pc3268 : CycleSubmission.Artifact.artifact.instructionPC 2434 = 3129 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2434 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3268

@[simp] theorem pc3269 : CycleSubmission.Artifact.artifact.instructionPC 2435 = 3130 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2435 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3269

@[simp] theorem pc3270 : CycleSubmission.Artifact.artifact.instructionPC 2436 = 3131 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2436 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3270

@[simp] theorem pc3271 : CycleSubmission.Artifact.artifact.instructionPC 2437 = 3132 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2437 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3271

@[simp] theorem pc3274 : CycleSubmission.Artifact.artifact.instructionPC 2438 = 3135 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2438 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3274

@[simp] theorem pc3276 : CycleSubmission.Artifact.artifact.instructionPC 2439 = 3136 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2439 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3276

@[simp] theorem pc3279 : CycleSubmission.Artifact.artifact.instructionPC 2440 = 3139 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2440 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3279

@[simp] theorem pc3281 : CycleSubmission.Artifact.artifact.instructionPC 2442 = 3141 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2442 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3281

@[simp] theorem pc3282 : CycleSubmission.Artifact.artifact.instructionPC 2443 = 3142 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2443 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3282

@[simp] theorem pc3285 : CycleSubmission.Artifact.artifact.instructionPC 2444 = 3145 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2444 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3285

@[simp] theorem pc3198 : CycleSubmission.Artifact.artifact.instructionPC 2383 = 3061 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2383 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3198

@[simp] theorem pcM9b2525 : CycleSubmission.Artifact.artifact.instructionPC 2384 = 3062 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2384 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcM9b2525

@[simp] theorem pcM9b2526 : CycleSubmission.Artifact.artifact.instructionPC 2385 = 3063 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2385 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcM9b2526

@[simp] theorem pcM9b2527 : CycleSubmission.Artifact.artifact.instructionPC 2386 = 3064 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2386 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcM9b2527

@[simp] theorem pcM9b2528 : CycleSubmission.Artifact.artifact.instructionPC 2387 = 3065 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2387 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcM9b2528

@[simp] theorem pcM9b2529 : CycleSubmission.Artifact.artifact.instructionPC 2388 = 3068 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2388 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcM9b2529

@[simp] theorem pcM9b2530 : CycleSubmission.Artifact.artifact.instructionPC 2389 = 3069 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2389 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcM9b2530

@[simp] theorem pcM9b2531 : CycleSubmission.Artifact.artifact.instructionPC 2390 = 3072 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2390 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcM9b2531

@[simp] theorem pc3346 : CycleSubmission.Artifact.artifact.instructionPC 2445 = 3146 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2445 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3346

@[simp] theorem pc3347 : CycleSubmission.Artifact.artifact.instructionPC 2446 = 3147 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2446 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3347

@[simp] theorem pc3265a : CycleSubmission.Artifact.artifact.instructionPC 2453 = 3158 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2453 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3265a


@[simp] theorem pc3265c : CycleSubmission.Artifact.artifact.instructionPC 2457 = 3165 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2457 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3265c


@[simp] theorem pc3265e : CycleSubmission.Artifact.artifact.instructionPC 2459 = 3169 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2459 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3265e

@[simp] theorem pcSaturate2987 : CycleSubmission.Artifact.artifact.instructionPC 2116 = 2750 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2116 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2863

@[simp] theorem pcSaturate2989 : CycleSubmission.Artifact.artifact.instructionPC 2117 = 2751 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2117 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2864

@[simp] theorem pcSaturate2990 : CycleSubmission.Artifact.artifact.instructionPC 2118 = 2752 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2118 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2865

@[simp] theorem pcSaturate2991 : CycleSubmission.Artifact.artifact.instructionPC 2119 = 2753 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2119 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcSaturate2991

@[simp] theorem pcSaturate2992 : CycleSubmission.Artifact.artifact.instructionPC 2310 = 2972 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2310 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcSaturate2992

@[simp] theorem pcSaturate2993 : CycleSubmission.Artifact.artifact.instructionPC 2311 = 2973 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2311 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcSaturate2993

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2668 = 3423 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2669 = 3424 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2670 = 3425 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2671 = 3426 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2672 = 3427 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3428 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2674 = 3429 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3432 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3433 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3433 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3436 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2895 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3437 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2896 : CycleSubmission.Artifact.artifact.instructionPC 2689 = 3457 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2930 : CycleSubmission.Artifact.artifact.instructionPC 2690 = 3458 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2931 : CycleSubmission.Artifact.artifact.instructionPC 2691 = 3459 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2932 : CycleSubmission.Artifact.artifact.instructionPC 2692 = 3460 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2933 : CycleSubmission.Artifact.artifact.instructionPC 2693 = 3461 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2694 = 3462 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2695 = 3463 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2696 = 3466 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2697 = 3467 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2698 = 3469 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2699 = 3470 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2700 = 3471 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2701 = 3472 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2702 = 3473 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2703 = 3476 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl


@[simp] theorem pcC3009 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3041 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2367 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3178

@[simp] theorem pcC3010 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3042 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2368 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3179

@[simp] theorem pcC3011 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3043 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2369 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3180

@[simp] theorem pcC3019 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3050 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2376 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3187

@[simp] theorem pcC3020 : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3051 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2377 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3188

@[simp] theorem pcC3021 : CycleSubmission.Artifact.artifact.instructionPC 2378 = 3054 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2378 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3191


@[simp] theorem pcC3078 : CycleSubmission.Artifact.artifact.instructionPC 2429 = 3122 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2429 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3261

@[simp] theorem pcC3082 : CycleSubmission.Artifact.artifact.instructionPC 2433 = 3126 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2433 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3265

@[simp] theorem pcC3083 : CycleSubmission.Artifact.artifact.instructionPC 2434 = 3129 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2434 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3268


/-! Program counters of the retained-T blocks the head-start table did not carry (generated from the artifact). -/

@[simp] theorem pcT2106 : CycleSubmission.Artifact.artifact.instructionPC 1887 = 2413 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1887 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2106

@[simp] theorem pcT2283 : CycleSubmission.Artifact.artifact.instructionPC 2081 = 2703 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2081 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2283

@[simp] theorem pcT2303 : CycleSubmission.Artifact.artifact.instructionPC 2097 = 2727 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2097 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2840

@[simp] theorem pcT2304 : CycleSubmission.Artifact.artifact.instructionPC 2098 = 2730 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2098 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2843

@[simp] theorem pcT2305 : CycleSubmission.Artifact.artifact.instructionPC 2099 = 2731 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2099 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2844

@[simp] theorem pcT2306 : CycleSubmission.Artifact.artifact.instructionPC 2100 = 2732 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2100 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2306

@[simp] theorem pcT2307 : CycleSubmission.Artifact.artifact.instructionPC 2101 = 2735 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2101 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2846

@[simp] theorem pcT2308 : CycleSubmission.Artifact.artifact.instructionPC 2102 = 2736 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2102 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2308

@[simp] theorem pcT2309 : CycleSubmission.Artifact.artifact.instructionPC 2103 = 2737 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2103 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2850

@[simp] theorem pcT2310 : CycleSubmission.Artifact.artifact.instructionPC 2104 = 2738 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2104 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2851

@[simp] theorem pcT2311 : CycleSubmission.Artifact.artifact.instructionPC 2105 = 2739 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2105 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2311

@[simp] theorem pcT2312 : CycleSubmission.Artifact.artifact.instructionPC 2106 = 2740 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2106 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2853

@[simp] theorem pcT2313 : CycleSubmission.Artifact.artifact.instructionPC 2107 = 2741 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2107 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2313

@[simp] theorem pcT2314 : CycleSubmission.Artifact.artifact.instructionPC 2108 = 2742 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2108 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2855

@[simp] theorem pcT2315 : CycleSubmission.Artifact.artifact.instructionPC 2109 = 2743 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2109 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2856

@[simp] theorem pcT2316 : CycleSubmission.Artifact.artifact.instructionPC 2110 = 2744 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2110 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2857

@[simp] theorem pcT2317 : CycleSubmission.Artifact.artifact.instructionPC 2111 = 2745 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2111 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2858

@[simp] theorem pcT2318 : CycleSubmission.Artifact.artifact.instructionPC 2112 = 2746 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2112 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2859

@[simp] theorem pcT2319 : CycleSubmission.Artifact.artifact.instructionPC 2113 = 2747 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2113 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2860

@[simp] theorem pcT2329 : CycleSubmission.Artifact.artifact.instructionPC 2313 = 2975 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2313 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2329

@[simp] theorem pcT2330 : CycleSubmission.Artifact.artifact.instructionPC 2314 = 2976 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2314 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2330

@[simp] theorem pcT2331 : CycleSubmission.Artifact.artifact.instructionPC 2315 = 2977 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2315 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2331

@[simp] theorem pcT2332 : CycleSubmission.Artifact.artifact.instructionPC 2316 = 2978 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2316 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2332

@[simp] theorem pcT2336 : CycleSubmission.Artifact.artifact.instructionPC 2320 = 2984 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2320 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2336

@[simp] theorem pcT2337 : CycleSubmission.Artifact.artifact.instructionPC 2321 = 2985 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2321 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2337

@[simp] theorem pcT2338 : CycleSubmission.Artifact.artifact.instructionPC 2322 = 2986 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2322 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2338

@[simp] theorem pcT2339 : CycleSubmission.Artifact.artifact.instructionPC 2323 = 2987 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2323 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2339

@[simp] theorem pcT2340 : CycleSubmission.Artifact.artifact.instructionPC 2324 = 2990 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2324 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2340

@[simp] theorem pcT2341 : CycleSubmission.Artifact.artifact.instructionPC 2325 = 2991 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2325 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3125

@[simp] theorem pcT2342 : CycleSubmission.Artifact.artifact.instructionPC 2326 = 2992 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2326 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2342

@[simp] theorem pcT2343 : CycleSubmission.Artifact.artifact.instructionPC 2327 = 2993 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2327 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2343

@[simp] theorem pcT2344 : CycleSubmission.Artifact.artifact.instructionPC 2328 = 2994 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2328 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2344

@[simp] theorem pcT2345 : CycleSubmission.Artifact.artifact.instructionPC 2329 = 2995 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2329 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2345

@[simp] theorem pcT2346 : CycleSubmission.Artifact.artifact.instructionPC 2330 = 2996 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2330 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2346

@[simp] theorem pcT2347 : CycleSubmission.Artifact.artifact.instructionPC 2331 = 2997 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2331 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2347

@[simp] theorem pcT2348 : CycleSubmission.Artifact.artifact.instructionPC 2332 = 2998 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2332 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2348

@[simp] theorem pcT2349 : CycleSubmission.Artifact.artifact.instructionPC 2333 = 3001 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2333 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2349

@[simp] theorem pcT2350 : CycleSubmission.Artifact.artifact.instructionPC 2334 = 3002 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2334 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2350

@[simp] theorem pcT2351 : CycleSubmission.Artifact.artifact.instructionPC 2335 = 3003 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2335 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2351

@[simp] theorem pcT2352 : CycleSubmission.Artifact.artifact.instructionPC 2336 = 3004 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2336 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2352

@[simp] theorem pcT2353 : CycleSubmission.Artifact.artifact.instructionPC 2337 = 3005 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2337 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2353

@[simp] theorem pcT2354 : CycleSubmission.Artifact.artifact.instructionPC 2338 = 3006 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2338 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2354

@[simp] theorem pcT2355 : CycleSubmission.Artifact.artifact.instructionPC 2339 = 3007 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2339 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2355

@[simp] theorem pcT2356 : CycleSubmission.Artifact.artifact.instructionPC 2340 = 3008 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2340 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2356

@[simp] theorem pcT2357 : CycleSubmission.Artifact.artifact.instructionPC 2341 = 3009 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2341 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2357

@[simp] theorem pcT2358 : CycleSubmission.Artifact.artifact.instructionPC 2342 = 3010 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2342 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2358

@[simp] theorem pcT2359 : CycleSubmission.Artifact.artifact.instructionPC 2343 = 3011 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2343 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2359

@[simp] theorem pcT2360 : CycleSubmission.Artifact.artifact.instructionPC 2344 = 3012 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2344 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2360

@[simp] theorem pcT2361 : CycleSubmission.Artifact.artifact.instructionPC 2345 = 3013 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2345 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2361

@[simp] theorem pcT2362 : CycleSubmission.Artifact.artifact.instructionPC 2346 = 3014 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2346 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2362

@[simp] theorem pcT2363 : CycleSubmission.Artifact.artifact.instructionPC 2347 = 3015 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2347 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2363

@[simp] theorem pcT2364 : CycleSubmission.Artifact.artifact.instructionPC 2348 = 3016 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2348 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2364

@[simp] theorem pcT2365 : CycleSubmission.Artifact.artifact.instructionPC 2349 = 3019 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2349 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2365

@[simp] theorem pcT2366 : CycleSubmission.Artifact.artifact.instructionPC 2350 = 3020 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2350 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2366

@[simp] theorem pcT2367 : CycleSubmission.Artifact.artifact.instructionPC 2351 = 3021 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2351 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2367

@[simp] theorem pcT2368 : CycleSubmission.Artifact.artifact.instructionPC 2352 = 3022 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2352 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2368

@[simp] theorem pcT2369 : CycleSubmission.Artifact.artifact.instructionPC 2353 = 3023 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2353 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2369

@[simp] theorem pcT2370 : CycleSubmission.Artifact.artifact.instructionPC 2354 = 3026 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2354 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2370

@[simp] theorem pcT2371 : CycleSubmission.Artifact.artifact.instructionPC 2355 = 3027 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2355 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2371

@[simp] theorem pcT2372 : CycleSubmission.Artifact.artifact.instructionPC 2356 = 3028 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2356 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2372

@[simp] theorem pcT2522 : CycleSubmission.Artifact.artifact.instructionPC 2379 = 3055 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2379 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3192

@[simp] theorem pcT2647 : CycleSubmission.Artifact.artifact.instructionPC 2452 = 3157 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2452 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2647

@[simp] theorem pcT2649 : CycleSubmission.Artifact.artifact.instructionPC 2454 = 3161 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2454 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2649

@[simp] theorem pcT2651 : CycleSubmission.Artifact.artifact.instructionPC 2456 = 3164 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2456 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2651

@[simp] theorem pcT2653 : CycleSubmission.Artifact.artifact.instructionPC 2458 = 3166 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2458 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcT2653

@[simp] theorem pcI2013 : CycleSubmission.Artifact.artifact.instructionPC 1831 = 2317 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1831 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2013

@[simp] theorem pcI2014 : CycleSubmission.Artifact.artifact.instructionPC 1832 = 2318 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1832 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2014

@[simp] theorem pcI2015 : CycleSubmission.Artifact.artifact.instructionPC 1833 = 2319 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1833 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2015

@[simp] theorem pcI2016 : CycleSubmission.Artifact.artifact.instructionPC 1834 = 2321 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1834 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2016

@[simp] theorem pcI2017 : CycleSubmission.Artifact.artifact.instructionPC 1835 = 2322 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1835 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2017

@[simp] theorem pcI2018 : CycleSubmission.Artifact.artifact.instructionPC 1836 = 2325 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1836 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2018

@[simp] theorem pcI2032 : CycleSubmission.Artifact.artifact.instructionPC 1839 = 2329 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1839 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2032

@[simp] theorem pcI2033 : CycleSubmission.Artifact.artifact.instructionPC 1840 = 2330 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1840 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2033

@[simp] theorem pcI2034 : CycleSubmission.Artifact.artifact.instructionPC 1841 = 2332 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1841 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2034

@[simp] theorem pcI2035 : CycleSubmission.Artifact.artifact.instructionPC 1842 = 2335 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1842 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2035

@[simp] theorem pcI2036 : CycleSubmission.Artifact.artifact.instructionPC 1852 = 2350 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1852 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2036

@[simp] theorem pcI2037 : CycleSubmission.Artifact.artifact.instructionPC 1853 = 2351 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1853 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2037

@[simp] theorem pcI2038 : CycleSubmission.Artifact.artifact.instructionPC 1854 = 2354 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1854 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2038

@[simp] theorem pcI2039 : CycleSubmission.Artifact.artifact.instructionPC 1855 = 2355 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1855 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2039

@[simp] theorem pcI2040 : CycleSubmission.Artifact.artifact.instructionPC 1856 = 2356 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1856 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2040

@[simp] theorem pcI2041 : CycleSubmission.Artifact.artifact.instructionPC 1857 = 2358 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1857 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2041

@[simp] theorem pcI2042 : CycleSubmission.Artifact.artifact.instructionPC 1858 = 2359 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1858 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2042

@[simp] theorem pcI2043 : CycleSubmission.Artifact.artifact.instructionPC 1859 = 2363 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1859 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2043

@[simp] theorem pcI2044 : CycleSubmission.Artifact.artifact.instructionPC 1860 = 2364 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1860 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2044

@[simp] theorem pcI2045 : CycleSubmission.Artifact.artifact.instructionPC 1861 = 2366 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1861 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2045

@[simp] theorem pcI2046 : CycleSubmission.Artifact.artifact.instructionPC 1862 = 2367 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1862 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2046

@[simp] theorem pcI2047 : CycleSubmission.Artifact.artifact.instructionPC 1863 = 2369 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1863 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2047

@[simp] theorem pcI2048 : CycleSubmission.Artifact.artifact.instructionPC 1864 = 2370 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1864 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2048

@[simp] theorem pcI2049 : CycleSubmission.Artifact.artifact.instructionPC 1865 = 2373 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old4 1865 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2049

@[simp] theorem pcI2050 : CycleSubmission.Artifact.artifact.instructionPC 1866 = 2375 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcI2051 : CycleSubmission.Artifact.artifact.instructionPC 1867 = 2376 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcI2052 : CycleSubmission.Artifact.artifact.instructionPC 1867 = 2376 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pcI2053 : CycleSubmission.Artifact.artifact.instructionPC 1868 = 2377 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1868 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2053

@[simp] theorem pcI2054 : CycleSubmission.Artifact.artifact.instructionPC 1869 = 2380 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1869 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2054

@[simp] theorem pcI2055 : CycleSubmission.Artifact.artifact.instructionPC 1870 = 2383 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1870 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2055

@[simp] theorem pcI2056 : CycleSubmission.Artifact.artifact.instructionPC 1871 = 2386 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1871 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2056

@[simp] theorem pcI2057 : CycleSubmission.Artifact.artifact.instructionPC 1872 = 2389 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail5 1872 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2057

@[simp] theorem pcI2093 : CycleSubmission.Artifact.artifact.instructionPC 1888 = 2414 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1888 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2093

@[simp] theorem pcI2094 : CycleSubmission.Artifact.artifact.instructionPC 1889 = 2417 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1889 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2094

@[simp] theorem pcI2095 : CycleSubmission.Artifact.artifact.instructionPC 1890 = 2420 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail6 1890 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2095

@[simp] theorem pcI2156 : CycleSubmission.Artifact.artifact.instructionPC 1970 = 2539 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail8 1970 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2156

@[simp] theorem pcI2200 : CycleSubmission.Artifact.artifact.instructionPC 2029 = 2613 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2029 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2200

@[simp] theorem pcI2201 : CycleSubmission.Artifact.artifact.instructionPC 2030 = 2614 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2030 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2201

@[simp] theorem pcI2202 : CycleSubmission.Artifact.artifact.instructionPC 2031 = 2615 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2031 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2202

@[simp] theorem pcI2203 : CycleSubmission.Artifact.artifact.instructionPC 2032 = 2616 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2032 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2203

@[simp] theorem pcI2204 : CycleSubmission.Artifact.artifact.instructionPC 2033 = 2617 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2033 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2204

@[simp] theorem pcI2205 : CycleSubmission.Artifact.artifact.instructionPC 2034 = 2618 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2034 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2205

@[simp] theorem pcI2206 : CycleSubmission.Artifact.artifact.instructionPC 2035 = 2621 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2035 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2206

@[simp] theorem pcI2207 : CycleSubmission.Artifact.artifact.instructionPC 2036 = 2622 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2036 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2207

@[simp] theorem pcI2208 : CycleSubmission.Artifact.artifact.instructionPC 2037 = 2625 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2037 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2208

@[simp] theorem pcI2209 : CycleSubmission.Artifact.artifact.instructionPC 2038 = 2626 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2038 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2209

@[simp] theorem pcI2210 : CycleSubmission.Artifact.artifact.instructionPC 2039 = 2629 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2039 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2210

@[simp] theorem pcI2211 : CycleSubmission.Artifact.artifact.instructionPC 2040 = 2630 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2040 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2211

@[simp] theorem pcI2212 : CycleSubmission.Artifact.artifact.instructionPC 2041 = 2633 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2041 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2212

@[simp] theorem pcI2213 : CycleSubmission.Artifact.artifact.instructionPC 2042 = 2634 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2042 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2213

@[simp] theorem pcI2214 : CycleSubmission.Artifact.artifact.instructionPC 2043 = 2637 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2043 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2214

@[simp] theorem pcI2215 : CycleSubmission.Artifact.artifact.instructionPC 2044 = 2638 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2044 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2215

@[simp] theorem pcI2216 : CycleSubmission.Artifact.artifact.instructionPC 2045 = 2641 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2045 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2216

@[simp] theorem pcI2217 : CycleSubmission.Artifact.artifact.instructionPC 2046 = 2642 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2046 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2217

@[simp] theorem pcI2218 : CycleSubmission.Artifact.artifact.instructionPC 2047 = 2645 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2047 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2218

@[simp] theorem pcI2219 : CycleSubmission.Artifact.artifact.instructionPC 2048 = 2646 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2048 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2219

@[simp] theorem pcI2220 : CycleSubmission.Artifact.artifact.instructionPC 2049 = 2649 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2049 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2220

@[simp] theorem pcI2221 : CycleSubmission.Artifact.artifact.instructionPC 2050 = 2650 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2050 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2221

@[simp] theorem pcI2222 : CycleSubmission.Artifact.artifact.instructionPC 2051 = 2653 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2051 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2222

@[simp] theorem pcI2223 : CycleSubmission.Artifact.artifact.instructionPC 2052 = 2654 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2052 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2223

@[simp] theorem pcI2224 : CycleSubmission.Artifact.artifact.instructionPC 2053 = 2657 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2053 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2224

@[simp] theorem pcI2225 : CycleSubmission.Artifact.artifact.instructionPC 2054 = 2658 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2054 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2225

@[simp] theorem pcI2226 : CycleSubmission.Artifact.artifact.instructionPC 2055 = 2661 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2055 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2226

@[simp] theorem pcI2227 : CycleSubmission.Artifact.artifact.instructionPC 2056 = 2662 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2056 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2227

@[simp] theorem pcI2228 : CycleSubmission.Artifact.artifact.instructionPC 2057 = 2663 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2057 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2228

@[simp] theorem pcI2229 : CycleSubmission.Artifact.artifact.instructionPC 2058 = 2664 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2058 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2229

@[simp] theorem pcI2230 : CycleSubmission.Artifact.artifact.instructionPC 2059 = 2666 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2059 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2230

@[simp] theorem pcI2232 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2667 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2060 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcIdx2192

@[simp] theorem pcI2233 : CycleSubmission.Artifact.artifact.instructionPC 2060 = 2667 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2060 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcIdx2192

@[simp] theorem pcI2234 : CycleSubmission.Artifact.artifact.instructionPC 2061 = 2673 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2061 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2234

@[simp] theorem pcI2235 : CycleSubmission.Artifact.artifact.instructionPC 2062 = 2674 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2062 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2235

@[simp] theorem pcI2236 : CycleSubmission.Artifact.artifact.instructionPC 2063 = 2677 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2063 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2236

@[simp] theorem pcI2237 : CycleSubmission.Artifact.artifact.instructionPC 2064 = 2678 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2064 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2237

@[simp] theorem pcI2238 : CycleSubmission.Artifact.artifact.instructionPC 2065 = 2679 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2065 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2238

@[simp] theorem pcI2239 : CycleSubmission.Artifact.artifact.instructionPC 2066 = 2681 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2066 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2239

@[simp] theorem pcI2240 : CycleSubmission.Artifact.artifact.instructionPC 2067 = 2682 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2067 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2240

@[simp] theorem pcI2241 : CycleSubmission.Artifact.artifact.instructionPC 2068 = 2685 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2068 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2241

@[simp] theorem pcI2242 : CycleSubmission.Artifact.artifact.instructionPC 2069 = 2686 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2069 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2242

@[simp] theorem pcI2243 : CycleSubmission.Artifact.artifact.instructionPC 2070 = 2687 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2070 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2243

@[simp] theorem pcI2244 : CycleSubmission.Artifact.artifact.instructionPC 2071 = 2688 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2071 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2244

@[simp] theorem pcI2245 : CycleSubmission.Artifact.artifact.instructionPC 2072 = 2689 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2072 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2245

@[simp] theorem pcI2246 : CycleSubmission.Artifact.artifact.instructionPC 2073 = 2691 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2073 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2246

@[simp] theorem pcI2247 : CycleSubmission.Artifact.artifact.instructionPC 2074 = 2692 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2074 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2247

@[simp] theorem pcI2253 : CycleSubmission.Artifact.artifact.instructionPC 2075 = 2693 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2075 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2253

@[simp] theorem pcI2254 : CycleSubmission.Artifact.artifact.instructionPC 2076 = 2694 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2076 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2254

@[simp] theorem pcI2255 : CycleSubmission.Artifact.artifact.instructionPC 2077 = 2697 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2077 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2255

@[simp] theorem pcI2256 : CycleSubmission.Artifact.artifact.instructionPC 2078 = 2698 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2078 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2256

@[simp] theorem pcI2257 : CycleSubmission.Artifact.artifact.instructionPC 2079 = 2699 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2079 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2257

@[simp] theorem pcI2258 : CycleSubmission.Artifact.artifact.instructionPC 2080 = 2702 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2080 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2258

@[simp] theorem pcI2265 : CycleSubmission.Artifact.artifact.instructionPC 2083 = 2705 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2083 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2265

@[simp] theorem pcI2275 : CycleSubmission.Artifact.artifact.instructionPC 2093 = 2723 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2093 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2275

@[simp] theorem pcI2296 : CycleSubmission.Artifact.artifact.instructionPC 2114 = 2748 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2114 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2296

@[simp] theorem pcI2302 : CycleSubmission.Artifact.artifact.instructionPC 2120 = 2754 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2120 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2302

@[simp] theorem pcI2303 : CycleSubmission.Artifact.artifact.instructionPC 2121 = 2757 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2121 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2303

@[simp] theorem pcI2304 : CycleSubmission.Artifact.artifact.instructionPC 2122 = 2758 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2122 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2304

@[simp] theorem pcI2305 : CycleSubmission.Artifact.artifact.instructionPC 2123 = 2759 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2123 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2305

@[simp] theorem pcI2306 : CycleSubmission.Artifact.artifact.instructionPC 2124 = 2761 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2124 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2306

@[simp] theorem pcI2307 : CycleSubmission.Artifact.artifact.instructionPC 2125 = 2762 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2125 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2307

@[simp] theorem pcI2308 : CycleSubmission.Artifact.artifact.instructionPC 2126 = 2764 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2126 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2308

@[simp] theorem pcI2309 : CycleSubmission.Artifact.artifact.instructionPC 2127 = 2765 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2127 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2309

@[simp] theorem pcI2310 : CycleSubmission.Artifact.artifact.instructionPC 2128 = 2766 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail11 2128 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2310

@[simp] theorem pcI2311 : CycleSubmission.Artifact.artifact.instructionPC 2129 = 2769 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2129 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2312

@[simp] theorem pcI2312 : CycleSubmission.Artifact.artifact.instructionPC 2130 = 2770 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2130 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2313

@[simp] theorem pcI2313 : CycleSubmission.Artifact.artifact.instructionPC 2131 = 2771 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2131 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2314

@[simp] theorem pcI2314 : CycleSubmission.Artifact.artifact.instructionPC 2132 = 2772 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2132 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2315

@[simp] theorem pcI2315 : CycleSubmission.Artifact.artifact.instructionPC 2133 = 2773 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2133 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2316

@[simp] theorem pcI2316 : CycleSubmission.Artifact.artifact.instructionPC 2134 = 2774 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2134 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2317

@[simp] theorem pcI2317 : CycleSubmission.Artifact.artifact.instructionPC 2135 = 2775 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2135 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc2888

@[simp] theorem pcI2319 : CycleSubmission.Artifact.artifact.instructionPC 2137 = 2777 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2137 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2320

@[simp] theorem pcI2320 : CycleSubmission.Artifact.artifact.instructionPC 2138 = 2778 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2138 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2321

@[simp] theorem pcI2321 : CycleSubmission.Artifact.artifact.instructionPC 2139 = 2779 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2139 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2322

@[simp] theorem pcI2322 : CycleSubmission.Artifact.artifact.instructionPC 2140 = 2780 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2140 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2323

@[simp] theorem pcI2323 : CycleSubmission.Artifact.artifact.instructionPC 2141 = 2781 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2141 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2324

@[simp] theorem pcI2326 : CycleSubmission.Artifact.artifact.instructionPC 2142 = 2782 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2142 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2326

@[simp] theorem pcI2327 : CycleSubmission.Artifact.artifact.instructionPC 2143 = 2783 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2143 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2327

@[simp] theorem pcI2328 : CycleSubmission.Artifact.artifact.instructionPC 2144 = 2784 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2144 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2328

@[simp] theorem pcI2329 : CycleSubmission.Artifact.artifact.instructionPC 2145 = 2785 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2145 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2329

@[simp] theorem pcI2330 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2331 : CycleSubmission.Artifact.artifact.instructionPC 2146 = 2786 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2146 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2331

@[simp] theorem pcI2332 : CycleSubmission.Artifact.artifact.instructionPC 2147 = 2787 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2147 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2332

@[simp] theorem pcI2333 : CycleSubmission.Artifact.artifact.instructionPC 2148 = 2788 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2148 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2333

@[simp] theorem pcI2334 : CycleSubmission.Artifact.artifact.instructionPC 2149 = 2789 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2149 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2334

@[simp] theorem pcI2335 : CycleSubmission.Artifact.artifact.instructionPC 2150 = 2790 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2150 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2335

@[simp] theorem pcI2336 : CycleSubmission.Artifact.artifact.instructionPC 2151 = 2791 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2151 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2336

@[simp] theorem pcI2337 : CycleSubmission.Artifact.artifact.instructionPC 2152 = 2792 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2152 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2337

@[simp] theorem pcI2338 : CycleSubmission.Artifact.artifact.instructionPC 2153 = 2793 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2153 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2338

@[simp] theorem pcI2339 : CycleSubmission.Artifact.artifact.instructionPC 2154 = 2794 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2154 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2339

@[simp] theorem pcI2340 : CycleSubmission.Artifact.artifact.instructionPC 2155 = 2795 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2155 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2340

@[simp] theorem pcI2341 : CycleSubmission.Artifact.artifact.instructionPC 2156 = 2798 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2156 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2341

@[simp] theorem pcI2342 : CycleSubmission.Artifact.artifact.instructionPC 2157 = 2799 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2157 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2342

@[simp] theorem pcI2343 : CycleSubmission.Artifact.artifact.instructionPC 2158 = 2800 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2158 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2343

@[simp] theorem pcI2344 : CycleSubmission.Artifact.artifact.instructionPC 2159 = 2801 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2159 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2344

@[simp] theorem pcI2345 : CycleSubmission.Artifact.artifact.instructionPC 2160 = 2802 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2160 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2345

@[simp] theorem pcI2346 : CycleSubmission.Artifact.artifact.instructionPC 2161 = 2803 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2161 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2346

@[simp] theorem pcI2347 : CycleSubmission.Artifact.artifact.instructionPC 2162 = 2804 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2162 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2347

@[simp] theorem pcI2348 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2349 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2350 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2351 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2352 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2353 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2354 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2355 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2356 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2357 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2358 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2359 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2360 : CycleSubmission.Artifact.artifact.instructionPC 2163 = 2805 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2163 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2360

@[simp] theorem pcI2361 : CycleSubmission.Artifact.artifact.instructionPC 2164 = 2806 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2164 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2361

@[simp] theorem pcI2362 : CycleSubmission.Artifact.artifact.instructionPC 2165 = 2807 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2165 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2362

@[simp] theorem pcI2363 : CycleSubmission.Artifact.artifact.instructionPC 2166 = 2808 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2166 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2363

@[simp] theorem pcI2364 : CycleSubmission.Artifact.artifact.instructionPC 2167 = 2809 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2167 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2364

@[simp] theorem pcI2365 : CycleSubmission.Artifact.artifact.instructionPC 2168 = 2810 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2168 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2365

@[simp] theorem pcI2366 : CycleSubmission.Artifact.artifact.instructionPC 2169 = 2811 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2169 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2366

@[simp] theorem pcI2367 : CycleSubmission.Artifact.artifact.instructionPC 2170 = 2812 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2170 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2367

@[simp] theorem pcI2368 : CycleSubmission.Artifact.artifact.instructionPC 2171 = 2813 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2171 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2368

@[simp] theorem pcI2369 : CycleSubmission.Artifact.artifact.instructionPC 2172 = 2814 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2172 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2369

@[simp] theorem pcI2370 : CycleSubmission.Artifact.artifact.instructionPC 2173 = 2815 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2173 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2370

@[simp] theorem pcI2371 : CycleSubmission.Artifact.artifact.instructionPC 2174 = 2816 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2174 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2371

@[simp] theorem pcI2372 : CycleSubmission.Artifact.artifact.instructionPC 2175 = 2817 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2175 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2372

@[simp] theorem pcI2373 : CycleSubmission.Artifact.artifact.instructionPC 2176 = 2818 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2176 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2373

@[simp] theorem pcI2374 : CycleSubmission.Artifact.artifact.instructionPC 2177 = 2819 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2177 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2374

@[simp] theorem pcI2375 : CycleSubmission.Artifact.artifact.instructionPC 2178 = 2822 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2178 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2375

@[simp] theorem pcI2376 : CycleSubmission.Artifact.artifact.instructionPC 2179 = 2823 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2179 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2376

@[simp] theorem pcI2377 : CycleSubmission.Artifact.artifact.instructionPC 2180 = 2824 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2180 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2377

@[simp] theorem pcI2378 : CycleSubmission.Artifact.artifact.instructionPC 2181 = 2825 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2181 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2378

@[simp] theorem pcI2379 : CycleSubmission.Artifact.artifact.instructionPC 2182 = 2826 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2182 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2379

@[simp] theorem pcI2380 : CycleSubmission.Artifact.artifact.instructionPC 2183 = 2829 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2183 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2380

@[simp] theorem pcI2381 : CycleSubmission.Artifact.artifact.instructionPC 2184 = 2830 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2184 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2381

@[simp] theorem pcI2382 : CycleSubmission.Artifact.artifact.instructionPC 2185 = 2831 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2185 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2382

@[simp] theorem pcI2383 : CycleSubmission.Artifact.artifact.instructionPC 2186 = 2832 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2186 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2383

@[simp] theorem pcI2384 : CycleSubmission.Artifact.artifact.instructionPC 2187 = 2833 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2187 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2384

@[simp] theorem pcI2385 : CycleSubmission.Artifact.artifact.instructionPC 2188 = 2834 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2188 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2385

@[simp] theorem pcI2386 : CycleSubmission.Artifact.artifact.instructionPC 2189 = 2835 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2189 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2386

@[simp] theorem pcI2387 : CycleSubmission.Artifact.artifact.instructionPC 2190 = 2836 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2190 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2387

@[simp] theorem pcI2388 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2389 : CycleSubmission.Artifact.artifact.instructionPC 2191 = 2837 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2191 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2389

@[simp] theorem pcI2390 : CycleSubmission.Artifact.artifact.instructionPC 2192 = 2838 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2192 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2390

@[simp] theorem pcI2391 : CycleSubmission.Artifact.artifact.instructionPC 2193 = 2839 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2193 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2391

@[simp] theorem pcI2392 : CycleSubmission.Artifact.artifact.instructionPC 2194 = 2840 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2194 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2392

@[simp] theorem pcI2393 : CycleSubmission.Artifact.artifact.instructionPC 2195 = 2841 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2195 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2393

@[simp] theorem pcI2394 : CycleSubmission.Artifact.artifact.instructionPC 2196 = 2842 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2196 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2394

@[simp] theorem pcI2395 : CycleSubmission.Artifact.artifact.instructionPC 2197 = 2843 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2197 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2395

@[simp] theorem pcI2396 : CycleSubmission.Artifact.artifact.instructionPC 2198 = 2844 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2198 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2396

@[simp] theorem pcI2397 : CycleSubmission.Artifact.artifact.instructionPC 2199 = 2845 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2199 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2397

@[simp] theorem pcI2398 : CycleSubmission.Artifact.artifact.instructionPC 2200 = 2846 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2200 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2398

@[simp] theorem pcI2399 : CycleSubmission.Artifact.artifact.instructionPC 2201 = 2847 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2201 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2399

@[simp] theorem pcI2400 : CycleSubmission.Artifact.artifact.instructionPC 2202 = 2848 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2202 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2400

@[simp] theorem pcI2401 : CycleSubmission.Artifact.artifact.instructionPC 2203 = 2849 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2203 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2401

@[simp] theorem pcI2402 : CycleSubmission.Artifact.artifact.instructionPC 2204 = 2850 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2204 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2402

@[simp] theorem pcI2403 : CycleSubmission.Artifact.artifact.instructionPC 2205 = 2851 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2205 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2403

@[simp] theorem pcI2404 : CycleSubmission.Artifact.artifact.instructionPC 2206 = 2854 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2206 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2404

@[simp] theorem pcI2405 : CycleSubmission.Artifact.artifact.instructionPC 2207 = 2855 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2207 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2405

@[simp] theorem pcI2406 : CycleSubmission.Artifact.artifact.instructionPC 2208 = 2856 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2208 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2406

@[simp] theorem pcI2407 : CycleSubmission.Artifact.artifact.instructionPC 2209 = 2857 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2209 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2407

@[simp] theorem pcI2408 : CycleSubmission.Artifact.artifact.instructionPC 2210 = 2858 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2210 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2408

@[simp] theorem pcI2409 : CycleSubmission.Artifact.artifact.instructionPC 2211 = 2861 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2211 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2409

@[simp] theorem pcI2410 : CycleSubmission.Artifact.artifact.instructionPC 2212 = 2862 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2212 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2410

@[simp] theorem pcI2411 : CycleSubmission.Artifact.artifact.instructionPC 2213 = 2863 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2213 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2411

@[simp] theorem pcI2412 : CycleSubmission.Artifact.artifact.instructionPC 2214 = 2864 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2214 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2412

@[simp] theorem pcI2413 : CycleSubmission.Artifact.artifact.instructionPC 2215 = 2865 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2215 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2413

@[simp] theorem pcI2414 : CycleSubmission.Artifact.artifact.instructionPC 2216 = 2866 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2216 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2414

@[simp] theorem pcI2415 : CycleSubmission.Artifact.artifact.instructionPC 2217 = 2867 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2217 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2415

@[simp] theorem pcI2416 : CycleSubmission.Artifact.artifact.instructionPC 2218 = 2868 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2218 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2416

@[simp] theorem pcI2417 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2418 : CycleSubmission.Artifact.artifact.instructionPC 2219 = 2869 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2219 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2418

@[simp] theorem pcI2419 : CycleSubmission.Artifact.artifact.instructionPC 2220 = 2870 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2220 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2419

@[simp] theorem pcI2420 : CycleSubmission.Artifact.artifact.instructionPC 2221 = 2871 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2221 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2420

@[simp] theorem pcI2421 : CycleSubmission.Artifact.artifact.instructionPC 2222 = 2872 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2222 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2421

@[simp] theorem pcI2422 : CycleSubmission.Artifact.artifact.instructionPC 2223 = 2873 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2223 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2422

@[simp] theorem pcI2423 : CycleSubmission.Artifact.artifact.instructionPC 2224 = 2874 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2224 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2423

@[simp] theorem pcI2424 : CycleSubmission.Artifact.artifact.instructionPC 2225 = 2875 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2225 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2424

@[simp] theorem pcI2425 : CycleSubmission.Artifact.artifact.instructionPC 2226 = 2876 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2226 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2425

@[simp] theorem pcI2426 : CycleSubmission.Artifact.artifact.instructionPC 2227 = 2877 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2227 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2426

@[simp] theorem pcI2432 : CycleSubmission.Artifact.artifact.instructionPC 2233 = 2883 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2233 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2432

@[simp] theorem pcI2433 : CycleSubmission.Artifact.artifact.instructionPC 2234 = 2886 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2234 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2433

@[simp] theorem pcI2434 : CycleSubmission.Artifact.artifact.instructionPC 2235 = 2887 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2235 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2434

@[simp] theorem pcI2435 : CycleSubmission.Artifact.artifact.instructionPC 2236 = 2888 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2236 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2435

@[simp] theorem pcI2436 : CycleSubmission.Artifact.artifact.instructionPC 2237 = 2889 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2237 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2436

@[simp] theorem pcI2437 : CycleSubmission.Artifact.artifact.instructionPC 2238 = 2890 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2238 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2437

@[simp] theorem pcI2438 : CycleSubmission.Artifact.artifact.instructionPC 2239 = 2893 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2239 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2438

@[simp] theorem pcI2439 : CycleSubmission.Artifact.artifact.instructionPC 2240 = 2894 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2240 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2439

@[simp] theorem pcI2440 : CycleSubmission.Artifact.artifact.instructionPC 2241 = 2895 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2241 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2440

@[simp] theorem pcI2441 : CycleSubmission.Artifact.artifact.instructionPC 2242 = 2896 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2242 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2441

@[simp] theorem pcI2442 : CycleSubmission.Artifact.artifact.instructionPC 2243 = 2897 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2243 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2442

@[simp] theorem pcI2443 : CycleSubmission.Artifact.artifact.instructionPC 2244 = 2898 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2244 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2443

@[simp] theorem pcI2444 : CycleSubmission.Artifact.artifact.instructionPC 2245 = 2899 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2245 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2444

@[simp] theorem pcI2445 : CycleSubmission.Artifact.artifact.instructionPC 2246 = 2900 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2246 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2445

@[simp] theorem pcI2446 : CycleSubmission.Artifact.artifact.instructionPC 2247 = 2901 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2247 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2446

@[simp] theorem pcI2447 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2448 : CycleSubmission.Artifact.artifact.instructionPC 2248 = 2902 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2248 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2448

@[simp] theorem pcI2449 : CycleSubmission.Artifact.artifact.instructionPC 2249 = 2903 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2249 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2449

@[simp] theorem pcI2450 : CycleSubmission.Artifact.artifact.instructionPC 2250 = 2904 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2250 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2450

@[simp] theorem pcI2451 : CycleSubmission.Artifact.artifact.instructionPC 2251 = 2905 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2251 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2451

@[simp] theorem pcI2452 : CycleSubmission.Artifact.artifact.instructionPC 2252 = 2906 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2252 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2452

@[simp] theorem pcI2453 : CycleSubmission.Artifact.artifact.instructionPC 2253 = 2907 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2253 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2453

@[simp] theorem pcI2454 : CycleSubmission.Artifact.artifact.instructionPC 2254 = 2908 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2254 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2454

@[simp] theorem pcI2455 : CycleSubmission.Artifact.artifact.instructionPC 2255 = 2909 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2255 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2455

@[simp] theorem pcI2456 : CycleSubmission.Artifact.artifact.instructionPC 2256 = 2910 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2256 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2456

@[simp] theorem pcI2457 : CycleSubmission.Artifact.artifact.instructionPC 2257 = 2911 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2257 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2457

@[simp] theorem pcI2458 : CycleSubmission.Artifact.artifact.instructionPC 2258 = 2912 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2258 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2458

@[simp] theorem pcI2459 : CycleSubmission.Artifact.artifact.instructionPC 2259 = 2913 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2259 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2459

@[simp] theorem pcI2460 : CycleSubmission.Artifact.artifact.instructionPC 2260 = 2914 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2260 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2460

@[simp] theorem pcI2461 : CycleSubmission.Artifact.artifact.instructionPC 2261 = 2915 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2261 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2461

@[simp] theorem pcI2462 : CycleSubmission.Artifact.artifact.instructionPC 2262 = 2916 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2262 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2462

@[simp] theorem pcI2463 : CycleSubmission.Artifact.artifact.instructionPC 2263 = 2919 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2263 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2463

@[simp] theorem pcI2464 : CycleSubmission.Artifact.artifact.instructionPC 2264 = 2920 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2264 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2464

@[simp] theorem pcI2465 : CycleSubmission.Artifact.artifact.instructionPC 2265 = 2921 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2265 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2465

@[simp] theorem pcI2466 : CycleSubmission.Artifact.artifact.instructionPC 2266 = 2922 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2266 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2466

@[simp] theorem pcI2467 : CycleSubmission.Artifact.artifact.instructionPC 2267 = 2923 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2267 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2467

@[simp] theorem pcI2468 : CycleSubmission.Artifact.artifact.instructionPC 2268 = 2926 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2268 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2468

@[simp] theorem pcI2469 : CycleSubmission.Artifact.artifact.instructionPC 2269 = 2927 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2269 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2469

@[simp] theorem pcI2470 : CycleSubmission.Artifact.artifact.instructionPC 2270 = 2928 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2270 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2470

@[simp] theorem pcI2471 : CycleSubmission.Artifact.artifact.instructionPC 2271 = 2929 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2271 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2471

@[simp] theorem pcI2472 : CycleSubmission.Artifact.artifact.instructionPC 2272 = 2930 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2272 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2472

@[simp] theorem pcI2473 : CycleSubmission.Artifact.artifact.instructionPC 2273 = 2931 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2273 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2473

@[simp] theorem pcI2474 : CycleSubmission.Artifact.artifact.instructionPC 2274 = 2932 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2274 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2474

@[simp] theorem pcI2475 : CycleSubmission.Artifact.artifact.instructionPC 2275 = 2933 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2275 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2475

@[simp] theorem pcI2476 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2477 : CycleSubmission.Artifact.artifact.instructionPC 2276 = 2934 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2276 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2477

@[simp] theorem pcI2478 : CycleSubmission.Artifact.artifact.instructionPC 2277 = 2935 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2277 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2478

@[simp] theorem pcI2479 : CycleSubmission.Artifact.artifact.instructionPC 2278 = 2936 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2278 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2479

@[simp] theorem pcI2480 : CycleSubmission.Artifact.artifact.instructionPC 2279 = 2937 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2279 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2480

@[simp] theorem pcI2481 : CycleSubmission.Artifact.artifact.instructionPC 2280 = 2938 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2280 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2481

@[simp] theorem pcI2482 : CycleSubmission.Artifact.artifact.instructionPC 2281 = 2939 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2281 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2482

@[simp] theorem pcI2483 : CycleSubmission.Artifact.artifact.instructionPC 2282 = 2940 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2282 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2483

@[simp] theorem pcI2484 : CycleSubmission.Artifact.artifact.instructionPC 2283 = 2941 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2283 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2484

@[simp] theorem pcI2485 : CycleSubmission.Artifact.artifact.instructionPC 2284 = 2942 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2284 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2485

@[simp] theorem pcI2486 : CycleSubmission.Artifact.artifact.instructionPC 2285 = 2943 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2285 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2486

@[simp] theorem pcI2487 : CycleSubmission.Artifact.artifact.instructionPC 2286 = 2944 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2286 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2487

@[simp] theorem pcI2488 : CycleSubmission.Artifact.artifact.instructionPC 2287 = 2945 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2287 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2488

@[simp] theorem pcI2489 : CycleSubmission.Artifact.artifact.instructionPC 2288 = 2946 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2288 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2489

@[simp] theorem pcI2490 : CycleSubmission.Artifact.artifact.instructionPC 2289 = 2947 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2289 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2490

@[simp] theorem pcI2491 : CycleSubmission.Artifact.artifact.instructionPC 2290 = 2948 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2290 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2491

@[simp] theorem pcI2492 : CycleSubmission.Artifact.artifact.instructionPC 2291 = 2951 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2291 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2492

@[simp] theorem pcI2493 : CycleSubmission.Artifact.artifact.instructionPC 2292 = 2952 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2292 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2493

@[simp] theorem pcI2494 : CycleSubmission.Artifact.artifact.instructionPC 2293 = 2953 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2293 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2494

@[simp] theorem pcI2495 : CycleSubmission.Artifact.artifact.instructionPC 2294 = 2954 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2294 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2495

@[simp] theorem pcI2496 : CycleSubmission.Artifact.artifact.instructionPC 2295 = 2955 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2295 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2496

@[simp] theorem pcI2497 : CycleSubmission.Artifact.artifact.instructionPC 2296 = 2958 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2296 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2497

@[simp] theorem pcI2498 : CycleSubmission.Artifact.artifact.instructionPC 2297 = 2959 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2297 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2498

@[simp] theorem pcI2499 : CycleSubmission.Artifact.artifact.instructionPC 2298 = 2960 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2298 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2499

@[simp] theorem pcI2500 : CycleSubmission.Artifact.artifact.instructionPC 2299 = 2961 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2299 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2500

@[simp] theorem pcI2501 : CycleSubmission.Artifact.artifact.instructionPC 2300 = 2962 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2300 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2501

@[simp] theorem pcI2502 : CycleSubmission.Artifact.artifact.instructionPC 2301 = 2963 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2301 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2502

@[simp] theorem pcI2503 : CycleSubmission.Artifact.artifact.instructionPC 2302 = 2964 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2302 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2503

@[simp] theorem pcI2504 : CycleSubmission.Artifact.artifact.instructionPC 2303 = 2965 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2303 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2504

@[simp] theorem pcI2505 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2506 : CycleSubmission.Artifact.artifact.instructionPC 2304 = 2966 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2304 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2506

@[simp] theorem pcI2507 : CycleSubmission.Artifact.artifact.instructionPC 2305 = 2967 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2305 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2507

@[simp] theorem pcI2508 : CycleSubmission.Artifact.artifact.instructionPC 2306 = 2968 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2306 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2508

@[simp] theorem pcI2509 : CycleSubmission.Artifact.artifact.instructionPC 2307 = 2969 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2307 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2509

@[simp] theorem pcI2510 : CycleSubmission.Artifact.artifact.instructionPC 2308 = 2970 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2308 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2510

@[simp] theorem pcI2511 : CycleSubmission.Artifact.artifact.instructionPC 2309 = 2971 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2309 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2511

@[simp] theorem pcI2514 : CycleSubmission.Artifact.artifact.instructionPC 2312 = 2974 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2312 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2514

@[simp] theorem pcI2519 : CycleSubmission.Artifact.artifact.instructionPC 2317 = 2979 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2317 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2519

@[simp] theorem pcI2520 : CycleSubmission.Artifact.artifact.instructionPC 2318 = 2980 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2318 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2520

@[simp] theorem pcI2521 : CycleSubmission.Artifact.artifact.instructionPC 2319 = 2983 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2319 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2521

@[simp] theorem pcI2559 : CycleSubmission.Artifact.artifact.instructionPC 2357 = 3029 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2357 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2559

@[simp] theorem pcI2560 : CycleSubmission.Artifact.artifact.instructionPC 2358 = 3030 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2358 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2560

@[simp] theorem pcI2561 : CycleSubmission.Artifact.artifact.instructionPC 2359 = 3031 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2359 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2561

@[simp] theorem pcI2562 : CycleSubmission.Artifact.artifact.instructionPC 2360 = 3032 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2360 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2562

@[simp] theorem pcI2563 : CycleSubmission.Artifact.artifact.instructionPC 2361 = 3033 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2361 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2563

@[simp] theorem pcI2564 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2565 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3034 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2362 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3171

@[simp] theorem pcI2566 : CycleSubmission.Artifact.artifact.instructionPC 2363 = 3037 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2363 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pc3174

@[simp] theorem pcI2585 : CycleSubmission.Artifact.artifact.instructionPC 2380 = 3056 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2380 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2585

@[simp] theorem pcI2586 : CycleSubmission.Artifact.artifact.instructionPC 2381 = 3057 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2381 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2586

@[simp] theorem pcI2587 : CycleSubmission.Artifact.artifact.instructionPC 2382 = 3060 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2382 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2587

@[simp] theorem pcI2594 : CycleSubmission.Artifact.artifact.instructionPC 2391 = 3073 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2391 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2594

@[simp] theorem pcI2630 : CycleSubmission.Artifact.artifact.instructionPC 2425 = 3114 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2425 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2630

@[simp] theorem pcI2647 : CycleSubmission.Artifact.artifact.instructionPC 2441 = 3140 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2441 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2647

@[simp] theorem pcI2698 : CycleSubmission.Artifact.artifact.instructionPC 2447 = 3148 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2447 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2698

@[simp] theorem pcI2699 : CycleSubmission.Artifact.artifact.instructionPC 2448 = 3151 := by
  rw [CycleSubmission.Global.PrefixPC.eq_old_tail12 2448 (by decide) (by decide)]
  exact Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs.pcI2699

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

end CycleSubmission.Global.ShiftPCs

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

/-- Instruction indices from 2135 on follow the `PUSH32` all-ones constant at 2134; their
program counters are computed from this anchor. -/
private theorem shiftAnchor : CycleSubmission.Artifact.artifact.instructionPC 2135 = 2807 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

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

@[simp] theorem pc3009 : CycleSubmission.Artifact.artifact.instructionPC 2227 = 2909 := by
  rw [show (2227:Nat)=2135+(2227-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3010 : CycleSubmission.Artifact.artifact.instructionPC 2228 = 2910 := by
  rw [show (2228:Nat)=2135+(2228-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3011 : CycleSubmission.Artifact.artifact.instructionPC 2229 = 2911 := by
  rw [show (2229:Nat)=2135+(2229-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3012 : CycleSubmission.Artifact.artifact.instructionPC 2230 = 2912 := by
  rw [show (2230:Nat)=2135+(2230-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3013 : CycleSubmission.Artifact.artifact.instructionPC 2231 = 2913 := by
  rw [show (2231:Nat)=2135+(2231-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

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

@[simp] theorem pc2888 : CycleSubmission.Artifact.artifact.instructionPC 2135 = 2807 := by
  rw [show (2135:Nat)=2135+(2135-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3125 : CycleSubmission.Artifact.artifact.instructionPC 2324 = 3022 := by
  rw [show (2324:Nat)=2135+(2324-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl







@[simp] theorem pc3171 : CycleSubmission.Artifact.artifact.instructionPC 2361 = 3065 := by
  rw [show (2361:Nat)=2135+(2361-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3174 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3068 := by
  rw [show (2362:Nat)=2135+(2362-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3175 : CycleSubmission.Artifact.artifact.instructionPC 2363 = 3069 := by
  rw [show (2363:Nat)=2135+(2363-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3176 : CycleSubmission.Artifact.artifact.instructionPC 2364 = 3070 := by
  rw [show (2364:Nat)=2135+(2364-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3177 : CycleSubmission.Artifact.artifact.instructionPC 2365 = 3071 := by
  rw [show (2365:Nat)=2135+(2365-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3178 : CycleSubmission.Artifact.artifact.instructionPC 2366 = 3072 := by
  rw [show (2366:Nat)=2135+(2366-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3179 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3073 := by
  rw [show (2367:Nat)=2135+(2367-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3180 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3074 := by
  rw [show (2368:Nat)=2135+(2368-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3181 : CycleSubmission.Artifact.artifact.instructionPC 2369 = 3075 := by
  rw [show (2369:Nat)=2135+(2369-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3182 : CycleSubmission.Artifact.artifact.instructionPC 2370 = 3076 := by
  rw [show (2370:Nat)=2135+(2370-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3183 : CycleSubmission.Artifact.artifact.instructionPC 2371 = 3077 := by
  rw [show (2371:Nat)=2135+(2371-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3184 : CycleSubmission.Artifact.artifact.instructionPC 2372 = 3078 := by
  rw [show (2372:Nat)=2135+(2372-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3185 : CycleSubmission.Artifact.artifact.instructionPC 2373 = 3079 := by
  rw [show (2373:Nat)=2135+(2373-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3186 : CycleSubmission.Artifact.artifact.instructionPC 2374 = 3080 := by
  rw [show (2374:Nat)=2135+(2374-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3187 : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3081 := by
  rw [show (2375:Nat)=2135+(2375-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3188 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3082 := by
  rw [show (2376:Nat)=2135+(2376-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3191 : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3085 := by
  rw [show (2377:Nat)=2135+(2377-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3192 : CycleSubmission.Artifact.artifact.instructionPC 2378 = 3086 := by
  rw [show (2378:Nat)=2135+(2378-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3214 : CycleSubmission.Artifact.artifact.instructionPC 2392 = 3106 := by
  rw [show (2392:Nat)=2135+(2392-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3215 : CycleSubmission.Artifact.artifact.instructionPC 2393 = 3107 := by
  rw [show (2393:Nat)=2135+(2393-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3216 : CycleSubmission.Artifact.artifact.instructionPC 2394 = 3108 := by
  rw [show (2394:Nat)=2135+(2394-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3219 : CycleSubmission.Artifact.artifact.instructionPC 2395 = 3111 := by
  rw [show (2395:Nat)=2135+(2395-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3220 : CycleSubmission.Artifact.artifact.instructionPC 2396 = 3112 := by
  rw [show (2396:Nat)=2135+(2396-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3221 : CycleSubmission.Artifact.artifact.instructionPC 2397 = 3113 := by
  rw [show (2397:Nat)=2135+(2397-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3222 : CycleSubmission.Artifact.artifact.instructionPC 2398 = 3114 := by
  rw [show (2398:Nat)=2135+(2398-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3223 : CycleSubmission.Artifact.artifact.instructionPC 2399 = 3115 := by
  rw [show (2399:Nat)=2135+(2399-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3226 : CycleSubmission.Artifact.artifact.instructionPC 2400 = 3118 := by
  rw [show (2400:Nat)=2135+(2400-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3227 : CycleSubmission.Artifact.artifact.instructionPC 2401 = 3119 := by
  rw [show (2401:Nat)=2135+(2401-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl


@[simp] theorem pc3228 : CycleSubmission.Artifact.artifact.instructionPC 2402 = 3120 := by
  rw [show (2402:Nat)=2135+(2402-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3229 : CycleSubmission.Artifact.artifact.instructionPC 2403 = 3121 := by
  rw [show (2403:Nat)=2135+(2403-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3230 : CycleSubmission.Artifact.artifact.instructionPC 2404 = 3122 := by
  rw [show (2404:Nat)=2135+(2404-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3231 : CycleSubmission.Artifact.artifact.instructionPC 2405 = 3123 := by
  rw [show (2405:Nat)=2135+(2405-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3232 : CycleSubmission.Artifact.artifact.instructionPC 2406 = 3124 := by
  rw [show (2406:Nat)=2135+(2406-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3233 : CycleSubmission.Artifact.artifact.instructionPC 2407 = 3125 := by
  rw [show (2407:Nat)=2135+(2407-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3234 : CycleSubmission.Artifact.artifact.instructionPC 2408 = 3126 := by
  rw [show (2408:Nat)=2135+(2408-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3235 : CycleSubmission.Artifact.artifact.instructionPC 2409 = 3127 := by
  rw [show (2409:Nat)=2135+(2409-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3236 : CycleSubmission.Artifact.artifact.instructionPC 2410 = 3128 := by
  rw [show (2410:Nat)=2135+(2410-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3237 : CycleSubmission.Artifact.artifact.instructionPC 2411 = 3129 := by
  rw [show (2411:Nat)=2135+(2411-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3238 : CycleSubmission.Artifact.artifact.instructionPC 2412 = 3130 := by
  rw [show (2412:Nat)=2135+(2412-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3239 : CycleSubmission.Artifact.artifact.instructionPC 2413 = 3131 := by
  rw [show (2413:Nat)=2135+(2413-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3240 : CycleSubmission.Artifact.artifact.instructionPC 2414 = 3132 := by
  rw [show (2414:Nat)=2135+(2414-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3241 : CycleSubmission.Artifact.artifact.instructionPC 2415 = 3133 := by
  rw [show (2415:Nat)=2135+(2415-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3242 : CycleSubmission.Artifact.artifact.instructionPC 2416 = 3134 := by
  rw [show (2416:Nat)=2135+(2416-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3243 : CycleSubmission.Artifact.artifact.instructionPC 2417 = 3135 := by
  rw [show (2417:Nat)=2135+(2417-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3244 : CycleSubmission.Artifact.artifact.instructionPC 2418 = 3136 := by
  rw [show (2418:Nat)=2135+(2418-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3246 : CycleSubmission.Artifact.artifact.instructionPC 2419 = 3138 := by
  rw [show (2419:Nat)=2135+(2419-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3247 : CycleSubmission.Artifact.artifact.instructionPC 2420 = 3139 := by
  rw [show (2420:Nat)=2135+(2420-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3248 : CycleSubmission.Artifact.artifact.instructionPC 2421 = 3140 := by
  rw [show (2421:Nat)=2135+(2421-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3251 : CycleSubmission.Artifact.artifact.instructionPC 2422 = 3143 := by
  rw [show (2422:Nat)=2135+(2422-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3252 : CycleSubmission.Artifact.artifact.instructionPC 2423 = 3144 := by
  rw [show (2423:Nat)=2135+(2423-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3185_compact : CycleSubmission.Artifact.artifact.instructionPC 2411 = 3129 := by
  rw [show (2411:Nat)=2135+(2411-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3256 : CycleSubmission.Artifact.artifact.instructionPC 2425 = 3148 := by
  rw [show (2425:Nat)=2135+(2425-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3257 : CycleSubmission.Artifact.artifact.instructionPC 2426 = 3149 := by
  rw [show (2426:Nat)=2135+(2426-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3258 : CycleSubmission.Artifact.artifact.instructionPC 2427 = 3150 := by
  rw [show (2427:Nat)=2135+(2427-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3261 : CycleSubmission.Artifact.artifact.instructionPC 2428 = 3153 := by
  rw [show (2428:Nat)=2135+(2428-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3262 : CycleSubmission.Artifact.artifact.instructionPC 2429 = 3154 := by
  rw [show (2429:Nat)=2135+(2429-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3263 : CycleSubmission.Artifact.artifact.instructionPC 2430 = 3155 := by
  rw [show (2430:Nat)=2135+(2430-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3264 : CycleSubmission.Artifact.artifact.instructionPC 2431 = 3156 := by
  rw [show (2431:Nat)=2135+(2431-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3265 : CycleSubmission.Artifact.artifact.instructionPC 2432 = 3157 := by
  rw [show (2432:Nat)=2135+(2432-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3268 : CycleSubmission.Artifact.artifact.instructionPC 2433 = 3160 := by
  rw [show (2433:Nat)=2135+(2433-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3269 : CycleSubmission.Artifact.artifact.instructionPC 2434 = 3161 := by
  rw [show (2434:Nat)=2135+(2434-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3270 : CycleSubmission.Artifact.artifact.instructionPC 2435 = 3162 := by
  rw [show (2435:Nat)=2135+(2435-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3271 : CycleSubmission.Artifact.artifact.instructionPC 2436 = 3163 := by
  rw [show (2436:Nat)=2135+(2436-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3274 : CycleSubmission.Artifact.artifact.instructionPC 2437 = 3166 := by
  rw [show (2437:Nat)=2135+(2437-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3276 : CycleSubmission.Artifact.artifact.instructionPC 2438 = 3167 := by
  rw [show (2438:Nat)=2135+(2438-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3279 : CycleSubmission.Artifact.artifact.instructionPC 2439 = 3170 := by
  rw [show (2439:Nat)=2135+(2439-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3281 : CycleSubmission.Artifact.artifact.instructionPC 2441 = 3172 := by
  rw [show (2441:Nat)=2135+(2441-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3282 : CycleSubmission.Artifact.artifact.instructionPC 2442 = 3173 := by
  rw [show (2442:Nat)=2135+(2442-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3285 : CycleSubmission.Artifact.artifact.instructionPC 2443 = 3176 := by
  rw [show (2443:Nat)=2135+(2443-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3198 : CycleSubmission.Artifact.artifact.instructionPC 2382 = 3092 := by
  rw [show (2382:Nat)=2135+(2382-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcM9b2525 : CycleSubmission.Artifact.artifact.instructionPC 2383 = 3093 := by
  rw [show (2383:Nat)=2135+(2383-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcM9b2526 : CycleSubmission.Artifact.artifact.instructionPC 2384 = 3094 := by
  rw [show (2384:Nat)=2135+(2384-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcM9b2527 : CycleSubmission.Artifact.artifact.instructionPC 2385 = 3095 := by
  rw [show (2385:Nat)=2135+(2385-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcM9b2528 : CycleSubmission.Artifact.artifact.instructionPC 2386 = 3096 := by
  rw [show (2386:Nat)=2135+(2386-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcM9b2529 : CycleSubmission.Artifact.artifact.instructionPC 2387 = 3099 := by
  rw [show (2387:Nat)=2135+(2387-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcM9b2530 : CycleSubmission.Artifact.artifact.instructionPC 2388 = 3100 := by
  rw [show (2388:Nat)=2135+(2388-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcM9b2531 : CycleSubmission.Artifact.artifact.instructionPC 2389 = 3103 := by
  rw [show (2389:Nat)=2135+(2389-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3346 : CycleSubmission.Artifact.artifact.instructionPC 2444 = 3177 := by
  rw [show (2444:Nat)=2135+(2444-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3347 : CycleSubmission.Artifact.artifact.instructionPC 2445 = 3178 := by
  rw [show (2445:Nat)=2135+(2445-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pc3265a : CycleSubmission.Artifact.artifact.instructionPC 2452 = 3189 := by
  rw [show (2452:Nat)=2135+(2452-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl


@[simp] theorem pc3265c : CycleSubmission.Artifact.artifact.instructionPC 2456 = 3196 := by
  rw [show (2456:Nat)=2135+(2456-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl


@[simp] theorem pc3265e : CycleSubmission.Artifact.artifact.instructionPC 2458 = 3200 := by
  rw [show (2458:Nat)=2135+(2458-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

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

@[simp] theorem pcSaturate2992 : CycleSubmission.Artifact.artifact.instructionPC 2309 = 3003 := by
  rw [show (2309:Nat)=2135+(2309-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcSaturate2993 : CycleSubmission.Artifact.artifact.instructionPC 2310 = 3004 := by
  rw [show (2310:Nat)=2135+(2310-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem earlyExtraPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2667 = 3454 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2668 = 3455 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2669 = 3456 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2670 = 3457 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2888 : CycleSubmission.Artifact.artifact.instructionPC 2671 = 3458 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2889 : CycleSubmission.Artifact.artifact.instructionPC 2672 = 3459 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2890 : CycleSubmission.Artifact.artifact.instructionPC 2673 = 3460 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2891 : CycleSubmission.Artifact.artifact.instructionPC 2674 = 3463 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2892 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3464 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2893 : CycleSubmission.Artifact.artifact.instructionPC 2675 = 3464 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2894 : CycleSubmission.Artifact.artifact.instructionPC 2676 = 3467 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2934 : CycleSubmission.Artifact.artifact.instructionPC 2677 = 3468 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2935 : CycleSubmission.Artifact.artifact.instructionPC 2678 = 3469 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2936 : CycleSubmission.Artifact.artifact.instructionPC 2679 = 3472 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2937 : CycleSubmission.Artifact.artifact.instructionPC 2680 = 3473 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2938 : CycleSubmission.Artifact.artifact.instructionPC 2681 = 3475 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2939 : CycleSubmission.Artifact.artifact.instructionPC 2682 = 3476 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2940 : CycleSubmission.Artifact.artifact.instructionPC 2683 = 3477 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2941 : CycleSubmission.Artifact.artifact.instructionPC 2684 = 3478 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2942 : CycleSubmission.Artifact.artifact.instructionPC 2685 = 3479 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem earlyExtraPC2943 : CycleSubmission.Artifact.artifact.instructionPC 2686 = 3482 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl


@[simp] theorem pcC3009 : CycleSubmission.Artifact.artifact.instructionPC 2366 = 3072 := by
  rw [show (2366:Nat)=2135+(2366-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcC3010 : CycleSubmission.Artifact.artifact.instructionPC 2367 = 3073 := by
  rw [show (2367:Nat)=2135+(2367-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcC3011 : CycleSubmission.Artifact.artifact.instructionPC 2368 = 3074 := by
  rw [show (2368:Nat)=2135+(2368-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcC3019 : CycleSubmission.Artifact.artifact.instructionPC 2375 = 3081 := by
  rw [show (2375:Nat)=2135+(2375-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcC3020 : CycleSubmission.Artifact.artifact.instructionPC 2376 = 3082 := by
  rw [show (2376:Nat)=2135+(2376-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcC3021 : CycleSubmission.Artifact.artifact.instructionPC 2377 = 3085 := by
  rw [show (2377:Nat)=2135+(2377-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl


@[simp] theorem pcC3078 : CycleSubmission.Artifact.artifact.instructionPC 2428 = 3153 := by
  rw [show (2428:Nat)=2135+(2428-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcC3082 : CycleSubmission.Artifact.artifact.instructionPC 2432 = 3157 := by
  rw [show (2432:Nat)=2135+(2432-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcC3083 : CycleSubmission.Artifact.artifact.instructionPC 2433 = 3160 := by
  rw [show (2433:Nat)=2135+(2433-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl


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

@[simp] theorem pcT2329 : CycleSubmission.Artifact.artifact.instructionPC 2312 = 3006 := by
  rw [show (2312:Nat)=2135+(2312-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2330 : CycleSubmission.Artifact.artifact.instructionPC 2313 = 3007 := by
  rw [show (2313:Nat)=2135+(2313-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2331 : CycleSubmission.Artifact.artifact.instructionPC 2314 = 3008 := by
  rw [show (2314:Nat)=2135+(2314-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2332 : CycleSubmission.Artifact.artifact.instructionPC 2315 = 3009 := by
  rw [show (2315:Nat)=2135+(2315-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2336 : CycleSubmission.Artifact.artifact.instructionPC 2319 = 3015 := by
  rw [show (2319:Nat)=2135+(2319-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2337 : CycleSubmission.Artifact.artifact.instructionPC 2320 = 3016 := by
  rw [show (2320:Nat)=2135+(2320-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2338 : CycleSubmission.Artifact.artifact.instructionPC 2321 = 3017 := by
  rw [show (2321:Nat)=2135+(2321-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2339 : CycleSubmission.Artifact.artifact.instructionPC 2322 = 3018 := by
  rw [show (2322:Nat)=2135+(2322-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2340 : CycleSubmission.Artifact.artifact.instructionPC 2323 = 3021 := by
  rw [show (2323:Nat)=2135+(2323-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2341 : CycleSubmission.Artifact.artifact.instructionPC 2324 = 3022 := by
  rw [show (2324:Nat)=2135+(2324-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2342 : CycleSubmission.Artifact.artifact.instructionPC 2325 = 3023 := by
  rw [show (2325:Nat)=2135+(2325-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2343 : CycleSubmission.Artifact.artifact.instructionPC 2326 = 3024 := by
  rw [show (2326:Nat)=2135+(2326-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2344 : CycleSubmission.Artifact.artifact.instructionPC 2327 = 3025 := by
  rw [show (2327:Nat)=2135+(2327-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2345 : CycleSubmission.Artifact.artifact.instructionPC 2328 = 3026 := by
  rw [show (2328:Nat)=2135+(2328-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2346 : CycleSubmission.Artifact.artifact.instructionPC 2329 = 3027 := by
  rw [show (2329:Nat)=2135+(2329-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2347 : CycleSubmission.Artifact.artifact.instructionPC 2330 = 3028 := by
  rw [show (2330:Nat)=2135+(2330-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2348 : CycleSubmission.Artifact.artifact.instructionPC 2331 = 3029 := by
  rw [show (2331:Nat)=2135+(2331-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2349 : CycleSubmission.Artifact.artifact.instructionPC 2332 = 3032 := by
  rw [show (2332:Nat)=2135+(2332-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2350 : CycleSubmission.Artifact.artifact.instructionPC 2333 = 3033 := by
  rw [show (2333:Nat)=2135+(2333-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2351 : CycleSubmission.Artifact.artifact.instructionPC 2334 = 3034 := by
  rw [show (2334:Nat)=2135+(2334-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2352 : CycleSubmission.Artifact.artifact.instructionPC 2335 = 3035 := by
  rw [show (2335:Nat)=2135+(2335-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2353 : CycleSubmission.Artifact.artifact.instructionPC 2336 = 3036 := by
  rw [show (2336:Nat)=2135+(2336-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2354 : CycleSubmission.Artifact.artifact.instructionPC 2337 = 3037 := by
  rw [show (2337:Nat)=2135+(2337-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2355 : CycleSubmission.Artifact.artifact.instructionPC 2338 = 3038 := by
  rw [show (2338:Nat)=2135+(2338-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2356 : CycleSubmission.Artifact.artifact.instructionPC 2339 = 3039 := by
  rw [show (2339:Nat)=2135+(2339-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2357 : CycleSubmission.Artifact.artifact.instructionPC 2340 = 3040 := by
  rw [show (2340:Nat)=2135+(2340-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2358 : CycleSubmission.Artifact.artifact.instructionPC 2341 = 3041 := by
  rw [show (2341:Nat)=2135+(2341-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2359 : CycleSubmission.Artifact.artifact.instructionPC 2342 = 3042 := by
  rw [show (2342:Nat)=2135+(2342-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2360 : CycleSubmission.Artifact.artifact.instructionPC 2343 = 3043 := by
  rw [show (2343:Nat)=2135+(2343-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2361 : CycleSubmission.Artifact.artifact.instructionPC 2344 = 3044 := by
  rw [show (2344:Nat)=2135+(2344-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2362 : CycleSubmission.Artifact.artifact.instructionPC 2345 = 3045 := by
  rw [show (2345:Nat)=2135+(2345-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2363 : CycleSubmission.Artifact.artifact.instructionPC 2346 = 3046 := by
  rw [show (2346:Nat)=2135+(2346-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2364 : CycleSubmission.Artifact.artifact.instructionPC 2347 = 3047 := by
  rw [show (2347:Nat)=2135+(2347-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2365 : CycleSubmission.Artifact.artifact.instructionPC 2348 = 3050 := by
  rw [show (2348:Nat)=2135+(2348-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2366 : CycleSubmission.Artifact.artifact.instructionPC 2349 = 3051 := by
  rw [show (2349:Nat)=2135+(2349-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2367 : CycleSubmission.Artifact.artifact.instructionPC 2350 = 3052 := by
  rw [show (2350:Nat)=2135+(2350-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2368 : CycleSubmission.Artifact.artifact.instructionPC 2351 = 3053 := by
  rw [show (2351:Nat)=2135+(2351-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2369 : CycleSubmission.Artifact.artifact.instructionPC 2352 = 3054 := by
  rw [show (2352:Nat)=2135+(2352-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2370 : CycleSubmission.Artifact.artifact.instructionPC 2353 = 3057 := by
  rw [show (2353:Nat)=2135+(2353-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2371 : CycleSubmission.Artifact.artifact.instructionPC 2354 = 3058 := by
  rw [show (2354:Nat)=2135+(2354-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2372 : CycleSubmission.Artifact.artifact.instructionPC 2355 = 3059 := by
  rw [show (2355:Nat)=2135+(2355-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2522 : CycleSubmission.Artifact.artifact.instructionPC 2378 = 3086 := by
  rw [show (2378:Nat)=2135+(2378-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2647 : CycleSubmission.Artifact.artifact.instructionPC 2451 = 3188 := by
  rw [show (2451:Nat)=2135+(2451-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2649 : CycleSubmission.Artifact.artifact.instructionPC 2453 = 3192 := by
  rw [show (2453:Nat)=2135+(2453-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2651 : CycleSubmission.Artifact.artifact.instructionPC 2455 = 3195 := by
  rw [show (2455:Nat)=2135+(2455-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcT2653 : CycleSubmission.Artifact.artifact.instructionPC 2457 = 3197 := by
  rw [show (2457:Nat)=2135+(2457-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

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

@[simp] theorem pcI2319 : CycleSubmission.Artifact.artifact.instructionPC 2136 = 2808 := by
  rw [show (2136:Nat)=2135+(2136-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2320 : CycleSubmission.Artifact.artifact.instructionPC 2137 = 2809 := by
  rw [show (2137:Nat)=2135+(2137-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2321 : CycleSubmission.Artifact.artifact.instructionPC 2138 = 2810 := by
  rw [show (2138:Nat)=2135+(2138-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2322 : CycleSubmission.Artifact.artifact.instructionPC 2139 = 2811 := by
  rw [show (2139:Nat)=2135+(2139-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2323 : CycleSubmission.Artifact.artifact.instructionPC 2140 = 2812 := by
  rw [show (2140:Nat)=2135+(2140-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2326 : CycleSubmission.Artifact.artifact.instructionPC 2141 = 2813 := by
  rw [show (2141:Nat)=2135+(2141-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2327 : CycleSubmission.Artifact.artifact.instructionPC 2142 = 2814 := by
  rw [show (2142:Nat)=2135+(2142-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2328 : CycleSubmission.Artifact.artifact.instructionPC 2143 = 2815 := by
  rw [show (2143:Nat)=2135+(2143-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2329 : CycleSubmission.Artifact.artifact.instructionPC 2144 = 2816 := by
  rw [show (2144:Nat)=2135+(2144-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2330 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2331 : CycleSubmission.Artifact.artifact.instructionPC 2145 = 2817 := by
  rw [show (2145:Nat)=2135+(2145-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2332 : CycleSubmission.Artifact.artifact.instructionPC 2146 = 2818 := by
  rw [show (2146:Nat)=2135+(2146-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2333 : CycleSubmission.Artifact.artifact.instructionPC 2147 = 2819 := by
  rw [show (2147:Nat)=2135+(2147-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2334 : CycleSubmission.Artifact.artifact.instructionPC 2148 = 2820 := by
  rw [show (2148:Nat)=2135+(2148-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2335 : CycleSubmission.Artifact.artifact.instructionPC 2149 = 2821 := by
  rw [show (2149:Nat)=2135+(2149-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2336 : CycleSubmission.Artifact.artifact.instructionPC 2150 = 2822 := by
  rw [show (2150:Nat)=2135+(2150-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2337 : CycleSubmission.Artifact.artifact.instructionPC 2151 = 2823 := by
  rw [show (2151:Nat)=2135+(2151-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2338 : CycleSubmission.Artifact.artifact.instructionPC 2152 = 2824 := by
  rw [show (2152:Nat)=2135+(2152-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2339 : CycleSubmission.Artifact.artifact.instructionPC 2153 = 2825 := by
  rw [show (2153:Nat)=2135+(2153-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2340 : CycleSubmission.Artifact.artifact.instructionPC 2154 = 2826 := by
  rw [show (2154:Nat)=2135+(2154-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2341 : CycleSubmission.Artifact.artifact.instructionPC 2155 = 2829 := by
  rw [show (2155:Nat)=2135+(2155-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2342 : CycleSubmission.Artifact.artifact.instructionPC 2156 = 2830 := by
  rw [show (2156:Nat)=2135+(2156-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2343 : CycleSubmission.Artifact.artifact.instructionPC 2157 = 2831 := by
  rw [show (2157:Nat)=2135+(2157-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2344 : CycleSubmission.Artifact.artifact.instructionPC 2158 = 2832 := by
  rw [show (2158:Nat)=2135+(2158-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2345 : CycleSubmission.Artifact.artifact.instructionPC 2159 = 2833 := by
  rw [show (2159:Nat)=2135+(2159-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2346 : CycleSubmission.Artifact.artifact.instructionPC 2160 = 2834 := by
  rw [show (2160:Nat)=2135+(2160-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2347 : CycleSubmission.Artifact.artifact.instructionPC 2161 = 2835 := by
  rw [show (2161:Nat)=2135+(2161-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

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

@[simp] theorem pcI2360 : CycleSubmission.Artifact.artifact.instructionPC 2162 = 2836 := by
  rw [show (2162:Nat)=2135+(2162-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2361 : CycleSubmission.Artifact.artifact.instructionPC 2163 = 2837 := by
  rw [show (2163:Nat)=2135+(2163-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2362 : CycleSubmission.Artifact.artifact.instructionPC 2164 = 2838 := by
  rw [show (2164:Nat)=2135+(2164-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2363 : CycleSubmission.Artifact.artifact.instructionPC 2165 = 2839 := by
  rw [show (2165:Nat)=2135+(2165-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2364 : CycleSubmission.Artifact.artifact.instructionPC 2166 = 2840 := by
  rw [show (2166:Nat)=2135+(2166-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2365 : CycleSubmission.Artifact.artifact.instructionPC 2167 = 2841 := by
  rw [show (2167:Nat)=2135+(2167-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2366 : CycleSubmission.Artifact.artifact.instructionPC 2168 = 2842 := by
  rw [show (2168:Nat)=2135+(2168-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2367 : CycleSubmission.Artifact.artifact.instructionPC 2169 = 2843 := by
  rw [show (2169:Nat)=2135+(2169-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2368 : CycleSubmission.Artifact.artifact.instructionPC 2170 = 2844 := by
  rw [show (2170:Nat)=2135+(2170-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2369 : CycleSubmission.Artifact.artifact.instructionPC 2171 = 2845 := by
  rw [show (2171:Nat)=2135+(2171-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2370 : CycleSubmission.Artifact.artifact.instructionPC 2172 = 2846 := by
  rw [show (2172:Nat)=2135+(2172-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2371 : CycleSubmission.Artifact.artifact.instructionPC 2173 = 2847 := by
  rw [show (2173:Nat)=2135+(2173-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2372 : CycleSubmission.Artifact.artifact.instructionPC 2174 = 2848 := by
  rw [show (2174:Nat)=2135+(2174-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2373 : CycleSubmission.Artifact.artifact.instructionPC 2175 = 2849 := by
  rw [show (2175:Nat)=2135+(2175-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2374 : CycleSubmission.Artifact.artifact.instructionPC 2176 = 2850 := by
  rw [show (2176:Nat)=2135+(2176-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2375 : CycleSubmission.Artifact.artifact.instructionPC 2177 = 2853 := by
  rw [show (2177:Nat)=2135+(2177-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2376 : CycleSubmission.Artifact.artifact.instructionPC 2178 = 2854 := by
  rw [show (2178:Nat)=2135+(2178-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2377 : CycleSubmission.Artifact.artifact.instructionPC 2179 = 2855 := by
  rw [show (2179:Nat)=2135+(2179-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2378 : CycleSubmission.Artifact.artifact.instructionPC 2180 = 2856 := by
  rw [show (2180:Nat)=2135+(2180-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2379 : CycleSubmission.Artifact.artifact.instructionPC 2181 = 2857 := by
  rw [show (2181:Nat)=2135+(2181-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2380 : CycleSubmission.Artifact.artifact.instructionPC 2182 = 2860 := by
  rw [show (2182:Nat)=2135+(2182-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2381 : CycleSubmission.Artifact.artifact.instructionPC 2183 = 2861 := by
  rw [show (2183:Nat)=2135+(2183-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2382 : CycleSubmission.Artifact.artifact.instructionPC 2184 = 2862 := by
  rw [show (2184:Nat)=2135+(2184-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2383 : CycleSubmission.Artifact.artifact.instructionPC 2185 = 2863 := by
  rw [show (2185:Nat)=2135+(2185-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2384 : CycleSubmission.Artifact.artifact.instructionPC 2186 = 2864 := by
  rw [show (2186:Nat)=2135+(2186-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2385 : CycleSubmission.Artifact.artifact.instructionPC 2187 = 2865 := by
  rw [show (2187:Nat)=2135+(2187-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2386 : CycleSubmission.Artifact.artifact.instructionPC 2188 = 2866 := by
  rw [show (2188:Nat)=2135+(2188-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2387 : CycleSubmission.Artifact.artifact.instructionPC 2189 = 2867 := by
  rw [show (2189:Nat)=2135+(2189-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2388 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2389 : CycleSubmission.Artifact.artifact.instructionPC 2190 = 2868 := by
  rw [show (2190:Nat)=2135+(2190-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2390 : CycleSubmission.Artifact.artifact.instructionPC 2191 = 2869 := by
  rw [show (2191:Nat)=2135+(2191-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2391 : CycleSubmission.Artifact.artifact.instructionPC 2192 = 2870 := by
  rw [show (2192:Nat)=2135+(2192-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2392 : CycleSubmission.Artifact.artifact.instructionPC 2193 = 2871 := by
  rw [show (2193:Nat)=2135+(2193-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2393 : CycleSubmission.Artifact.artifact.instructionPC 2194 = 2872 := by
  rw [show (2194:Nat)=2135+(2194-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2394 : CycleSubmission.Artifact.artifact.instructionPC 2195 = 2873 := by
  rw [show (2195:Nat)=2135+(2195-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2395 : CycleSubmission.Artifact.artifact.instructionPC 2196 = 2874 := by
  rw [show (2196:Nat)=2135+(2196-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2396 : CycleSubmission.Artifact.artifact.instructionPC 2197 = 2875 := by
  rw [show (2197:Nat)=2135+(2197-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2397 : CycleSubmission.Artifact.artifact.instructionPC 2198 = 2876 := by
  rw [show (2198:Nat)=2135+(2198-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2398 : CycleSubmission.Artifact.artifact.instructionPC 2199 = 2877 := by
  rw [show (2199:Nat)=2135+(2199-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2399 : CycleSubmission.Artifact.artifact.instructionPC 2200 = 2878 := by
  rw [show (2200:Nat)=2135+(2200-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2400 : CycleSubmission.Artifact.artifact.instructionPC 2201 = 2879 := by
  rw [show (2201:Nat)=2135+(2201-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2401 : CycleSubmission.Artifact.artifact.instructionPC 2202 = 2880 := by
  rw [show (2202:Nat)=2135+(2202-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2402 : CycleSubmission.Artifact.artifact.instructionPC 2203 = 2881 := by
  rw [show (2203:Nat)=2135+(2203-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2403 : CycleSubmission.Artifact.artifact.instructionPC 2204 = 2882 := by
  rw [show (2204:Nat)=2135+(2204-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2404 : CycleSubmission.Artifact.artifact.instructionPC 2205 = 2885 := by
  rw [show (2205:Nat)=2135+(2205-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2405 : CycleSubmission.Artifact.artifact.instructionPC 2206 = 2886 := by
  rw [show (2206:Nat)=2135+(2206-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2406 : CycleSubmission.Artifact.artifact.instructionPC 2207 = 2887 := by
  rw [show (2207:Nat)=2135+(2207-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2407 : CycleSubmission.Artifact.artifact.instructionPC 2208 = 2888 := by
  rw [show (2208:Nat)=2135+(2208-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2408 : CycleSubmission.Artifact.artifact.instructionPC 2209 = 2889 := by
  rw [show (2209:Nat)=2135+(2209-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2409 : CycleSubmission.Artifact.artifact.instructionPC 2210 = 2892 := by
  rw [show (2210:Nat)=2135+(2210-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2410 : CycleSubmission.Artifact.artifact.instructionPC 2211 = 2893 := by
  rw [show (2211:Nat)=2135+(2211-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2411 : CycleSubmission.Artifact.artifact.instructionPC 2212 = 2894 := by
  rw [show (2212:Nat)=2135+(2212-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2412 : CycleSubmission.Artifact.artifact.instructionPC 2213 = 2895 := by
  rw [show (2213:Nat)=2135+(2213-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2413 : CycleSubmission.Artifact.artifact.instructionPC 2214 = 2896 := by
  rw [show (2214:Nat)=2135+(2214-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2414 : CycleSubmission.Artifact.artifact.instructionPC 2215 = 2897 := by
  rw [show (2215:Nat)=2135+(2215-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2415 : CycleSubmission.Artifact.artifact.instructionPC 2216 = 2898 := by
  rw [show (2216:Nat)=2135+(2216-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2416 : CycleSubmission.Artifact.artifact.instructionPC 2217 = 2899 := by
  rw [show (2217:Nat)=2135+(2217-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2417 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2418 : CycleSubmission.Artifact.artifact.instructionPC 2218 = 2900 := by
  rw [show (2218:Nat)=2135+(2218-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2419 : CycleSubmission.Artifact.artifact.instructionPC 2219 = 2901 := by
  rw [show (2219:Nat)=2135+(2219-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2420 : CycleSubmission.Artifact.artifact.instructionPC 2220 = 2902 := by
  rw [show (2220:Nat)=2135+(2220-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2421 : CycleSubmission.Artifact.artifact.instructionPC 2221 = 2903 := by
  rw [show (2221:Nat)=2135+(2221-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2422 : CycleSubmission.Artifact.artifact.instructionPC 2222 = 2904 := by
  rw [show (2222:Nat)=2135+(2222-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2423 : CycleSubmission.Artifact.artifact.instructionPC 2223 = 2905 := by
  rw [show (2223:Nat)=2135+(2223-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2424 : CycleSubmission.Artifact.artifact.instructionPC 2224 = 2906 := by
  rw [show (2224:Nat)=2135+(2224-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2425 : CycleSubmission.Artifact.artifact.instructionPC 2225 = 2907 := by
  rw [show (2225:Nat)=2135+(2225-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2426 : CycleSubmission.Artifact.artifact.instructionPC 2226 = 2908 := by
  rw [show (2226:Nat)=2135+(2226-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2432 : CycleSubmission.Artifact.artifact.instructionPC 2232 = 2914 := by
  rw [show (2232:Nat)=2135+(2232-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2433 : CycleSubmission.Artifact.artifact.instructionPC 2233 = 2917 := by
  rw [show (2233:Nat)=2135+(2233-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2434 : CycleSubmission.Artifact.artifact.instructionPC 2234 = 2918 := by
  rw [show (2234:Nat)=2135+(2234-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2435 : CycleSubmission.Artifact.artifact.instructionPC 2235 = 2919 := by
  rw [show (2235:Nat)=2135+(2235-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2436 : CycleSubmission.Artifact.artifact.instructionPC 2236 = 2920 := by
  rw [show (2236:Nat)=2135+(2236-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2437 : CycleSubmission.Artifact.artifact.instructionPC 2237 = 2921 := by
  rw [show (2237:Nat)=2135+(2237-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2438 : CycleSubmission.Artifact.artifact.instructionPC 2238 = 2924 := by
  rw [show (2238:Nat)=2135+(2238-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2439 : CycleSubmission.Artifact.artifact.instructionPC 2239 = 2925 := by
  rw [show (2239:Nat)=2135+(2239-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2440 : CycleSubmission.Artifact.artifact.instructionPC 2240 = 2926 := by
  rw [show (2240:Nat)=2135+(2240-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2441 : CycleSubmission.Artifact.artifact.instructionPC 2241 = 2927 := by
  rw [show (2241:Nat)=2135+(2241-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2442 : CycleSubmission.Artifact.artifact.instructionPC 2242 = 2928 := by
  rw [show (2242:Nat)=2135+(2242-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2443 : CycleSubmission.Artifact.artifact.instructionPC 2243 = 2929 := by
  rw [show (2243:Nat)=2135+(2243-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2444 : CycleSubmission.Artifact.artifact.instructionPC 2244 = 2930 := by
  rw [show (2244:Nat)=2135+(2244-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2445 : CycleSubmission.Artifact.artifact.instructionPC 2245 = 2931 := by
  rw [show (2245:Nat)=2135+(2245-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2446 : CycleSubmission.Artifact.artifact.instructionPC 2246 = 2932 := by
  rw [show (2246:Nat)=2135+(2246-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2447 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2448 : CycleSubmission.Artifact.artifact.instructionPC 2247 = 2933 := by
  rw [show (2247:Nat)=2135+(2247-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2449 : CycleSubmission.Artifact.artifact.instructionPC 2248 = 2934 := by
  rw [show (2248:Nat)=2135+(2248-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2450 : CycleSubmission.Artifact.artifact.instructionPC 2249 = 2935 := by
  rw [show (2249:Nat)=2135+(2249-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2451 : CycleSubmission.Artifact.artifact.instructionPC 2250 = 2936 := by
  rw [show (2250:Nat)=2135+(2250-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2452 : CycleSubmission.Artifact.artifact.instructionPC 2251 = 2937 := by
  rw [show (2251:Nat)=2135+(2251-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2453 : CycleSubmission.Artifact.artifact.instructionPC 2252 = 2938 := by
  rw [show (2252:Nat)=2135+(2252-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2454 : CycleSubmission.Artifact.artifact.instructionPC 2253 = 2939 := by
  rw [show (2253:Nat)=2135+(2253-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2455 : CycleSubmission.Artifact.artifact.instructionPC 2254 = 2940 := by
  rw [show (2254:Nat)=2135+(2254-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2456 : CycleSubmission.Artifact.artifact.instructionPC 2255 = 2941 := by
  rw [show (2255:Nat)=2135+(2255-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2457 : CycleSubmission.Artifact.artifact.instructionPC 2256 = 2942 := by
  rw [show (2256:Nat)=2135+(2256-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2458 : CycleSubmission.Artifact.artifact.instructionPC 2257 = 2943 := by
  rw [show (2257:Nat)=2135+(2257-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2459 : CycleSubmission.Artifact.artifact.instructionPC 2258 = 2944 := by
  rw [show (2258:Nat)=2135+(2258-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2460 : CycleSubmission.Artifact.artifact.instructionPC 2259 = 2945 := by
  rw [show (2259:Nat)=2135+(2259-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2461 : CycleSubmission.Artifact.artifact.instructionPC 2260 = 2946 := by
  rw [show (2260:Nat)=2135+(2260-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2462 : CycleSubmission.Artifact.artifact.instructionPC 2261 = 2947 := by
  rw [show (2261:Nat)=2135+(2261-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2463 : CycleSubmission.Artifact.artifact.instructionPC 2262 = 2950 := by
  rw [show (2262:Nat)=2135+(2262-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2464 : CycleSubmission.Artifact.artifact.instructionPC 2263 = 2951 := by
  rw [show (2263:Nat)=2135+(2263-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2465 : CycleSubmission.Artifact.artifact.instructionPC 2264 = 2952 := by
  rw [show (2264:Nat)=2135+(2264-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2466 : CycleSubmission.Artifact.artifact.instructionPC 2265 = 2953 := by
  rw [show (2265:Nat)=2135+(2265-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2467 : CycleSubmission.Artifact.artifact.instructionPC 2266 = 2954 := by
  rw [show (2266:Nat)=2135+(2266-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2468 : CycleSubmission.Artifact.artifact.instructionPC 2267 = 2957 := by
  rw [show (2267:Nat)=2135+(2267-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2469 : CycleSubmission.Artifact.artifact.instructionPC 2268 = 2958 := by
  rw [show (2268:Nat)=2135+(2268-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2470 : CycleSubmission.Artifact.artifact.instructionPC 2269 = 2959 := by
  rw [show (2269:Nat)=2135+(2269-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2471 : CycleSubmission.Artifact.artifact.instructionPC 2270 = 2960 := by
  rw [show (2270:Nat)=2135+(2270-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2472 : CycleSubmission.Artifact.artifact.instructionPC 2271 = 2961 := by
  rw [show (2271:Nat)=2135+(2271-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2473 : CycleSubmission.Artifact.artifact.instructionPC 2272 = 2962 := by
  rw [show (2272:Nat)=2135+(2272-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2474 : CycleSubmission.Artifact.artifact.instructionPC 2273 = 2963 := by
  rw [show (2273:Nat)=2135+(2273-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2475 : CycleSubmission.Artifact.artifact.instructionPC 2274 = 2964 := by
  rw [show (2274:Nat)=2135+(2274-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2476 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2477 : CycleSubmission.Artifact.artifact.instructionPC 2275 = 2965 := by
  rw [show (2275:Nat)=2135+(2275-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2478 : CycleSubmission.Artifact.artifact.instructionPC 2276 = 2966 := by
  rw [show (2276:Nat)=2135+(2276-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2479 : CycleSubmission.Artifact.artifact.instructionPC 2277 = 2967 := by
  rw [show (2277:Nat)=2135+(2277-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2480 : CycleSubmission.Artifact.artifact.instructionPC 2278 = 2968 := by
  rw [show (2278:Nat)=2135+(2278-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2481 : CycleSubmission.Artifact.artifact.instructionPC 2279 = 2969 := by
  rw [show (2279:Nat)=2135+(2279-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2482 : CycleSubmission.Artifact.artifact.instructionPC 2280 = 2970 := by
  rw [show (2280:Nat)=2135+(2280-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2483 : CycleSubmission.Artifact.artifact.instructionPC 2281 = 2971 := by
  rw [show (2281:Nat)=2135+(2281-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2484 : CycleSubmission.Artifact.artifact.instructionPC 2282 = 2972 := by
  rw [show (2282:Nat)=2135+(2282-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2485 : CycleSubmission.Artifact.artifact.instructionPC 2283 = 2973 := by
  rw [show (2283:Nat)=2135+(2283-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2486 : CycleSubmission.Artifact.artifact.instructionPC 2284 = 2974 := by
  rw [show (2284:Nat)=2135+(2284-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2487 : CycleSubmission.Artifact.artifact.instructionPC 2285 = 2975 := by
  rw [show (2285:Nat)=2135+(2285-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2488 : CycleSubmission.Artifact.artifact.instructionPC 2286 = 2976 := by
  rw [show (2286:Nat)=2135+(2286-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2489 : CycleSubmission.Artifact.artifact.instructionPC 2287 = 2977 := by
  rw [show (2287:Nat)=2135+(2287-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2490 : CycleSubmission.Artifact.artifact.instructionPC 2288 = 2978 := by
  rw [show (2288:Nat)=2135+(2288-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2491 : CycleSubmission.Artifact.artifact.instructionPC 2289 = 2979 := by
  rw [show (2289:Nat)=2135+(2289-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2492 : CycleSubmission.Artifact.artifact.instructionPC 2290 = 2982 := by
  rw [show (2290:Nat)=2135+(2290-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2493 : CycleSubmission.Artifact.artifact.instructionPC 2291 = 2983 := by
  rw [show (2291:Nat)=2135+(2291-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2494 : CycleSubmission.Artifact.artifact.instructionPC 2292 = 2984 := by
  rw [show (2292:Nat)=2135+(2292-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2495 : CycleSubmission.Artifact.artifact.instructionPC 2293 = 2985 := by
  rw [show (2293:Nat)=2135+(2293-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2496 : CycleSubmission.Artifact.artifact.instructionPC 2294 = 2986 := by
  rw [show (2294:Nat)=2135+(2294-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2497 : CycleSubmission.Artifact.artifact.instructionPC 2295 = 2989 := by
  rw [show (2295:Nat)=2135+(2295-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2498 : CycleSubmission.Artifact.artifact.instructionPC 2296 = 2990 := by
  rw [show (2296:Nat)=2135+(2296-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2499 : CycleSubmission.Artifact.artifact.instructionPC 2297 = 2991 := by
  rw [show (2297:Nat)=2135+(2297-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2500 : CycleSubmission.Artifact.artifact.instructionPC 2298 = 2992 := by
  rw [show (2298:Nat)=2135+(2298-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2501 : CycleSubmission.Artifact.artifact.instructionPC 2299 = 2993 := by
  rw [show (2299:Nat)=2135+(2299-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2502 : CycleSubmission.Artifact.artifact.instructionPC 2300 = 2994 := by
  rw [show (2300:Nat)=2135+(2300-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2503 : CycleSubmission.Artifact.artifact.instructionPC 2301 = 2995 := by
  rw [show (2301:Nat)=2135+(2301-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2504 : CycleSubmission.Artifact.artifact.instructionPC 2302 = 2996 := by
  rw [show (2302:Nat)=2135+(2302-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2505 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2506 : CycleSubmission.Artifact.artifact.instructionPC 2303 = 2997 := by
  rw [show (2303:Nat)=2135+(2303-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2507 : CycleSubmission.Artifact.artifact.instructionPC 2304 = 2998 := by
  rw [show (2304:Nat)=2135+(2304-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2508 : CycleSubmission.Artifact.artifact.instructionPC 2305 = 2999 := by
  rw [show (2305:Nat)=2135+(2305-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2509 : CycleSubmission.Artifact.artifact.instructionPC 2306 = 3000 := by
  rw [show (2306:Nat)=2135+(2306-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2510 : CycleSubmission.Artifact.artifact.instructionPC 2307 = 3001 := by
  rw [show (2307:Nat)=2135+(2307-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2511 : CycleSubmission.Artifact.artifact.instructionPC 2308 = 3002 := by
  rw [show (2308:Nat)=2135+(2308-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2514 : CycleSubmission.Artifact.artifact.instructionPC 2311 = 3005 := by
  rw [show (2311:Nat)=2135+(2311-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2519 : CycleSubmission.Artifact.artifact.instructionPC 2316 = 3010 := by
  rw [show (2316:Nat)=2135+(2316-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2520 : CycleSubmission.Artifact.artifact.instructionPC 2317 = 3011 := by
  rw [show (2317:Nat)=2135+(2317-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2521 : CycleSubmission.Artifact.artifact.instructionPC 2318 = 3014 := by
  rw [show (2318:Nat)=2135+(2318-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2559 : CycleSubmission.Artifact.artifact.instructionPC 2356 = 3060 := by
  rw [show (2356:Nat)=2135+(2356-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2560 : CycleSubmission.Artifact.artifact.instructionPC 2357 = 3061 := by
  rw [show (2357:Nat)=2135+(2357-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2561 : CycleSubmission.Artifact.artifact.instructionPC 2358 = 3062 := by
  rw [show (2358:Nat)=2135+(2358-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2562 : CycleSubmission.Artifact.artifact.instructionPC 2359 = 3063 := by
  rw [show (2359:Nat)=2135+(2359-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2563 : CycleSubmission.Artifact.artifact.instructionPC 2360 = 3064 := by
  rw [show (2360:Nat)=2135+(2360-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2564 : CycleSubmission.Artifact.artifact.instructionPC 0 = 0 := by
  rw [PCFast.instructionPC_eq_byteLength]; rfl

@[simp] theorem pcI2565 : CycleSubmission.Artifact.artifact.instructionPC 2361 = 3065 := by
  rw [show (2361:Nat)=2135+(2361-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2566 : CycleSubmission.Artifact.artifact.instructionPC 2362 = 3068 := by
  rw [show (2362:Nat)=2135+(2362-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2585 : CycleSubmission.Artifact.artifact.instructionPC 2379 = 3087 := by
  rw [show (2379:Nat)=2135+(2379-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2586 : CycleSubmission.Artifact.artifact.instructionPC 2380 = 3088 := by
  rw [show (2380:Nat)=2135+(2380-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2587 : CycleSubmission.Artifact.artifact.instructionPC 2381 = 3091 := by
  rw [show (2381:Nat)=2135+(2381-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2594 : CycleSubmission.Artifact.artifact.instructionPC 2390 = 3104 := by
  rw [show (2390:Nat)=2135+(2390-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2630 : CycleSubmission.Artifact.artifact.instructionPC 2424 = 3145 := by
  rw [show (2424:Nat)=2135+(2424-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2647 : CycleSubmission.Artifact.artifact.instructionPC 2440 = 3171 := by
  rw [show (2440:Nat)=2135+(2440-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2698 : CycleSubmission.Artifact.artifact.instructionPC 2446 = 3179 := by
  rw [show (2446:Nat)=2135+(2446-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

@[simp] theorem pcI2699 : CycleSubmission.Artifact.artifact.instructionPC 2447 = 3182 := by
  rw [show (2447:Nat)=2135+(2447-2135) from rfl, CycleSubmission.Global.PrefixPC.pc_add, shiftAnchor]
  rfl

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

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

Instruction indices 8575 .. 1652, one lemma each.
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
  let seg' := mkIdent (`CycleSubmission.Global.PrefixPC++seg.getId)
  let old' := mkIdent (`Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs++old.getId)
  `(tactic| (rw [$seg':ident $i (by decide) (by decide)]; exact $old':ident))
@[simp] theorem pc2545 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pc2546 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pc2547 : IPC 673 = 916 := by pc_by_len
@[simp] theorem pc2548 : IPC 674 = 917 := by pc_by_len
@[simp] theorem pc2556 : IPC 675 = 918 := by pc_by_len
@[simp] theorem pc2559 : IPC 676 = 920 := by pc_by_len
@[simp] theorem pc2560 : IPC 677 = 921 := by pc_by_len
@[simp] theorem pc2561 : IPC 678 = 922 := by pc_by_len
@[simp] theorem pc2563 : IPC 679 = 924 := by pc_by_len
@[simp] theorem pc2566 : IPC 680 = 927 := by pc_by_len
@[simp] theorem pc2567 : IPC 681 = 928 := by pc_by_len
@[simp] theorem pc2570 : IPC 681 = 928 := by pc_by_len
@[simp] theorem pc2574 : IPC 7913 = 10466 := by pc_by_len
@[simp] theorem pc2586 : IPC 7924 = 10485 := by pc_by_len
@[simp] theorem pc2591 : IPC 7930 = 10494 := by pc_by_len
@[simp] theorem pc2592 : IPC 7931 = 10495 := by pc_by_len
@[simp] theorem pc2600 : IPC 7959 = 10540 := by pc_by_len
@[simp] theorem pc2604 : IPC 7961 = 10542 := by pc_by_len
@[simp] theorem pc2618 : IPC 7965 = 10548 := by pc_by_len
@[simp] theorem pc2619 : IPC 7966 = 10549 := by pc_by_len
@[simp] theorem pc2620 : IPC 7967 = 10550 := by pc_by_len
@[simp] theorem pc2621 : IPC 7968 = 10551 := by pc_by_len
@[simp] theorem pc2622 : IPC 7969 = 10552 := by pc_by_len
@[simp] theorem pc2623 : IPC 7970 = 10553 := by pc_by_len
@[simp] theorem pc2624 : IPC 7971 = 10554 := by pc_by_len
@[simp] theorem pc2625 : IPC 7971 = 10554 := by pc_by_len
@[simp] theorem pc2628 : IPC 7972 = 10555 := by pc_by_len
@[simp] theorem pc2629 : IPC 7973 = 10556 := by pc_by_len
@[simp] theorem pc2631 : IPC 7974 = 10558 := by pc_by_len
@[simp] theorem pc2632 : IPC 7975 = 10559 := by pc_by_len
@[simp] theorem pc2633 : IPC 7976 = 10562 := by pc_by_len
@[simp] theorem pc2636 : IPC 7977 = 10563 := by pc_by_len
@[simp] theorem pc2637 : IPC 7978 = 10565 := by pc_by_len
@[simp] theorem pc2638 : IPC 7979 = 10566 := by pc_by_len
@[simp] theorem pc2639 : IPC 7980 = 10567 := by pc_by_len
@[simp] theorem pc2641 : IPC 7981 = 10570 := by pc_by_len
@[simp] theorem pc2642 : IPC 7982 = 10571 := by pc_by_len
@[simp] theorem pc2644 : IPC 7983 = 10572 := by pc_by_len
@[simp] theorem pc2645 : IPC 7984 = 10573 := by pc_by_len
@[simp] theorem pc2648 : IPC 7985 = 10576 := by pc_by_len
@[simp] theorem pc2649 : IPC 7986 = 10577 := by pc_by_len
@[simp] theorem pc2650 : IPC 7987 = 10578 := by pc_by_len
@[simp] theorem pc2651 : IPC 7988 = 10579 := by pc_by_len
@[simp] theorem pc2652 : IPC 7989 = 10580 := by pc_by_len
@[simp] theorem pc2653 : IPC 7990 = 10581 := by pc_by_len
@[simp] theorem pc2654 : IPC 7991 = 10582 := by pc_by_len
@[simp] theorem pc2657 : IPC 7992 = 10585 := by pc_by_len
@[simp] theorem pc2658 : IPC 7993 = 10586 := by pc_by_len
@[simp] theorem pc2659 : IPC 7994 = 10589 := by pc_by_len
@[simp] theorem pc2695 : IPC 8040 = 10643 := by pc_by_len
@[simp] theorem pc2696 : IPC 8041 = 10644 := by pc_by_len
@[simp] theorem pc2698 : IPC 8042 = 10645 := by pc_by_len
@[simp] theorem pc2699 : IPC 8043 = 10646 := by pc_by_len
@[simp] theorem pc2702 : IPC 8044 = 10649 := by pc_by_len
@[simp] theorem pc2703 : IPC 8045 = 10650 := by pc_by_len
@[simp] theorem pc2705 : IPC 8046 = 10651 := by pc_by_len
@[simp] theorem pc2706 : IPC 8047 = 10652 := by pc_by_len
@[simp] theorem pc2713 : IPC 8050 = 10657 := by pc_by_len
@[simp] theorem pc3009 : IPC 6494 = 8637 := by pc_by_len
@[simp] theorem pc3010 : IPC 6495 = 8638 := by pc_by_len
@[simp] theorem pc3011 : IPC 6496 = 8639 := by pc_by_len
@[simp] theorem pc3012 : IPC 6497 = 8640 := by pc_by_len
@[simp] theorem pc3013 : IPC 6498 = 8641 := by pc_by_len
@[simp] theorem pc2712 : IPC 8049 = 10656 := by pc_by_len
@[simp] theorem pc3125 : IPC 6590 = 8749 := by pc_by_len
@[simp] theorem pc3171 : IPC 6627 = 8792 := by pc_by_len
@[simp] theorem pc3174 : IPC 6628 = 8795 := by pc_by_len
@[simp] theorem pc3175 : IPC 6629 = 8796 := by pc_by_len
@[simp] theorem pc3176 : IPC 6630 = 8797 := by pc_by_len
@[simp] theorem pc3177 : IPC 6631 = 8798 := by pc_by_len
@[simp] theorem pc3178 : IPC 6631 = 8798 := by pc_by_len
@[simp] theorem pc3179 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3180 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3181 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3182 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3183 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3184 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3185 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3186 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3187 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3188 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3191 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pc3192 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcSaturate2992 : IPC 6575 = 8730 := by pc_by_len
@[simp] theorem pcSaturate2993 : IPC 6576 = 8731 := by pc_by_len
@[simp] theorem earlyExtraPC2883 : IPC 7439 = 9897 := by pc_by_len
@[simp] theorem earlyExtraPC2884 : IPC 7440 = 9898 := by pc_by_len
@[simp] theorem earlyExtraPC2885 : IPC 7441 = 9899 := by pc_by_len
@[simp] theorem earlyExtraPC2886 : IPC 7442 = 9900 := by pc_by_len
@[simp] theorem earlyExtraPC2888 : IPC 7443 = 9901 := by pc_by_len
@[simp] theorem earlyExtraPC2889 : IPC 7444 = 9902 := by pc_by_len
@[simp] theorem earlyExtraPC2890 : IPC 7445 = 9903 := by pc_by_len
@[simp] theorem earlyExtraPC2891 : IPC 7446 = 9906 := by pc_by_len
@[simp] theorem earlyExtraPC2892 : IPC 7447 = 9907 := by pc_by_len
@[simp] theorem earlyExtraPC2893 : IPC 7447 = 9907 := by pc_by_len
@[simp] theorem earlyExtraPC2894 : IPC 7447 = 9907 := by pc_by_len
@[simp] theorem earlyExtraPC2895 : IPC 8165 = 10834 := by pc_by_len
@[simp] theorem earlyExtraPC2896 : IPC 8177 = 10853 := by pc_by_len
@[simp] theorem earlyExtraPC2930 : IPC 8177 = 10853 := by pc_by_len
@[simp] theorem earlyExtraPC2931 : IPC 8177 = 10853 := by pc_by_len
@[simp] theorem earlyExtraPC2932 : IPC 8177 = 10853 := by pc_by_len
@[simp] theorem earlyExtraPC2933 : IPC 8196 = 10876 := by pc_by_len
@[simp] theorem earlyExtraPC2934 : IPC 4851 = 6622 := by pc_by_len
@[simp] theorem earlyExtraPC2935 : IPC 4852 = 6623 := by pc_by_len
@[simp] theorem earlyExtraPC2936 : IPC 4853 = 6626 := by pc_by_len
@[simp] theorem earlyExtraPC2937 : IPC 4854 = 6627 := by pc_by_len
@[simp] theorem earlyExtraPC2938 : IPC 4855 = 6629 := by pc_by_len
@[simp] theorem earlyExtraPC2939 : IPC 4856 = 6630 := by pc_by_len
@[simp] theorem earlyExtraPC2940 : IPC 4857 = 6631 := by pc_by_len
@[simp] theorem earlyExtraPC2941 : IPC 4858 = 6632 := by pc_by_len
@[simp] theorem earlyExtraPC2942 : IPC 4859 = 6633 := by pc_by_len
@[simp] theorem earlyExtraPC2943 : IPC 4860 = 6636 := by pc_by_len
@[simp] theorem pcC3009 : IPC 6631 = 8798 := by pc_by_len
@[simp] theorem pcC3010 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcC3011 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcC3019 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcC3020 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcC3021 : IPC 6632 = 8801 := by pc_by_len
/-! Program counters of the retained-T blocks the head-start table did not carry (generated from the artifact). -/
@[simp] theorem pcT2106 : IPC 7914 = 10467 := by pc_by_len
@[simp] theorem pcT2329 : IPC 6578 = 8733 := by pc_by_len
@[simp] theorem pcT2330 : IPC 6579 = 8734 := by pc_by_len
@[simp] theorem pcT2331 : IPC 6580 = 8735 := by pc_by_len
@[simp] theorem pcT2332 : IPC 6581 = 8736 := by pc_by_len
@[simp] theorem pcT2336 : IPC 6585 = 8742 := by pc_by_len
@[simp] theorem pcT2337 : IPC 6586 = 8743 := by pc_by_len
@[simp] theorem pcT2338 : IPC 6587 = 8744 := by pc_by_len
@[simp] theorem pcT2339 : IPC 6588 = 8745 := by pc_by_len
@[simp] theorem pcT2340 : IPC 6589 = 8748 := by pc_by_len
@[simp] theorem pcT2341 : IPC 6590 = 8749 := by pc_by_len
@[simp] theorem pcT2342 : IPC 6591 = 8750 := by pc_by_len
@[simp] theorem pcT2343 : IPC 6592 = 8751 := by pc_by_len
@[simp] theorem pcT2344 : IPC 6593 = 8752 := by pc_by_len
@[simp] theorem pcT2345 : IPC 6594 = 8753 := by pc_by_len
@[simp] theorem pcT2346 : IPC 6595 = 8754 := by pc_by_len
@[simp] theorem pcT2347 : IPC 6596 = 8755 := by pc_by_len
@[simp] theorem pcT2348 : IPC 6597 = 8756 := by pc_by_len
@[simp] theorem pcT2349 : IPC 6598 = 8759 := by pc_by_len
@[simp] theorem pcT2350 : IPC 6599 = 8760 := by pc_by_len
@[simp] theorem pcT2351 : IPC 6600 = 8761 := by pc_by_len
@[simp] theorem pcT2352 : IPC 6601 = 8762 := by pc_by_len
@[simp] theorem pcT2353 : IPC 6602 = 8763 := by pc_by_len
@[simp] theorem pcT2354 : IPC 6603 = 8764 := by pc_by_len
@[simp] theorem pcT2355 : IPC 6604 = 8765 := by pc_by_len
@[simp] theorem pcT2356 : IPC 6605 = 8766 := by pc_by_len
@[simp] theorem pcT2357 : IPC 6606 = 8767 := by pc_by_len
@[simp] theorem pcT2358 : IPC 6607 = 8768 := by pc_by_len
@[simp] theorem pcT2359 : IPC 6608 = 8769 := by pc_by_len
@[simp] theorem pcT2360 : IPC 6609 = 8770 := by pc_by_len
@[simp] theorem pcT2361 : IPC 6610 = 8771 := by pc_by_len
@[simp] theorem pcT2362 : IPC 6611 = 8772 := by pc_by_len
@[simp] theorem pcT2363 : IPC 6612 = 8773 := by pc_by_len
@[simp] theorem pcT2364 : IPC 6613 = 8774 := by pc_by_len
@[simp] theorem pcT2365 : IPC 6614 = 8777 := by pc_by_len
@[simp] theorem pcT2366 : IPC 6615 = 8778 := by pc_by_len
@[simp] theorem pcT2367 : IPC 6616 = 8779 := by pc_by_len
@[simp] theorem pcT2368 : IPC 6617 = 8780 := by pc_by_len
@[simp] theorem pcT2369 : IPC 6618 = 8781 := by pc_by_len
@[simp] theorem pcT2370 : IPC 6619 = 8784 := by pc_by_len
@[simp] theorem pcT2371 : IPC 6620 = 8785 := by pc_by_len
@[simp] theorem pcT2372 : IPC 6621 = 8786 := by pc_by_len
@[simp] theorem pcT2522 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcI2013 : IPC 4864 = 6642 := by pc_by_len
@[simp] theorem pcI2014 : IPC 4865 = 6643 := by pc_by_len
@[simp] theorem pcI2015 : IPC 4864 = 6642 := by pc_by_len
@[simp] theorem pcI2016 : IPC 4867 = 6646 := by pc_by_len
@[simp] theorem pcI2017 : IPC 4868 = 6647 := by pc_by_len
@[simp] theorem pcI2018 : IPC 4864 = 6642 := by pc_by_len
@[simp] theorem pcI2032 : IPC 7908 = 10459 := by pc_by_len
@[simp] theorem pcI2033 : IPC 7910 = 10461 := by pc_by_len
@[simp] theorem pcI2034 : IPC 7911 = 10462 := by pc_by_len
@[simp] theorem pcI2035 : IPC 7912 = 10465 := by pc_by_len
@[simp] theorem pcI2039 : IPC 4864 = 6642 := by pc_by_len
@[simp] theorem pcI2040 : IPC 4864 = 6642 := by pc_by_len
@[simp] theorem pcI2042 : IPC 6325 = 8404 := by pc_by_len
@[simp] theorem pcI2043 : IPC 6328 = 8408 := by pc_by_len
@[simp] theorem pcI2044 : IPC 6332 = 8413 := by pc_by_len
@[simp] theorem pcI2045 : IPC 6333 = 8416 := by pc_by_len
@[simp] theorem pcI2046 : IPC 6334 = 8417 := by pc_by_len
@[simp] theorem pcI2047 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2048 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2049 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2050 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2051 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2052 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2053 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2054 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2055 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2056 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2057 : IPC 672 = 915 := by pc_by_len
@[simp] theorem pcI2093 : IPC 7915 = 10468 := by pc_by_len
@[simp] theorem pcI2094 : IPC 7916 = 10471 := by pc_by_len
@[simp] theorem pcI2095 : IPC 7917 = 10474 := by pc_by_len
@[simp] theorem pcI2156 : IPC 7995 = 10590 := by pc_by_len
@[simp] theorem pcI2200 : IPC 8050 = 10657 := by pc_by_len
@[simp] theorem pcI2201 : IPC 8053 = 10663 := by pc_by_len
@[simp] theorem pcI2202 : IPC 8064 = 10681 := by pc_by_len
@[simp] theorem pcI2203 : IPC 8064 = 10681 := by pc_by_len
@[simp] theorem pcI2204 : IPC 8065 = 10682 := by pc_by_len
@[simp] theorem pcI2205 : IPC 8067 = 10684 := by pc_by_len
@[simp] theorem pcI2206 : IPC 8067 = 10684 := by pc_by_len
@[simp] theorem pcI2207 : IPC 8069 = 10687 := by pc_by_len
@[simp] theorem pcI2208 : IPC 8070 = 10689 := by pc_by_len
@[simp] theorem pcI2209 : IPC 8072 = 10693 := by pc_by_len
@[simp] theorem pcI2210 : IPC 8072 = 10693 := by pc_by_len
@[simp] theorem pcI2211 : IPC 8074 = 10697 := by pc_by_len
@[simp] theorem pcI2212 : IPC 8074 = 10697 := by pc_by_len
@[simp] theorem pcI2213 : IPC 8076 = 10701 := by pc_by_len
@[simp] theorem pcI2214 : IPC 8076 = 10701 := by pc_by_len
@[simp] theorem pcI2215 : IPC 8078 = 10705 := by pc_by_len
@[simp] theorem pcI2216 : IPC 8078 = 10705 := by pc_by_len
@[simp] theorem pcI2217 : IPC 8080 = 10709 := by pc_by_len
@[simp] theorem pcI2218 : IPC 8080 = 10709 := by pc_by_len
@[simp] theorem pcI2219 : IPC 8082 = 10713 := by pc_by_len
@[simp] theorem pcI2220 : IPC 8082 = 10713 := by pc_by_len
@[simp] theorem pcI2221 : IPC 8084 = 10717 := by pc_by_len
@[simp] theorem pcI2222 : IPC 8084 = 10717 := by pc_by_len
@[simp] theorem pcI2223 : IPC 8086 = 10721 := by pc_by_len
@[simp] theorem pcI2224 : IPC 8086 = 10721 := by pc_by_len
@[simp] theorem pcI2225 : IPC 8088 = 10725 := by pc_by_len
@[simp] theorem pcI2226 : IPC 8088 = 10725 := by pc_by_len
@[simp] theorem pcI2330 : IPC 0 = 0 := by pc_by_len
@[simp] theorem pcI2332 : IPC 6413 = 8546 := by pc_by_len
@[simp] theorem pcI2333 : IPC 6414 = 8547 := by pc_by_len
@[simp] theorem pcI2334 : IPC 6415 = 8548 := by pc_by_len
@[simp] theorem pcI2335 : IPC 6416 = 8549 := by pc_by_len
@[simp] theorem pcI2336 : IPC 6417 = 8550 := by pc_by_len
@[simp] theorem pcI2337 : IPC 6418 = 8551 := by pc_by_len
@[simp] theorem pcI2338 : IPC 6419 = 8552 := by pc_by_len
@[simp] theorem pcI2339 : IPC 6420 = 8553 := by pc_by_len
@[simp] theorem pcI2340 : IPC 6421 = 8554 := by pc_by_len
@[simp] theorem pcI2341 : IPC 6422 = 8557 := by pc_by_len
@[simp] theorem pcI2342 : IPC 6423 = 8558 := by pc_by_len
@[simp] theorem pcI2343 : IPC 6424 = 8559 := by pc_by_len
@[simp] theorem pcI2344 : IPC 6425 = 8560 := by pc_by_len
@[simp] theorem pcI2345 : IPC 6426 = 8561 := by pc_by_len
@[simp] theorem pcI2346 : IPC 6427 = 8562 := by pc_by_len
@[simp] theorem pcI2347 : IPC 6428 = 8563 := by pc_by_len
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
@[simp] theorem pcI2360 : IPC 6429 = 8564 := by pc_by_len
@[simp] theorem pcI2361 : IPC 6430 = 8565 := by pc_by_len
@[simp] theorem pcI2362 : IPC 6431 = 8566 := by pc_by_len
@[simp] theorem pcI2363 : IPC 6432 = 8567 := by pc_by_len
@[simp] theorem pcI2364 : IPC 6433 = 8568 := by pc_by_len
@[simp] theorem pcI2365 : IPC 6434 = 8569 := by pc_by_len
@[simp] theorem pcI2366 : IPC 6435 = 8570 := by pc_by_len
@[simp] theorem pcI2367 : IPC 6436 = 8571 := by pc_by_len
@[simp] theorem pcI2368 : IPC 6437 = 8572 := by pc_by_len
@[simp] theorem pcI2369 : IPC 6438 = 8573 := by pc_by_len
@[simp] theorem pcI2370 : IPC 6439 = 8574 := by pc_by_len
@[simp] theorem pcI2371 : IPC 6440 = 8575 := by pc_by_len
@[simp] theorem pcI2372 : IPC 6441 = 8576 := by pc_by_len
@[simp] theorem pcI2373 : IPC 6442 = 8577 := by pc_by_len
@[simp] theorem pcI2374 : IPC 6443 = 8578 := by pc_by_len
@[simp] theorem pcI2375 : IPC 6444 = 8581 := by pc_by_len
@[simp] theorem pcI2376 : IPC 6445 = 8582 := by pc_by_len
@[simp] theorem pcI2377 : IPC 6446 = 8583 := by pc_by_len
@[simp] theorem pcI2378 : IPC 6447 = 8584 := by pc_by_len
@[simp] theorem pcI2379 : IPC 6448 = 8585 := by pc_by_len
@[simp] theorem pcI2380 : IPC 6449 = 8588 := by pc_by_len
@[simp] theorem pcI2381 : IPC 6450 = 8589 := by pc_by_len
@[simp] theorem pcI2382 : IPC 6451 = 8590 := by pc_by_len
@[simp] theorem pcI2383 : IPC 6452 = 8591 := by pc_by_len
@[simp] theorem pcI2384 : IPC 6453 = 8592 := by pc_by_len
@[simp] theorem pcI2385 : IPC 6454 = 8593 := by pc_by_len
@[simp] theorem pcI2386 : IPC 6455 = 8594 := by pc_by_len
@[simp] theorem pcI2387 : IPC 6456 = 8595 := by pc_by_len
@[simp] theorem pcI2388 : IPC 0 = 0 := by pc_by_len
@[simp] theorem pcI2389 : IPC 6457 = 8596 := by pc_by_len
@[simp] theorem pcI2390 : IPC 6458 = 8597 := by pc_by_len
@[simp] theorem pcI2391 : IPC 6459 = 8598 := by pc_by_len
@[simp] theorem pcI2392 : IPC 6460 = 8599 := by pc_by_len
@[simp] theorem pcI2393 : IPC 6461 = 8600 := by pc_by_len
@[simp] theorem pcI2394 : IPC 6462 = 8601 := by pc_by_len
@[simp] theorem pcI2395 : IPC 6463 = 8602 := by pc_by_len
@[simp] theorem pcI2396 : IPC 6464 = 8603 := by pc_by_len
@[simp] theorem pcI2397 : IPC 6465 = 8604 := by pc_by_len
@[simp] theorem pcI2398 : IPC 6466 = 8605 := by pc_by_len
@[simp] theorem pcI2399 : IPC 6467 = 8606 := by pc_by_len
@[simp] theorem pcI2400 : IPC 6468 = 8607 := by pc_by_len
@[simp] theorem pcI2401 : IPC 6469 = 8608 := by pc_by_len
@[simp] theorem pcI2402 : IPC 6470 = 8609 := by pc_by_len
@[simp] theorem pcI2403 : IPC 6471 = 8610 := by pc_by_len
@[simp] theorem pcI2404 : IPC 6472 = 8613 := by pc_by_len
@[simp] theorem pcI2405 : IPC 6473 = 8614 := by pc_by_len
@[simp] theorem pcI2406 : IPC 6474 = 8615 := by pc_by_len
@[simp] theorem pcI2407 : IPC 6475 = 8616 := by pc_by_len
@[simp] theorem pcI2408 : IPC 6476 = 8617 := by pc_by_len
@[simp] theorem pcI2409 : IPC 6477 = 8620 := by pc_by_len
@[simp] theorem pcI2410 : IPC 6478 = 8621 := by pc_by_len
@[simp] theorem pcI2411 : IPC 6479 = 8622 := by pc_by_len
@[simp] theorem pcI2412 : IPC 6480 = 8623 := by pc_by_len
@[simp] theorem pcI2413 : IPC 6481 = 8624 := by pc_by_len
@[simp] theorem pcI2414 : IPC 6482 = 8625 := by pc_by_len
@[simp] theorem pcI2415 : IPC 6483 = 8626 := by pc_by_len
@[simp] theorem pcI2416 : IPC 6484 = 8627 := by pc_by_len
@[simp] theorem pcI2417 : IPC 0 = 0 := by pc_by_len
@[simp] theorem pcI2418 : IPC 6485 = 8628 := by pc_by_len
@[simp] theorem pcI2419 : IPC 6486 = 8629 := by pc_by_len
@[simp] theorem pcI2420 : IPC 6487 = 8630 := by pc_by_len
@[simp] theorem pcI2421 : IPC 6488 = 8631 := by pc_by_len
@[simp] theorem pcI2422 : IPC 6489 = 8632 := by pc_by_len
@[simp] theorem pcI2423 : IPC 6490 = 8633 := by pc_by_len
@[simp] theorem pcI2424 : IPC 6491 = 8634 := by pc_by_len
@[simp] theorem pcI2425 : IPC 6492 = 8635 := by pc_by_len
@[simp] theorem pcI2426 : IPC 6493 = 8636 := by pc_by_len
@[simp] theorem pcI2432 : IPC 6499 = 8642 := by pc_by_len
@[simp] theorem pcI2433 : IPC 6500 = 8645 := by pc_by_len
@[simp] theorem pcI2434 : IPC 6501 = 8646 := by pc_by_len
@[simp] theorem pcI2435 : IPC 6502 = 8647 := by pc_by_len
@[simp] theorem pcI2436 : IPC 6503 = 8648 := by pc_by_len
@[simp] theorem pcI2437 : IPC 6504 = 8649 := by pc_by_len
@[simp] theorem pcI2438 : IPC 6505 = 8652 := by pc_by_len
@[simp] theorem pcI2439 : IPC 6506 = 8653 := by pc_by_len
@[simp] theorem pcI2440 : IPC 6507 = 8654 := by pc_by_len
@[simp] theorem pcI2441 : IPC 6508 = 8655 := by pc_by_len
@[simp] theorem pcI2442 : IPC 6509 = 8656 := by pc_by_len
@[simp] theorem pcI2443 : IPC 6510 = 8657 := by pc_by_len
@[simp] theorem pcI2444 : IPC 6511 = 8658 := by pc_by_len
@[simp] theorem pcI2445 : IPC 6512 = 8659 := by pc_by_len
@[simp] theorem pcI2446 : IPC 6513 = 8660 := by pc_by_len
@[simp] theorem pcI2447 : IPC 0 = 0 := by pc_by_len
@[simp] theorem pcI2448 : IPC 6514 = 8661 := by pc_by_len
@[simp] theorem pcI2449 : IPC 6515 = 8662 := by pc_by_len
@[simp] theorem pcI2450 : IPC 6516 = 8663 := by pc_by_len
@[simp] theorem pcI2451 : IPC 6517 = 8664 := by pc_by_len
@[simp] theorem pcI2452 : IPC 6518 = 8665 := by pc_by_len
@[simp] theorem pcI2453 : IPC 6519 = 8666 := by pc_by_len
@[simp] theorem pcI2454 : IPC 6520 = 8667 := by pc_by_len
@[simp] theorem pcI2455 : IPC 6521 = 8668 := by pc_by_len
@[simp] theorem pcI2456 : IPC 6522 = 8669 := by pc_by_len
@[simp] theorem pcI2457 : IPC 6523 = 8670 := by pc_by_len
@[simp] theorem pcI2458 : IPC 6524 = 8671 := by pc_by_len
@[simp] theorem pcI2459 : IPC 6525 = 8672 := by pc_by_len
@[simp] theorem pcI2460 : IPC 6526 = 8673 := by pc_by_len
@[simp] theorem pcI2461 : IPC 6527 = 8674 := by pc_by_len
@[simp] theorem pcI2462 : IPC 6528 = 8677 := by pc_by_len
@[simp] theorem pcI2463 : IPC 6529 = 8678 := by pc_by_len
@[simp] theorem pcI2464 : IPC 6530 = 8679 := by pc_by_len
@[simp] theorem pcI2465 : IPC 6531 = 8680 := by pc_by_len
@[simp] theorem pcI2466 : IPC 6532 = 8681 := by pc_by_len
@[simp] theorem pcI2467 : IPC 6533 = 8684 := by pc_by_len
@[simp] theorem pcI2468 : IPC 6534 = 8685 := by pc_by_len
@[simp] theorem pcI2469 : IPC 6535 = 8686 := by pc_by_len
@[simp] theorem pcI2470 : IPC 6536 = 8687 := by pc_by_len
@[simp] theorem pcI2471 : IPC 6537 = 8688 := by pc_by_len
@[simp] theorem pcI2472 : IPC 6538 = 8689 := by pc_by_len
@[simp] theorem pcI2473 : IPC 6539 = 8690 := by pc_by_len
@[simp] theorem pcI2474 : IPC 6540 = 8691 := by pc_by_len
@[simp] theorem pcI2475 : IPC 6541 = 8692 := by pc_by_len
@[simp] theorem pcI2476 : IPC 0 = 0 := by pc_by_len
@[simp] theorem pcI2477 : IPC 6542 = 8693 := by pc_by_len
@[simp] theorem pcI2478 : IPC 6543 = 8694 := by pc_by_len
@[simp] theorem pcI2479 : IPC 6544 = 8695 := by pc_by_len
@[simp] theorem pcI2480 : IPC 6545 = 8696 := by pc_by_len
@[simp] theorem pcI2481 : IPC 6546 = 8697 := by pc_by_len
@[simp] theorem pcI2482 : IPC 6547 = 8698 := by pc_by_len
@[simp] theorem pcI2483 : IPC 6548 = 8699 := by pc_by_len
@[simp] theorem pcI2484 : IPC 6549 = 8700 := by pc_by_len
@[simp] theorem pcI2485 : IPC 6550 = 8701 := by pc_by_len
@[simp] theorem pcI2486 : IPC 6551 = 8702 := by pc_by_len
@[simp] theorem pcI2487 : IPC 6552 = 8703 := by pc_by_len
@[simp] theorem pcI2488 : IPC 6553 = 8704 := by pc_by_len
@[simp] theorem pcI2489 : IPC 6554 = 8705 := by pc_by_len
@[simp] theorem pcI2490 : IPC 6555 = 8706 := by pc_by_len
@[simp] theorem pcI2492 : IPC 6556 = 8709 := by pc_by_len
@[simp] theorem pcI2493 : IPC 6557 = 8710 := by pc_by_len
@[simp] theorem pcI2494 : IPC 6558 = 8711 := by pc_by_len
@[simp] theorem pcI2495 : IPC 6559 = 8712 := by pc_by_len
@[simp] theorem pcI2496 : IPC 6560 = 8713 := by pc_by_len
@[simp] theorem pcI2497 : IPC 6561 = 8716 := by pc_by_len
@[simp] theorem pcI2498 : IPC 6562 = 8717 := by pc_by_len
@[simp] theorem pcI2499 : IPC 6563 = 8718 := by pc_by_len
@[simp] theorem pcI2500 : IPC 6564 = 8719 := by pc_by_len
@[simp] theorem pcI2501 : IPC 6565 = 8720 := by pc_by_len
@[simp] theorem pcI2502 : IPC 6566 = 8721 := by pc_by_len
@[simp] theorem pcI2503 : IPC 6567 = 8722 := by pc_by_len
@[simp] theorem pcI2504 : IPC 6568 = 8723 := by pc_by_len
@[simp] theorem pcI2505 : IPC 0 = 0 := by pc_by_len
@[simp] theorem pcI2506 : IPC 6569 = 8724 := by pc_by_len
@[simp] theorem pcI2507 : IPC 6570 = 8725 := by pc_by_len
@[simp] theorem pcI2508 : IPC 6571 = 8726 := by pc_by_len
@[simp] theorem pcI2509 : IPC 6572 = 8727 := by pc_by_len
@[simp] theorem pcI2510 : IPC 6573 = 8728 := by pc_by_len
@[simp] theorem pcI2511 : IPC 6574 = 8729 := by pc_by_len
@[simp] theorem pcI2514 : IPC 6577 = 8732 := by pc_by_len
@[simp] theorem pcI2519 : IPC 6582 = 8737 := by pc_by_len
@[simp] theorem pcI2520 : IPC 6583 = 8738 := by pc_by_len
@[simp] theorem pcI2521 : IPC 6584 = 8741 := by pc_by_len
@[simp] theorem pcI2559 : IPC 6622 = 8787 := by pc_by_len
@[simp] theorem pcI2560 : IPC 6623 = 8788 := by pc_by_len
@[simp] theorem pcI2561 : IPC 6624 = 8789 := by pc_by_len
@[simp] theorem pcI2562 : IPC 6625 = 8790 := by pc_by_len
@[simp] theorem pcI2563 : IPC 6626 = 8791 := by pc_by_len
@[simp] theorem pcI2564 : IPC 0 = 0 := by pc_by_len
@[simp] theorem pcI2565 : IPC 6627 = 8792 := by pc_by_len
@[simp] theorem pcI2566 : IPC 6628 = 8795 := by pc_by_len
@[simp] theorem pcI2585 : IPC 6632 = 8801 := by pc_by_len
/-! ## The straight-line negation and the inline Newton chain (negun, inl693) -/
@[simp] theorem negunPC0 (i : Nat) (hi : 4864 ≤ i) (hii : i ≤ 4872) :
    cachedArtifact.instructionPC i =
      ([6642,6643,6645,6646,6647,6648,6651,6652,6655] : List Nat)[i - 4864]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem negunPC1 (i : Nat) (hi : 7918 ≤ i) (hii : i ≤ 7964) :
    cachedArtifact.instructionPC i =
      ([10475,10476,10478,10479,10482,10483,10485,10486,10487,10488,10491,10492,10494,10495,10496,10499,10500,10502,10503,10504,10507,10508,10510,10511,10512,10515,10516,10518,10519,10520,10523,10524,10525,10527,10528,10529,10532,10533,10535,10536,10537,10540,10541,10542,10543,10544,10545] : List Nat)[i - 7918]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem negunPC2 (i : Nat) (hi : 7996 ≤ i) (hii : i ≤ 8039) :
    cachedArtifact.instructionPC i =
      ([10591,10592,10593,10594,10595,10597,10598,10600,10601,10602,10603,10604,10606,10607,10608,10609,10610,10611,10613,10614,10615,10616,10617,10618,10620,10621,10622,10623,10624,10625,10627,10628,10629,10630,10631,10632,10634,10635,10636,10637,10638,10639,10641,10642] : List Nat)[i - 7996]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
/-! ## Directly stated pcs: E5 and the eight-limb loop head (7809 .. 7899), the bottom test,
the exit / E3 phase blocks and the repair loop (8134 .. 8218), and the appended four-limb
loop head (6559 .. 8608). -/
@[simp] theorem pcDual2056 : IPC 8090 = 10729 := by pc_by_len
@[simp] theorem pcDual2057 : IPC 8065 = 10682 := by pc_by_len
@[simp] theorem pcDual2065 : IPC 8065 = 10682 := by pc_by_len
@[simp] theorem pcDual2066 : IPC 8065 = 10682 := by pc_by_len
@[simp] theorem pcDual2067 : IPC 8065 = 10682 := by pc_by_len
@[simp] theorem pcDual2068 : IPC 8090 = 10729 := by pc_by_len
@[simp] theorem pcDual2069 : IPC 8053 = 10663 := by pc_by_len
@[simp] theorem pcDual2070 : IPC 8057 = 10671 := by pc_by_len
@[simp] theorem pcDual2071 : IPC 8057 = 10671 := by pc_by_len
@[simp] theorem pcDual2072 : IPC 8059 = 10673 := by pc_by_len
@[simp] theorem pcDual2073 : IPC 8060 = 10674 := by pc_by_len
@[simp] theorem pcDual2074 : IPC 8061 = 10675 := by pc_by_len
@[simp] theorem pcDual2075 : IPC 8062 = 10677 := by pc_by_len
@[simp] theorem pcDual2076 : IPC 8062 = 10677 := by pc_by_len
@[simp] theorem pcDual2077 : IPC 8063 = 10678 := by pc_by_len
@[simp] theorem pcDual2078 : IPC 8064 = 10681 := by pc_by_len
@[simp] theorem pcDual2079 : IPC 8090 = 10729 := by pc_by_len
@[simp] theorem pcDual2080 : IPC 8090 = 10729 := by pc_by_len
@[simp] theorem pcDual2081 : IPC 8092 = 10733 := by pc_by_len
@[simp] theorem pcDual2082 : IPC 8093 = 10734 := by pc_by_len
@[simp] theorem pcDual2083 : IPC 8094 = 10735 := by pc_by_len
@[simp] theorem pcDual2084 : IPC 8094 = 10735 := by pc_by_len
@[simp] theorem pcDual2085 : IPC 8094 = 10735 := by pc_by_len
@[simp] theorem pcDual2086 : IPC 8094 = 10735 := by pc_by_len
@[simp] theorem pcDual2087 : IPC 8096 = 10739 := by pc_by_len
@[simp] theorem pcDual2088 : IPC 6360 = 8448 := by pc_by_len
@[simp] theorem pcDual2089 : IPC 6360 = 8448 := by pc_by_len
@[simp] theorem pcDual2090 : IPC 6360 = 8448 := by pc_by_len
@[simp] theorem pcDual2091 : IPC 6360 = 8448 := by pc_by_len
@[simp] theorem pcDual2092 : IPC 6361 = 8449 := by pc_by_len
@[simp] theorem pcDual2093 : IPC 6362 = 8450 := by pc_by_len
@[simp] theorem pcDual2094 : IPC 6363 = 8453 := by pc_by_len
@[simp] theorem pcDual2095 : IPC 6364 = 8456 := by pc_by_len
@[simp] theorem pcDual2096 : IPC 6365 = 8457 := by pc_by_len
@[simp] theorem pcDual2100 : IPC 6366 = 8460 := by pc_by_len
@[simp] theorem pcDual2101 : IPC 6367 = 8461 := by pc_by_len
@[simp] theorem pcDual2102 : IPC 6368 = 8462 := by pc_by_len
@[simp] theorem pcDual2103 : IPC 6369 = 8463 := by pc_by_len
@[simp] theorem pcDual2104 : IPC 6370 = 8464 := by pc_by_len
@[simp] theorem pcDual2105 : IPC 6371 = 8465 := by pc_by_len
@[simp] theorem pcDual2106 : IPC 6372 = 8468 := by pc_by_len
@[simp] theorem pcDual2107 : IPC 6373 = 8469 := by pc_by_len
@[simp] theorem pcDual2108 : IPC 6374 = 8470 := by pc_by_len
@[simp] theorem pcDual2109 : IPC 6375 = 8473 := by pc_by_len
@[simp] theorem pcDual2110 : IPC 6376 = 8474 := by pc_by_len
@[simp] theorem pcDual2111 : IPC 6377 = 8475 := by pc_by_len
@[simp] theorem pcDual2112 : IPC 6378 = 8476 := by pc_by_len
@[simp] theorem pcDual2113 : IPC 6379 = 8477 := by pc_by_len
@[simp] theorem pcDual2114 : IPC 6380 = 8478 := by pc_by_len
@[simp] theorem pcDual2115 : IPC 6381 = 8479 := by pc_by_len
@[simp] theorem pcDual2116 : IPC 6382 = 8480 := by pc_by_len
@[simp] theorem pcDual2117 : IPC 6383 = 8481 := by pc_by_len
@[simp] theorem pcDual2118 : IPC 6384 = 8482 := by pc_by_len
@[simp] theorem pcDual2119 : IPC 6385 = 8483 := by pc_by_len
@[simp] theorem pcDual2120 : IPC 6386 = 8484 := by pc_by_len
@[simp] theorem pcDual2121 : IPC 6387 = 8485 := by pc_by_len
@[simp] theorem pcDual2122 : IPC 6388 = 8486 := by pc_by_len
@[simp] theorem pcDual2123 : IPC 6389 = 8487 := by pc_by_len
@[simp] theorem pcDual2124 : IPC 6390 = 8488 := by pc_by_len
@[simp] theorem pcDual2125 : IPC 6391 = 8489 := by pc_by_len
@[simp] theorem pcDual2126 : IPC 6392 = 8490 := by pc_by_len
@[simp] theorem pcDual2127 : IPC 6393 = 8492 := by pc_by_len
@[simp] theorem pcDual2128 : IPC 6394 = 8493 := by pc_by_len
@[simp] theorem pcDual2129 : IPC 6395 = 8494 := by pc_by_len
@[simp] theorem pcDual2130 : IPC 6396 = 8495 := by pc_by_len
@[simp] theorem pcDual2131 : IPC 6397 = 8496 := by pc_by_len
@[simp] theorem pcDual2132 : IPC 6398 = 8497 := by pc_by_len
@[simp] theorem pcDual2133 : IPC 6399 = 8498 := by pc_by_len
@[simp] theorem pcDual2134 : IPC 6400 = 8501 := by pc_by_len
@[simp] theorem pcDual2135 : IPC 6401 = 8502 := by pc_by_len
@[simp] theorem pcDual2136 : IPC 6402 = 8503 := by pc_by_len
@[simp] theorem pcDual2137 : IPC 6403 = 8504 := by pc_by_len
@[simp] theorem pcDual2138 : IPC 6404 = 8505 := by pc_by_len
@[simp] theorem pcDual2139 : IPC 6406 = 8507 := by pc_by_len
@[simp] theorem pcDual2141 : IPC 6407 = 8540 := by pc_by_len
@[simp] theorem pcDual2142 : IPC 6408 = 8541 := by pc_by_len
@[simp] theorem pcDual2143 : IPC 6409 = 8542 := by pc_by_len
@[simp] theorem pcDual2144 : IPC 6410 = 8543 := by pc_by_len
@[simp] theorem pcDual2145 : IPC 6411 = 8544 := by pc_by_len
@[simp] theorem pcDual2146 : IPC 6412 = 8545 := by pc_by_len
@[simp] theorem pcDual2381 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcDual2382 : IPC 6632 = 8801 := by pc_by_len
@[simp] theorem pcDual2383 : IPC 6633 = 8802 := by pc_by_len
@[simp] theorem pcDual2384 : IPC 6634 = 8803 := by pc_by_len
@[simp] theorem pcDual2385 : IPC 6634 = 8803 := by pc_by_len
@[simp] theorem pcDual2386 : IPC 6635 = 8804 := by pc_by_len
@[simp] theorem pcDual2387 : IPC 6636 = 8805 := by pc_by_len
@[simp] theorem pcDual2388 : IPC 6637 = 8806 := by pc_by_len
@[simp] theorem pcDual2389 : IPC 6637 = 8806 := by pc_by_len
@[simp] theorem pcDual2390 : IPC 6637 = 8806 := by pc_by_len
@[simp] theorem pcDual2391 : IPC 6638 = 8807 := by pc_by_len
@[simp] theorem pcDual2392 : IPC 6638 = 8807 := by pc_by_len
@[simp] theorem pcDual2393 : IPC 6638 = 8807 := by pc_by_len
@[simp] theorem pcDual2394 : IPC 6638 = 8807 := by pc_by_len
@[simp] theorem pcDual2395 : IPC 863 = 1223 := by pc_by_len
@[simp] theorem pcDual2396 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2397 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2398 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2399 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2400 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2401 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2402 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2403 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2404 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2405 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2406 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2407 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2408 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2409 : IPC 555 = 761 := by pc_by_len
@[simp] theorem pcDual2410 : IPC 863 = 1223 := by pc_by_len
@[simp] theorem pcDual2411 : IPC 866 = 1228 := by pc_by_len
@[simp] theorem pcDual2412 : IPC 866 = 1228 := by pc_by_len
@[simp] theorem pcDual2413 : IPC 867 = 1229 := by pc_by_len
@[simp] theorem pcDual2414 : IPC 868 = 1230 := by pc_by_len
@[simp] theorem pcDual2415 : IPC 869 = 1233 := by pc_by_len
@[simp] theorem pcDual2416 : IPC 870 = 1234 := by pc_by_len
@[simp] theorem pcDual2417 : IPC 871 = 1235 := by pc_by_len
@[simp] theorem pcDual2418 : IPC 872 = 1236 := by pc_by_len
@[simp] theorem pcDual2419 : IPC 873 = 1237 := by pc_by_len
@[simp] theorem pcDual2420 : IPC 874 = 1240 := by pc_by_len
@[simp] theorem pcDual2421 : IPC 875 = 1241 := by pc_by_len
@[simp] theorem pcDual2422 : IPC 876 = 1242 := by pc_by_len
@[simp] theorem pcDual2423 : IPC 877 = 1243 := by pc_by_len
@[simp] theorem pcDual2424 : IPC 878 = 1244 := by pc_by_len
@[simp] theorem pcDual2425 : IPC 879 = 1245 := by pc_by_len
@[simp] theorem pcDual2426 : IPC 880 = 1246 := by pc_by_len
@[simp] theorem pcDual2427 : IPC 881 = 1247 := by pc_by_len
@[simp] theorem pcDual2428 : IPC 882 = 1248 := by pc_by_len
@[simp] theorem pcDual2429 : IPC 883 = 1249 := by pc_by_len
@[simp] theorem pcDual2430 : IPC 884 = 1250 := by pc_by_len
@[simp] theorem pcDual2431 : IPC 885 = 1251 := by pc_by_len
@[simp] theorem pcDual2432 : IPC 886 = 1252 := by pc_by_len
@[simp] theorem pcDual2433 : IPC 887 = 1253 := by pc_by_len
@[simp] theorem pcDual2434 : IPC 888 = 1254 := by pc_by_len
@[simp] theorem pcDual2435 : IPC 889 = 1255 := by pc_by_len
@[simp] theorem pcDual2436 : IPC 890 = 1256 := by pc_by_len
@[simp] theorem pcDual2437 : IPC 891 = 1257 := by pc_by_len
@[simp] theorem pcDual2438 : IPC 892 = 1258 := by pc_by_len
@[simp] theorem pcDual2439 : IPC 893 = 1260 := by pc_by_len
@[simp] theorem pcDual2440 : IPC 894 = 1261 := by pc_by_len
@[simp] theorem pcDual2441 : IPC 895 = 1262 := by pc_by_len
@[simp] theorem pcDual2442 : IPC 896 = 1265 := by pc_by_len
@[simp] theorem pcDual2443 : IPC 897 = 1266 := by pc_by_len
@[simp] theorem pcDual2444 : IPC 898 = 1267 := by pc_by_len
@[simp] theorem pcDual2445 : IPC 899 = 1270 := by pc_by_len
@[simp] theorem pcDual2446 : IPC 900 = 1271 := by pc_by_len
@[simp] theorem pcDual2447 : IPC 901 = 1272 := by pc_by_len
@[simp] theorem pcDual2448 : IPC 902 = 1275 := by pc_by_len
@[simp] theorem pcDual2449 : IPC 903 = 1276 := by pc_by_len
@[simp] theorem pcDual2450 : IPC 904 = 1277 := by pc_by_len
@[simp] theorem pcDual2451 : IPC 905 = 1278 := by pc_by_len
@[simp] theorem pcDual2452 : IPC 906 = 1279 := by pc_by_len
@[simp] theorem pcDual2453 : IPC 907 = 1282 := by pc_by_len
@[simp] theorem pcDual2454 : IPC 908 = 1283 := by pc_by_len
@[simp] theorem pcDual2455 : IPC 909 = 1284 := by pc_by_len
@[simp] theorem pcDual2456 : IPC 910 = 1285 := by pc_by_len
@[simp] theorem pcDual2457 : IPC 911 = 1288 := by pc_by_len
@[simp] theorem pcDual2458 : IPC 912 = 1289 := by pc_by_len
@[simp] theorem pcDual2459 : IPC 913 = 1292 := by pc_by_len
@[simp] theorem pcDual2460 : IPC 919 = 1298 := by pc_by_len
@[simp] theorem pcDual2461 : IPC 920 = 1301 := by pc_by_len
@[simp] theorem pcDual2462 : IPC 920 = 1301 := by pc_by_len
@[simp] theorem pcDual2463 : IPC 920 = 1301 := by pc_by_len
@[simp] theorem pcDual2464 : IPC 920 = 1301 := by pc_by_len
@[simp] theorem pcDual2465 : IPC 923 = 1304 := by pc_by_len
@[simp] theorem pcDual8548 : IPC 387 = 528 := by pc_by_len
@[simp] theorem pcDual8549 : IPC 387 = 528 := by pc_by_len
@[simp] theorem pcDual8550 : IPC 387 = 528 := by pc_by_len
@[simp] theorem pcDual8551 : IPC 388 = 529 := by pc_by_len
@[simp] theorem pcDual8552 : IPC 389 = 530 := by pc_by_len
@[simp] theorem pcDual8553 : IPC 390 = 533 := by pc_by_len
@[simp] theorem pcDual8554 : IPC 391 = 536 := by pc_by_len
@[simp] theorem pcDual8555 : IPC 392 = 537 := by pc_by_len
@[simp] theorem pcDual8559 : IPC 393 = 540 := by pc_by_len
@[simp] theorem pcDual8560 : IPC 394 = 541 := by pc_by_len
@[simp] theorem pcDual8561 : IPC 395 = 542 := by pc_by_len
@[simp] theorem pcDual8562 : IPC 396 = 543 := by pc_by_len
@[simp] theorem pcDual8563 : IPC 397 = 544 := by pc_by_len
@[simp] theorem pcDual8564 : IPC 398 = 545 := by pc_by_len
@[simp] theorem pcDual8565 : IPC 399 = 548 := by pc_by_len
@[simp] theorem pcDual8566 : IPC 400 = 549 := by pc_by_len
@[simp] theorem pcDual8567 : IPC 401 = 550 := by pc_by_len
@[simp] theorem pcDual8568 : IPC 402 = 553 := by pc_by_len
@[simp] theorem pcDual8569 : IPC 403 = 554 := by pc_by_len
@[simp] theorem pcDual8570 : IPC 404 = 555 := by pc_by_len
@[simp] theorem pcDual8571 : IPC 405 = 556 := by pc_by_len
@[simp] theorem pcDual8572 : IPC 406 = 557 := by pc_by_len
@[simp] theorem pcDual8573 : IPC 407 = 558 := by pc_by_len
@[simp] theorem pcDual8574 : IPC 408 = 559 := by pc_by_len
@[simp] theorem pcDual8575 : IPC 409 = 560 := by pc_by_len
@[simp] theorem pcDual8576 : IPC 410 = 561 := by pc_by_len
@[simp] theorem pcDual8577 : IPC 411 = 562 := by pc_by_len
@[simp] theorem pcDual8578 : IPC 412 = 563 := by pc_by_len
@[simp] theorem pcDual8579 : IPC 413 = 564 := by pc_by_len
@[simp] theorem pcDual8580 : IPC 414 = 565 := by pc_by_len
@[simp] theorem pcDual8581 : IPC 415 = 566 := by pc_by_len
@[simp] theorem pcDual8582 : IPC 416 = 567 := by pc_by_len
@[simp] theorem pcDual8583 : IPC 417 = 568 := by pc_by_len
@[simp] theorem pcDual8584 : IPC 418 = 569 := by pc_by_len
@[simp] theorem pcDual8585 : IPC 419 = 570 := by pc_by_len
@[simp] theorem pcDual8586 : IPC 420 = 572 := by pc_by_len
@[simp] theorem pcDual8587 : IPC 421 = 573 := by pc_by_len
@[simp] theorem pcDual8588 : IPC 422 = 574 := by pc_by_len
@[simp] theorem pcDual8589 : IPC 423 = 575 := by pc_by_len
@[simp] theorem pcDual8590 : IPC 424 = 576 := by pc_by_len
@[simp] theorem pcDual8591 : IPC 425 = 577 := by pc_by_len
@[simp] theorem pcDual8592 : IPC 426 = 578 := by pc_by_len
@[simp] theorem pcDual8593 : IPC 427 = 581 := by pc_by_len
@[simp] theorem pcDual8594 : IPC 428 = 582 := by pc_by_len
@[simp] theorem pcDual8595 : IPC 429 = 583 := by pc_by_len
@[simp] theorem pcDual8596 : IPC 430 = 584 := by pc_by_len
@[simp] theorem pcDual8597 : IPC 431 = 585 := by pc_by_len
@[simp] theorem pcDual8598 : IPC 433 = 587 := by pc_by_len
@[simp] theorem pcDual8600 : IPC 434 = 620 := by pc_by_len
@[simp] theorem pcDual8601 : IPC 435 = 621 := by pc_by_len
@[simp] theorem pcDual8602 : IPC 436 = 622 := by pc_by_len
@[simp] theorem pcDual8603 : IPC 437 = 623 := by pc_by_len
@[simp] theorem pcDual8604 : IPC 438 = 624 := by pc_by_len
@[simp] theorem pcDual8605 : IPC 439 = 625 := by pc_by_len
@[simp] theorem pcDual8606 : IPC 440 = 626 := by pc_by_len
@[simp] theorem pcDual8607 : IPC 441 = 627 := by pc_by_len
@[simp] theorem pcDual8608 : IPC 442 = 628 := by pc_by_len
@[simp] theorem pcDual8609 : IPC 443 = 629 := by pc_by_len
@[simp] theorem pcDual8610 : IPC 444 = 630 := by pc_by_len
@[simp] theorem pcDual8611 : IPC 445 = 631 := by pc_by_len
@[simp] theorem pcDual8612 : IPC 446 = 632 := by pc_by_len
@[simp] theorem pcDual8613 : IPC 447 = 633 := by pc_by_len
@[simp] theorem pcDual8614 : IPC 448 = 634 := by pc_by_len
@[simp] theorem pcDual8615 : IPC 449 = 637 := by pc_by_len
@[simp] theorem pcDual8616 : IPC 450 = 638 := by pc_by_len
@[simp] theorem pcDual8617 : IPC 451 = 639 := by pc_by_len
@[simp] theorem pcDual8618 : IPC 452 = 640 := by pc_by_len
@[simp] theorem pcDual8619 : IPC 453 = 641 := by pc_by_len
@[simp] theorem pcDual8620 : IPC 454 = 642 := by pc_by_len
@[simp] theorem pcDual8621 : IPC 455 = 643 := by pc_by_len
@[simp] theorem pcDual8622 : IPC 456 = 644 := by pc_by_len
@[simp] theorem pcDual8623 : IPC 457 = 645 := by pc_by_len
@[simp] theorem pcDual8624 : IPC 458 = 646 := by pc_by_len
@[simp] theorem pcDual8625 : IPC 459 = 647 := by pc_by_len
@[simp] theorem pcDual8626 : IPC 460 = 648 := by pc_by_len
@[simp] theorem pcDual8627 : IPC 461 = 649 := by pc_by_len
@[simp] theorem pcDual8628 : IPC 462 = 650 := by pc_by_len
@[simp] theorem pcDual8629 : IPC 463 = 651 := by pc_by_len
@[simp] theorem pcDual8630 : IPC 464 = 652 := by pc_by_len
@[simp] theorem pcDual8631 : IPC 465 = 653 := by pc_by_len
@[simp] theorem pcDual8632 : IPC 466 = 654 := by pc_by_len
@[simp] theorem pcDual8633 : IPC 467 = 655 := by pc_by_len
@[simp] theorem pcDual8634 : IPC 468 = 656 := by pc_by_len
@[simp] theorem pcDual8635 : IPC 469 = 657 := by pc_by_len
@[simp] theorem pcDual8636 : IPC 470 = 658 := by pc_by_len
@[simp] theorem pcDual8637 : IPC 471 = 661 := by pc_by_len
@[simp] theorem pcDual8638 : IPC 472 = 662 := by pc_by_len
@[simp] theorem pcDual8639 : IPC 473 = 663 := by pc_by_len
@[simp] theorem pcDual8640 : IPC 474 = 664 := by pc_by_len
@[simp] theorem pcDual8641 : IPC 475 = 665 := by pc_by_len
@[simp] theorem pcDual8642 : IPC 476 = 668 := by pc_by_len
@[simp] theorem pcDual8643 : IPC 477 = 669 := by pc_by_len
@[simp] theorem pcDual8644 : IPC 478 = 670 := by pc_by_len
@[simp] theorem pcDual8645 : IPC 479 = 671 := by pc_by_len
@[simp] theorem pcDual8646 : IPC 480 = 672 := by pc_by_len
@[simp] theorem pcDual8647 : IPC 481 = 673 := by pc_by_len
@[simp] theorem pcDual8648 : IPC 482 = 674 := by pc_by_len
@[simp] theorem pcDual8649 : IPC 483 = 675 := by pc_by_len
@[simp] theorem pcDual8650 : IPC 484 = 676 := by pc_by_len
@[simp] theorem pcDual8651 : IPC 485 = 677 := by pc_by_len
@[simp] theorem pcDual8652 : IPC 486 = 678 := by pc_by_len
@[simp] theorem pcDual8653 : IPC 487 = 679 := by pc_by_len
@[simp] theorem pcDual8654 : IPC 488 = 680 := by pc_by_len
@[simp] theorem pcDual8655 : IPC 489 = 681 := by pc_by_len
@[simp] theorem pcDual8656 : IPC 490 = 682 := by pc_by_len
@[simp] theorem pcDual8657 : IPC 491 = 683 := by pc_by_len
@[simp] theorem pcDual8658 : IPC 492 = 684 := by pc_by_len
@[simp] theorem pcDual8659 : IPC 493 = 685 := by pc_by_len
@[simp] theorem pcDual8660 : IPC 494 = 686 := by pc_by_len
@[simp] theorem pcDual8661 : IPC 495 = 687 := by pc_by_len
@[simp] theorem pcDual8662 : IPC 496 = 688 := by pc_by_len
@[simp] theorem pcDual8663 : IPC 497 = 689 := by pc_by_len
@[simp] theorem pcDual8664 : IPC 498 = 690 := by pc_by_len
@[simp] theorem pcDual8665 : IPC 499 = 693 := by pc_by_len
@[simp] theorem pcDual8666 : IPC 500 = 694 := by pc_by_len
@[simp] theorem pcDual8667 : IPC 501 = 695 := by pc_by_len
@[simp] theorem pcDual8668 : IPC 502 = 696 := by pc_by_len
@[simp] theorem pcDual8669 : IPC 503 = 697 := by pc_by_len
@[simp] theorem pcDual8670 : IPC 504 = 700 := by pc_by_len
@[simp] theorem pcDual8671 : IPC 505 = 701 := by pc_by_len
@[simp] theorem pcDual8672 : IPC 506 = 702 := by pc_by_len
@[simp] theorem pcDual8673 : IPC 507 = 703 := by pc_by_len
@[simp] theorem pcDual8674 : IPC 508 = 704 := by pc_by_len
@[simp] theorem pcDual8675 : IPC 509 = 705 := by pc_by_len
@[simp] theorem pcDual8676 : IPC 510 = 706 := by pc_by_len
@[simp] theorem pcDual8677 : IPC 511 = 707 := by pc_by_len
@[simp] theorem pcDual8678 : IPC 512 = 708 := by pc_by_len
@[simp] theorem pcDual8679 : IPC 513 = 711 := by pc_by_len
@[simp] theorem pcDual8680 : IPC 514 = 712 := by pc_by_len
@[simp] theorem pcDual8681 : IPC 515 = 713 := by pc_by_len
@[simp] theorem pcDual8682 : IPC 516 = 714 := by pc_by_len
@[simp] theorem pcDual8683 : IPC 517 = 715 := by pc_by_len
@[simp] theorem pcDual8684 : IPC 518 = 716 := by pc_by_len
@[simp] theorem pcDual8685 : IPC 519 = 717 := by pc_by_len
@[simp] theorem pcDual8686 : IPC 520 = 718 := by pc_by_len
@[simp] theorem pcDual8687 : IPC 521 = 719 := by pc_by_len
@[simp] theorem pcDual8688 : IPC 522 = 720 := by pc_by_len
@[simp] theorem pcDual8689 : IPC 523 = 721 := by pc_by_len
@[simp] theorem pcDual8690 : IPC 524 = 722 := by pc_by_len
@[simp] theorem pcDual8691 : IPC 525 = 723 := by pc_by_len
@[simp] theorem pcDual8692 : IPC 526 = 724 := by pc_by_len
@[simp] theorem pcDual8693 : IPC 527 = 725 := by pc_by_len
@[simp] theorem pcDual8694 : IPC 528 = 726 := by pc_by_len
@[simp] theorem pcDual8695 : IPC 529 = 729 := by pc_by_len
@[simp] theorem pcDual8696 : IPC 530 = 730 := by pc_by_len
@[simp] theorem pcDual8697 : IPC 531 = 731 := by pc_by_len
@[simp] theorem pcDual8698 : IPC 532 = 732 := by pc_by_len
@[simp] theorem pcDual8699 : IPC 533 = 733 := by pc_by_len
@[simp] theorem pcDual8700 : IPC 534 = 736 := by pc_by_len
@[simp] theorem pcDual8701 : IPC 535 = 737 := by pc_by_len
@[simp] theorem pcDual8702 : IPC 536 = 738 := by pc_by_len
@[simp] theorem pcDual8703 : IPC 537 = 739 := by pc_by_len
@[simp] theorem pcDual8704 : IPC 538 = 740 := by pc_by_len
@[simp] theorem pcDual8705 : IPC 539 = 741 := by pc_by_len
@[simp] theorem pcDual8706 : IPC 540 = 742 := by pc_by_len
@[simp] theorem pcDual8707 : IPC 541 = 743 := by pc_by_len
@[simp] theorem pcDual8708 : IPC 542 = 744 := by pc_by_len
@[simp] theorem pcDual8709 : IPC 543 = 747 := by pc_by_len
@[simp] theorem pcDual8710 : IPC 544 = 748 := by pc_by_len
@[simp] theorem pcDual8711 : IPC 545 = 749 := by pc_by_len
@[simp] theorem pcDual8712 : IPC 546 = 750 := by pc_by_len
@[simp] theorem pcDual8713 : IPC 546 = 750 := by pc_by_len
@[simp] theorem pcDual8714 : IPC 547 = 753 := by pc_by_len
@[simp] theorem pcDual8715 : IPC 547 = 753 := by pc_by_len
@[simp] theorem pcDual8716 : IPC 550 = 756 := by pc_by_len
@[simp] theorem pcDual8717 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8718 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8719 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8720 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8721 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8722 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8723 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8724 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8725 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8726 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8727 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8728 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8729 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8730 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8731 : IPC 549 = 755 := by pc_by_len
@[simp] theorem pcDual8732 : IPC 550 = 756 := by pc_by_len
@[simp] theorem pcDual8733 : IPC 551 = 757 := by pc_by_len
@[simp] theorem pcDual8734 : IPC 552 = 758 := by pc_by_len
@[simp] theorem pcDual8735 : IPC 553 = 759 := by pc_by_len
@[simp] theorem restoredGeneralPC2339 : cachedArtifact.instructionPC 6627 = 8792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2340 : cachedArtifact.instructionPC 6628 = 8795 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2341 : cachedArtifact.instructionPC 6629 = 8796 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2342 : cachedArtifact.instructionPC 6630 = 8797 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2343 : cachedArtifact.instructionPC 6631 = 8798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2344 : cachedArtifact.instructionPC 6631 = 8798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2345 : cachedArtifact.instructionPC 6632 = 8801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2346 : cachedArtifact.instructionPC 6632 = 8801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2347 : cachedArtifact.instructionPC 6632 = 8801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2348 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2349 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2350 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2351 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2352 : cachedArtifact.instructionPC 6634 = 8803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2353 : cachedArtifact.instructionPC 6634 = 8803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2354 : cachedArtifact.instructionPC 6635 = 8804 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2355 : cachedArtifact.instructionPC 6636 = 8805 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2356 : cachedArtifact.instructionPC 6634 = 8803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2412 : cachedArtifact.instructionPC 912 = 1289 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2413 : cachedArtifact.instructionPC 913 = 1292 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2414 : cachedArtifact.instructionPC 914 = 1293 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2415 : cachedArtifact.instructionPC 915 = 1294 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2416 : cachedArtifact.instructionPC 919 = 1298 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem restoredGeneralPC2417 : cachedArtifact.instructionPC 920 = 1301 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2339 : cachedArtifact.instructionPC 6627 = 8792 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2340 : cachedArtifact.instructionPC 6628 = 8795 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2341 : cachedArtifact.instructionPC 6629 = 8796 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2342 : cachedArtifact.instructionPC 6630 = 8797 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2343 : cachedArtifact.instructionPC 6631 = 8798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2344 : cachedArtifact.instructionPC 6631 = 8798 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2345 : cachedArtifact.instructionPC 6632 = 8801 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2346 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2347 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2348 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2349 : cachedArtifact.instructionPC 6633 = 8802 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2350 : cachedArtifact.instructionPC 6634 = 8803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2351 : cachedArtifact.instructionPC 6634 = 8803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2352 : cachedArtifact.instructionPC 6635 = 8804 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2353 : cachedArtifact.instructionPC 6636 = 8805 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2354 : cachedArtifact.instructionPC 6634 = 8803 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2355 : cachedArtifact.instructionPC 6637 = 8806 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2451 : cachedArtifact.instructionPC 7293 = 9735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2452 : cachedArtifact.instructionPC 7293 = 9735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2453 : cachedArtifact.instructionPC 7293 = 9735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2454 : cachedArtifact.instructionPC 7293 = 9735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC2455 : cachedArtifact.instructionPC 7293 = 9735 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8399 : cachedArtifact.instructionPC 542 = 744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8400 : cachedArtifact.instructionPC 543 = 747 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8401 : cachedArtifact.instructionPC 544 = 748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8402 : cachedArtifact.instructionPC 545 = 749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8403 : cachedArtifact.instructionPC 546 = 750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8404 : cachedArtifact.instructionPC 546 = 750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8405 : cachedArtifact.instructionPC 547 = 753 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8406 : cachedArtifact.instructionPC 548 = 754 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8407 : cachedArtifact.instructionPC 549 = 755 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8408 : cachedArtifact.instructionPC 549 = 755 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8409 : cachedArtifact.instructionPC 550 = 756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8410 : cachedArtifact.instructionPC 551 = 757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8411 : cachedArtifact.instructionPC 552 = 758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8412 : cachedArtifact.instructionPC 553 = 759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8413 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8414 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8415 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8416 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8417 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8418 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8419 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8420 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8421 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8422 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8423 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8424 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8425 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8426 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8427 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8428 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8429 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8430 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8431 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8432 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem lazyTopPC8433 : cachedArtifact.instructionPC 555 = 761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2361 : cachedArtifact.instructionPC 863 = 1223 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2362 : cachedArtifact.instructionPC 864 = 1224 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2363 : cachedArtifact.instructionPC 865 = 1227 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2364 : cachedArtifact.instructionPC 866 = 1228 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2365 : cachedArtifact.instructionPC 866 = 1228 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2366 : cachedArtifact.instructionPC 867 = 1229 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2367 : cachedArtifact.instructionPC 868 = 1230 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2368 : cachedArtifact.instructionPC 869 = 1233 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2369 : cachedArtifact.instructionPC 870 = 1234 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2370 : cachedArtifact.instructionPC 871 = 1235 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2371 : cachedArtifact.instructionPC 872 = 1236 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2372 : cachedArtifact.instructionPC 873 = 1237 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2373 : cachedArtifact.instructionPC 874 = 1240 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2374 : cachedArtifact.instructionPC 875 = 1241 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2375 : cachedArtifact.instructionPC 876 = 1242 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2376 : cachedArtifact.instructionPC 877 = 1243 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2377 : cachedArtifact.instructionPC 878 = 1244 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2378 : cachedArtifact.instructionPC 879 = 1245 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2379 : cachedArtifact.instructionPC 880 = 1246 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2380 : cachedArtifact.instructionPC 881 = 1247 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2381 : cachedArtifact.instructionPC 882 = 1248 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2382 : cachedArtifact.instructionPC 883 = 1249 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2383 : cachedArtifact.instructionPC 884 = 1250 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2384 : cachedArtifact.instructionPC 885 = 1251 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2385 : cachedArtifact.instructionPC 886 = 1252 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2386 : cachedArtifact.instructionPC 887 = 1253 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2387 : cachedArtifact.instructionPC 888 = 1254 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2388 : cachedArtifact.instructionPC 889 = 1255 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2389 : cachedArtifact.instructionPC 890 = 1256 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2390 : cachedArtifact.instructionPC 891 = 1257 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2391 : cachedArtifact.instructionPC 892 = 1258 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2392 : cachedArtifact.instructionPC 893 = 1260 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2393 : cachedArtifact.instructionPC 894 = 1261 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2394 : cachedArtifact.instructionPC 895 = 1262 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2395 : cachedArtifact.instructionPC 896 = 1265 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2396 : cachedArtifact.instructionPC 897 = 1266 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2397 : cachedArtifact.instructionPC 898 = 1267 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2398 : cachedArtifact.instructionPC 899 = 1270 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2399 : cachedArtifact.instructionPC 900 = 1271 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2400 : cachedArtifact.instructionPC 901 = 1272 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2401 : cachedArtifact.instructionPC 902 = 1275 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2402 : cachedArtifact.instructionPC 903 = 1276 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2403 : cachedArtifact.instructionPC 904 = 1277 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2404 : cachedArtifact.instructionPC 905 = 1278 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2405 : cachedArtifact.instructionPC 906 = 1279 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2406 : cachedArtifact.instructionPC 907 = 1282 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2407 : cachedArtifact.instructionPC 908 = 1283 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2408 : cachedArtifact.instructionPC 909 = 1284 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2409 : cachedArtifact.instructionPC 910 = 1285 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2410 : cachedArtifact.instructionPC 911 = 1288 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2411 : cachedArtifact.instructionPC 912 = 1289 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2412 : cachedArtifact.instructionPC 913 = 1292 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2413 : cachedArtifact.instructionPC 914 = 1293 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2414 : cachedArtifact.instructionPC 915 = 1294 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2415 : cachedArtifact.instructionPC 919 = 1298 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2416 : cachedArtifact.instructionPC 920 = 1301 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2417 : cachedArtifact.instructionPC 921 = 1302 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem inlineRepairPC2418 : cachedArtifact.instructionPC 923 = 1304 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2009 : cachedArtifact.instructionPC 8040 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2010 : cachedArtifact.instructionPC 8041 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2011 : cachedArtifact.instructionPC 8042 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2012 : cachedArtifact.instructionPC 8043 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2013 : cachedArtifact.instructionPC 8044 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2014 : cachedArtifact.instructionPC 8045 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2015 : cachedArtifact.instructionPC 8046 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2016 : cachedArtifact.instructionPC 8047 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2017 : cachedArtifact.instructionPC 8048 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2018 : cachedArtifact.instructionPC 8049 = 10656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2019 : cachedArtifact.instructionPC 8050 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2020 : cachedArtifact.instructionPC 8051 = 10660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2021 : cachedArtifact.instructionPC 8052 = 10661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2022 : cachedArtifact.instructionPC 8053 = 10663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2023 : cachedArtifact.instructionPC 8056 = 10668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2024 : cachedArtifact.instructionPC 8057 = 10671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2025 : cachedArtifact.instructionPC 8058 = 10672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2026 : cachedArtifact.instructionPC 8059 = 10673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2027 : cachedArtifact.instructionPC 8060 = 10674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2028 : cachedArtifact.instructionPC 8061 = 10675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2029 : cachedArtifact.instructionPC 8062 = 10677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2030 : cachedArtifact.instructionPC 8062 = 10677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2031 : cachedArtifact.instructionPC 8063 = 10678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2032 : cachedArtifact.instructionPC 8064 = 10681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2033 : cachedArtifact.instructionPC 8065 = 10682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2034 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2035 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2036 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2037 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2038 : cachedArtifact.instructionPC 8069 = 10687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2039 : cachedArtifact.instructionPC 8070 = 10689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2040 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2041 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2042 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2043 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2044 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2045 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2046 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2047 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2048 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2049 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2050 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2051 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2052 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2053 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2054 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2055 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2056 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2057 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2058 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directInitialPC2059 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2009 : cachedArtifact.instructionPC 8040 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2010 : cachedArtifact.instructionPC 8041 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2011 : cachedArtifact.instructionPC 8042 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2012 : cachedArtifact.instructionPC 8043 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2013 : cachedArtifact.instructionPC 8044 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2014 : cachedArtifact.instructionPC 8045 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2015 : cachedArtifact.instructionPC 8046 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2016 : cachedArtifact.instructionPC 8047 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2017 : cachedArtifact.instructionPC 8048 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2018 : cachedArtifact.instructionPC 8049 = 10656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2019 : cachedArtifact.instructionPC 8050 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2020 : cachedArtifact.instructionPC 8051 = 10660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2021 : cachedArtifact.instructionPC 8052 = 10661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2022 : cachedArtifact.instructionPC 8053 = 10663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2023 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2024 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2025 : cachedArtifact.instructionPC 8055 = 10667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2026 : cachedArtifact.instructionPC 8056 = 10668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2027 : cachedArtifact.instructionPC 8057 = 10671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2028 : cachedArtifact.instructionPC 8058 = 10672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2029 : cachedArtifact.instructionPC 8059 = 10673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2030 : cachedArtifact.instructionPC 8060 = 10674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2031 : cachedArtifact.instructionPC 8061 = 10675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2032 : cachedArtifact.instructionPC 8062 = 10677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2033 : cachedArtifact.instructionPC 8063 = 10678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2034 : cachedArtifact.instructionPC 8064 = 10681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2035 : cachedArtifact.instructionPC 8065 = 10682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2036 : cachedArtifact.instructionPC 8066 = 10683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2037 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2038 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2039 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2040 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2041 : cachedArtifact.instructionPC 8069 = 10687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2042 : cachedArtifact.instructionPC 8070 = 10689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2043 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2044 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2045 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2046 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2047 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2048 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2049 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2050 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2051 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2052 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2053 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2054 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2055 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2056 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2057 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2058 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2059 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2060 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2061 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem directWordInitPC2062 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2009 : cachedArtifact.instructionPC 8040 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2010 : cachedArtifact.instructionPC 8041 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2011 : cachedArtifact.instructionPC 8042 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2012 : cachedArtifact.instructionPC 8043 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2013 : cachedArtifact.instructionPC 8044 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2014 : cachedArtifact.instructionPC 8045 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2015 : cachedArtifact.instructionPC 8046 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2016 : cachedArtifact.instructionPC 8047 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2017 : cachedArtifact.instructionPC 8048 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2018 : cachedArtifact.instructionPC 8049 = 10656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2019 : cachedArtifact.instructionPC 8050 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2020 : cachedArtifact.instructionPC 8050 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2021 : cachedArtifact.instructionPC 8051 = 10660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2022 : cachedArtifact.instructionPC 8052 = 10661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2023 : cachedArtifact.instructionPC 8053 = 10663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2024 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2025 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2026 : cachedArtifact.instructionPC 8055 = 10667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2027 : cachedArtifact.instructionPC 8056 = 10668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2028 : cachedArtifact.instructionPC 8057 = 10671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2029 : cachedArtifact.instructionPC 8058 = 10672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2030 : cachedArtifact.instructionPC 8059 = 10673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2031 : cachedArtifact.instructionPC 8060 = 10674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2032 : cachedArtifact.instructionPC 8061 = 10675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2033 : cachedArtifact.instructionPC 8062 = 10677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2034 : cachedArtifact.instructionPC 8063 = 10678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2035 : cachedArtifact.instructionPC 8064 = 10681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2036 : cachedArtifact.instructionPC 8065 = 10682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2037 : cachedArtifact.instructionPC 8066 = 10683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2038 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2039 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2040 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2041 : cachedArtifact.instructionPC 8069 = 10687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2042 : cachedArtifact.instructionPC 8070 = 10689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2043 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2044 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2045 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2046 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2047 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2048 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2049 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2050 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2051 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2052 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2053 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2054 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2055 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2056 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2057 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2058 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2059 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2060 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2061 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2062 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2063 : cachedArtifact.instructionPC 8091 = 10730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2064 : cachedArtifact.instructionPC 8092 = 10733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem conventionalInitPC2065 : cachedArtifact.instructionPC 8092 = 10733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2009 : cachedArtifact.instructionPC 8040 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2010 : cachedArtifact.instructionPC 8041 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2011 : cachedArtifact.instructionPC 8042 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2012 : cachedArtifact.instructionPC 8043 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2013 : cachedArtifact.instructionPC 8044 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2014 : cachedArtifact.instructionPC 8045 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2015 : cachedArtifact.instructionPC 8046 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2016 : cachedArtifact.instructionPC 8047 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2017 : cachedArtifact.instructionPC 8048 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2018 : cachedArtifact.instructionPC 8049 = 10656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2019 : cachedArtifact.instructionPC 8050 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2020 : cachedArtifact.instructionPC 8051 = 10660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2021 : cachedArtifact.instructionPC 8052 = 10661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2022 : cachedArtifact.instructionPC 8053 = 10663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2023 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2024 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2025 : cachedArtifact.instructionPC 8055 = 10667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2026 : cachedArtifact.instructionPC 8056 = 10668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2027 : cachedArtifact.instructionPC 8057 = 10671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2028 : cachedArtifact.instructionPC 8058 = 10672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2029 : cachedArtifact.instructionPC 8059 = 10673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2030 : cachedArtifact.instructionPC 8060 = 10674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2031 : cachedArtifact.instructionPC 8061 = 10675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2032 : cachedArtifact.instructionPC 8062 = 10677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2033 : cachedArtifact.instructionPC 8063 = 10678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2034 : cachedArtifact.instructionPC 8064 = 10681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2035 : cachedArtifact.instructionPC 8065 = 10682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2036 : cachedArtifact.instructionPC 8066 = 10683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2037 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2038 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2039 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2040 : cachedArtifact.instructionPC 8069 = 10687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2041 : cachedArtifact.instructionPC 8070 = 10689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2042 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2043 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2044 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2045 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2046 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2047 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2048 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2049 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2050 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2051 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2052 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2053 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2054 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2055 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2056 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2057 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2058 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2059 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2060 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2061 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2062 : cachedArtifact.instructionPC 8091 = 10730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2063 : cachedArtifact.instructionPC 8092 = 10733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem singleInitPC2064 : cachedArtifact.instructionPC 8092 = 10733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2009 : cachedArtifact.instructionPC 8040 = 10643 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2010 : cachedArtifact.instructionPC 8041 = 10644 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2011 : cachedArtifact.instructionPC 8042 = 10645 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2012 : cachedArtifact.instructionPC 8043 = 10646 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2013 : cachedArtifact.instructionPC 8044 = 10649 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2014 : cachedArtifact.instructionPC 8045 = 10650 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2015 : cachedArtifact.instructionPC 8046 = 10651 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2016 : cachedArtifact.instructionPC 8047 = 10652 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2017 : cachedArtifact.instructionPC 8048 = 10653 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2018 : cachedArtifact.instructionPC 8049 = 10656 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2019 : cachedArtifact.instructionPC 8050 = 10657 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2020 : cachedArtifact.instructionPC 8051 = 10660 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2021 : cachedArtifact.instructionPC 8052 = 10661 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2022 : cachedArtifact.instructionPC 8053 = 10663 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2023 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2024 : cachedArtifact.instructionPC 8054 = 10664 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2025 : cachedArtifact.instructionPC 8055 = 10667 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2026 : cachedArtifact.instructionPC 8056 = 10668 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2027 : cachedArtifact.instructionPC 8057 = 10671 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2028 : cachedArtifact.instructionPC 8058 = 10672 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2029 : cachedArtifact.instructionPC 8059 = 10673 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2030 : cachedArtifact.instructionPC 8060 = 10674 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2031 : cachedArtifact.instructionPC 8061 = 10675 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2032 : cachedArtifact.instructionPC 8062 = 10677 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2033 : cachedArtifact.instructionPC 8063 = 10678 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2034 : cachedArtifact.instructionPC 8064 = 10681 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2035 : cachedArtifact.instructionPC 8065 = 10682 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2036 : cachedArtifact.instructionPC 8066 = 10683 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2037 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2038 : cachedArtifact.instructionPC 8067 = 10684 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2039 : cachedArtifact.instructionPC 8068 = 10686 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2040 : cachedArtifact.instructionPC 8069 = 10687 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2041 : cachedArtifact.instructionPC 8070 = 10689 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2042 : cachedArtifact.instructionPC 8071 = 10690 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2043 : cachedArtifact.instructionPC 8072 = 10693 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2044 : cachedArtifact.instructionPC 8073 = 10694 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2045 : cachedArtifact.instructionPC 8074 = 10697 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2046 : cachedArtifact.instructionPC 8075 = 10698 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2047 : cachedArtifact.instructionPC 8076 = 10701 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2048 : cachedArtifact.instructionPC 8077 = 10702 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2049 : cachedArtifact.instructionPC 8078 = 10705 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2050 : cachedArtifact.instructionPC 8079 = 10706 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2051 : cachedArtifact.instructionPC 8080 = 10709 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2052 : cachedArtifact.instructionPC 8081 = 10710 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2053 : cachedArtifact.instructionPC 8082 = 10713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2054 : cachedArtifact.instructionPC 8083 = 10714 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2055 : cachedArtifact.instructionPC 8084 = 10717 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2056 : cachedArtifact.instructionPC 8085 = 10718 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2057 : cachedArtifact.instructionPC 8086 = 10721 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2058 : cachedArtifact.instructionPC 8087 = 10722 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2059 : cachedArtifact.instructionPC 8088 = 10725 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2060 : cachedArtifact.instructionPC 8089 = 10726 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2061 : cachedArtifact.instructionPC 8090 = 10729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2062 : cachedArtifact.instructionPC 8091 = 10730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2063 : cachedArtifact.instructionPC 8092 = 10733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem readyInitPC2064 : cachedArtifact.instructionPC 8093 = 10734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
end CycleSubmission.Global.ShiftPCs

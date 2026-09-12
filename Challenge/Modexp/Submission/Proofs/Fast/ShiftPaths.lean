import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block of the selected shift-reduce program. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 (.Dup ⟨3, by decide⟩),
   opAt 2585 .EQ,
   pushAt 2586 0 0,
   opAt 2587 .MLOAD,
   pushAt 2588 1 255,
   opAt 2589 .SHR,
   opAt 2590 .AND,
   opAt 2591 .ISZERO,
   pushAt 2592 2 3481,
   opAt 2593 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2594 (.Dup ⟨0, by decide⟩),
   pushAt 2595 1 96,
   pushAt 2596 2 256,
   opAt 2597 .CALLDATACOPY,
   opAt 2598 (.Dup ⟨0, by decide⟩),
   pushAt 2599 1 96,
   pushAt 2600 2 4160,
   opAt 2601 .CALLDATACOPY,
   pushAt 2602 0 0,
   pushAt 2603 2 4128,
   opAt 2604 .MSTORE,
   pushAt 2605 2 3498,
   pushAt 2606 2 512,
   pushAt 2607 2 4804,
   opAt 2608 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2609 .JUMPDEST,
   pushAt 2610 1 1,
   pushAt 2611 2 1024,
   opAt 2612 .MSTORE,
   pushAt 2613 2 1435,
   pushAt 2614 2 1024,
   pushAt 2615 2 2216,
   opAt 2616 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2617 .JUMPDEST,
   pushAt 2618 1 1,
   pushAt 2619 2 5312,
   opAt 2620 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2621 .JUMPDEST,
   opAt 2622 (.Dup ⟨0, by decide⟩),
   opAt 2623 .MLOAD,
   opAt 2624 .NOT,
   opAt 2625 (.Dup ⟨2, by decide⟩),
   opAt 2626 .ADD,
   opAt 2627 (.Dup ⟨2, by decide⟩),
   opAt 2628 (.Dup ⟨1, by decide⟩),
   opAt 2629 .LT,
   opAt 2630 (.Swap ⟨2, by decide⟩),
   opAt 2631 .POP,
   opAt 2632 (.Dup ⟨1, by decide⟩),
   pushAt 2633 2 1280,
   opAt 2634 .ADD,
   opAt 2635 .MSTORE,
   opAt 2636 (.Dup ⟨0, by decide⟩),
   opAt 2637 .ISZERO,
   pushAt 2638 2 3536,
   opAt 2639 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2640 1 31,
   opAt 2641 .NOT,
   opAt 2642 .ADD,
   pushAt 2643 2 3505,
   opAt 2644 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2645 .JUMPDEST,
   opAt 2646 .POP,
   opAt 2647 .POP,
   pushAt 2648 0 0,
   opAt 2649 .MLOAD,
   opAt 2650 (.Dup ⟨0, by decide⟩),
   pushAt 2651 0 0,
   opAt 2652 .SUB,
   opAt 2653 (.Dup ⟨1, by decide⟩),
   opAt 2654 .AND,
   opAt 2655 (.Dup ⟨0, by decide⟩),
   pushAt 2656 2 1536,
   opAt 2657 .MSTORE,
   opAt 2658 (.Dup ⟨0, by decide⟩),
   opAt 2659 (.Dup ⟨2, by decide⟩),
   opAt 2660 .DIV,
   opAt 2661 (.Dup ⟨0, by decide⟩),
   pushAt 2662 2 1568,
   opAt 2663 .MSTORE,
   opAt 2664 (.Dup ⟨1, by decide⟩),
   pushAt 2665 0 0,
   opAt 2666 .SUB,
   opAt 2667 (.Dup ⟨2, by decide⟩),
   opAt 2668 (.Swap ⟨0, by decide⟩),
   opAt 2669 .DIV,
   pushAt 2670 1 1,
   opAt 2671 .ADD,
   pushAt 2672 2 1600,
   opAt 2673 .MSTORE,
   opAt 2674 (.Dup ⟨0, by decide⟩),
   pushAt 2675 0 0,
   opAt 2676 .SUB,
   opAt 2677 (.Dup ⟨1, by decide⟩),
   opAt 2678 (.Swap ⟨0, by decide⟩),
   opAt 2679 .MOD,
   pushAt 2680 2 1632,
   opAt 2681 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2682 (.Dup ⟨0, by decide⟩),
   pushAt 2683 1 2,
   opAt 2684 .SUB,
   opAt 2685 (.Dup ⟨0, by decide⟩),
   opAt 2686 (.Dup ⟨2, by decide⟩),
   opAt 2687 .MUL,
   pushAt 2688 1 2,
   opAt 2689 .SUB,
   opAt 2690 .MUL,
   opAt 2691 (.Dup ⟨0, by decide⟩),
   opAt 2692 (.Dup ⟨2, by decide⟩),
   opAt 2693 .MUL,
   pushAt 2694 1 2,
   opAt 2695 .SUB,
   opAt 2696 .MUL,
   opAt 2697 (.Dup ⟨0, by decide⟩),
   opAt 2698 (.Dup ⟨2, by decide⟩),
   opAt 2699 .MUL,
   pushAt 2700 1 2,
   opAt 2701 .SUB,
   opAt 2702 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2703 (.Dup ⟨0, by decide⟩),
   opAt 2704 (.Dup ⟨2, by decide⟩),
   opAt 2705 .MUL,
   pushAt 2706 1 2,
   opAt 2707 .SUB,
   opAt 2708 .MUL,
   opAt 2709 (.Dup ⟨0, by decide⟩),
   opAt 2710 (.Dup ⟨2, by decide⟩),
   opAt 2711 .MUL,
   pushAt 2712 1 2,
   opAt 2713 .SUB,
   opAt 2714 .MUL,
   opAt 2715 (.Dup ⟨0, by decide⟩),
   opAt 2716 (.Dup ⟨2, by decide⟩),
   opAt 2717 .MUL,
   pushAt 2718 1 2,
   opAt 2719 .SUB,
   opAt 2720 .MUL,
   opAt 2721 (.Dup ⟨0, by decide⟩),
   opAt 2722 (.Dup ⟨2, by decide⟩),
   opAt 2723 .MUL,
   pushAt 2724 1 2,
   opAt 2725 .SUB,
   opAt 2726 .MUL,
   pushAt 2727 2 1664,
   opAt 2728 .MSTORE,
   opAt 2729 .POP,
   opAt 2730 .POP,
   opAt 2731 .POP,
   opAt 2732 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2733 .JUMPDEST,
   opAt 2734 (.Dup ⟨0, by decide⟩),
   opAt 2735 .ISZERO,
   pushAt 2736 2 4030,
   opAt 2737 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2738 (.Dup ⟨1, by decide⟩),
   pushAt 2739 2 512,
   pushAt 2740 2 4128,
   opAt 2741 .MCOPY,
   pushAt 2742 0 0,
   pushAt 2743 2 5344,
   opAt 2744 .MLOAD,
   opAt 2745 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2746 2 512,
   opAt 2747 .MLOAD,
   pushAt 2748 2 1536,
   opAt 2749 .MLOAD,
   opAt 2750 (.Dup ⟨0, by decide⟩),
   opAt 2751 (.Dup ⟨2, by decide⟩),
   opAt 2752 .DIV,
   opAt 2753 (.Swap ⟨1, by decide⟩),
   opAt 2754 .MOD,
   pushAt 2755 2 1600,
   opAt 2756 .MLOAD,
   opAt 2757 .MUL,
   pushAt 2758 2 544,
   opAt 2759 .MLOAD,
   pushAt 2760 2 1536,
   opAt 2761 .MLOAD,
   opAt 2762 (.Swap ⟨0, by decide⟩),
   opAt 2763 .DIV,
   opAt 2764 .ADD,
   pushAt 2765 2 1568,
   opAt 2766 .MLOAD,
   opAt 2767 (.Dup ⟨0, by decide⟩),
   pushAt 2768 2 1632,
   opAt 2769 .MLOAD,
   opAt 2770 (.Dup ⟨4, by decide⟩),
   opAt 2771 .MULMOD,
   opAt 2772 (.Dup ⟨2, by decide⟩),
   opAt 2773 .ADDMOD,
   opAt 2774 (.Swap ⟨0, by decide⟩),
   opAt 2775 .SUB,
   pushAt 2776 2 1664,
   opAt 2777 .MLOAD,
   opAt 2778 .MUL,
   opAt 2779 (.Dup ⟨0, by decide⟩),
   pushAt 2780 0 0,
   opAt 2781 .MLOAD,
   opAt 2782 .MUL,
   pushAt 2783 2 544,
   opAt 2784 .MLOAD,
   opAt 2785 .SUB,
   pushAt 2786 1 32,
   opAt 2787 .MLOAD,
   pushAt 2788 1 128,
   opAt 2789 .SHR,
   opAt 2790 (.Dup ⟨2, by decide⟩),
   pushAt 2791 1 128,
   opAt 2792 .SHR,
   opAt 2793 .MUL,
   opAt 2794 .GT,
   opAt 2795 (.Swap ⟨0, by decide⟩),
   opAt 2796 .SUB,
   opAt 2797 (.Swap ⟨0, by decide⟩),
   pushAt 2798 2 1568,
   opAt 2799 .MLOAD,
   opAt 2800 .GT,
   opAt 2801 .ISZERO,
   pushAt 2802 0 0,
   opAt 2803 .SUB,
   opAt 2804 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2805 0 0,
   pushAt 2806 2 5344,
   opAt 2807 .MLOAD,
   pushAt 2808 2 5312,
   opAt 2809 .MLOAD,
   pushAt 2810 2 1280,
   opAt 2811 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2812 .JUMPDEST,
   opAt 2813 (.Dup ⟨0, by decide⟩),
   opAt 2814 .MLOAD,
   pushAt 2815 0 0,
   opAt 2816 .NOT,
   opAt 2817 (.Dup ⟨5, by decide⟩),
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .MUL,
   opAt 2820 (.Swap ⟨1, by decide⟩),
   opAt 2821 (.Dup ⟨6, by decide⟩),
   opAt 2822 .MULMOD,
   opAt 2823 (.Dup ⟨1, by decide⟩),
   opAt 2824 (.Dup ⟨1, by decide⟩),
   opAt 2825 .LT,
   opAt 2826 .SUB,
   opAt 2827 (.Dup ⟨4, by decide⟩),
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 .ADD,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Swap ⟨5, by decide⟩),
   opAt 2832 .GT,
   opAt 2833 .SUB,
   opAt 2834 .SUB,
   opAt 2835 (.Dup ⟨3, by decide⟩),
   opAt 2836 (.Dup ⟨3, by decide⟩),
   opAt 2837 .MLOAD,
   opAt 2838 .ADD,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Swap ⟨4, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 .ADD,
   opAt 2843 (.Swap ⟨2, by decide⟩),
   opAt 2844 (.Dup ⟨2, by decide⟩),
   pushAt 2845 1 31,
   opAt 2846 .NOT,
   opAt 2847 .ADD,
   opAt 2848 (.Swap ⟨2, by decide⟩),
   opAt 2849 .MSTORE,
   pushAt 2850 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2851 .ADD,
   pushAt 2852 2 4128,
   opAt 2853 (.Dup ⟨2, by decide⟩),
   opAt 2854 .GT,
   pushAt 2855 2 3759,
   opAt 2856 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2857 .POP,
   opAt 2858 .POP,
   pushAt 2859 2 4128,
   opAt 2860 .MLOAD,
   opAt 2861 (.Dup ⟨1, by decide⟩),
   opAt 2862 .ADD,
   opAt 2863 (.Dup ⟨1, by decide⟩),
   opAt 2864 (.Dup ⟨1, by decide⟩),
   opAt 2865 .LT,
   opAt 2866 (.Swap ⟨1, by decide⟩),
   opAt 2867 .POP,
   opAt 2868 (.Dup ⟨2, by decide⟩),
   opAt 2869 (.Dup ⟨1, by decide⟩),
   opAt 2870 .LT,
   opAt 2871 (.Swap ⟨0, by decide⟩),
   opAt 2872 (.Dup ⟨3, by decide⟩),
   opAt 2873 (.Swap ⟨0, by decide⟩),
   opAt 2874 .SUB,
   opAt 2875 (.Dup ⟨0, by decide⟩),
   pushAt 2876 2 4128,
   opAt 2877 .MSTORE,
   opAt 2878 .POP,
   opAt 2879 .GT,
   opAt 2880 (.Swap ⟨0, by decide⟩),
   opAt 2881 .POP,
   opAt 2882 .ISZERO,
   pushAt 2883 2 3942,
   opAt 2884 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2885 .JUMPDEST,
   pushAt 2886 0 0,
   pushAt 2887 2 5344,
   opAt 2888 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2889 .JUMPDEST,
   opAt 2890 (.Dup ⟨0, by decide⟩),
   opAt 2891 .MLOAD,
   opAt 2892 (.Dup ⟨1, by decide⟩),
   pushAt 2893 2 4160,
   opAt 2894 (.Swap ⟨0, by decide⟩),
   opAt 2895 .SUB,
   opAt 2896 .MLOAD,
   opAt 2897 (.Dup ⟨1, by decide⟩),
   opAt 2898 .ADD,
   opAt 2899 (.Dup ⟨0, by decide⟩),
   opAt 2900 (.Dup ⟨2, by decide⟩),
   opAt 2901 .GT,
   opAt 2902 (.Swap ⟨1, by decide⟩),
   opAt 2903 .POP,
   opAt 2904 (.Dup ⟨3, by decide⟩),
   opAt 2905 .ADD,
   opAt 2906 (.Dup ⟨0, by decide⟩),
   opAt 2907 (.Dup ⟨4, by decide⟩),
   opAt 2908 .GT,
   opAt 2909 (.Swap ⟨3, by decide⟩),
   opAt 2910 .POP,
   opAt 2911 (.Dup ⟨2, by decide⟩),
   opAt 2912 .MSTORE,
   opAt 2913 (.Swap ⟨0, by decide⟩),
   opAt 2914 (.Swap ⟨1, by decide⟩),
   opAt 2915 .OR,
   opAt 2916 (.Swap ⟨0, by decide⟩),
   pushAt 2917 1 31,
   opAt 2918 .NOT,
   opAt 2919 .ADD,
   pushAt 2920 2 4159,
   opAt 2921 (.Dup ⟨1, by decide⟩),
   opAt 2922 .GT,
   pushAt 2923 2 3881,
   opAt 2924 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2925 .POP,
   pushAt 2926 2 4128,
   opAt 2927 .MLOAD,
   opAt 2928 (.Dup ⟨1, by decide⟩),
   opAt 2929 .ADD,
   opAt 2930 (.Dup ⟨0, by decide⟩),
   pushAt 2931 2 4128,
   opAt 2932 .MSTORE,
   opAt 2933 .LT,
   opAt 2934 .ISZERO,
   pushAt 2935 2 3875,
   opAt 2936 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2937 .JUMPDEST,
   pushAt 2938 2 4128,
   opAt 2939 .MLOAD,
   opAt 2940 .ISZERO,
   pushAt 2941 2 4010,
   opAt 2942 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2943 0 0,
   pushAt 2944 2 5344,
   opAt 2945 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2946 .JUMPDEST,
   opAt 2947 (.Dup ⟨0, by decide⟩),
   opAt 2948 .MLOAD,
   pushAt 2949 2 4160,
   opAt 2950 (.Dup ⟨2, by decide⟩),
   opAt 2951 .SUB,
   opAt 2952 .MLOAD,
   opAt 2953 (.Dup ⟨1, by decide⟩),
   opAt 2954 (.Dup ⟨1, by decide⟩),
   opAt 2955 .GT,
   opAt 2956 (.Swap ⟨1, by decide⟩),
   opAt 2957 .SUB,
   opAt 2958 (.Dup ⟨3, by decide⟩),
   opAt 2959 (.Dup ⟨1, by decide⟩),
   opAt 2960 .LT,
   opAt 2961 (.Swap ⟨0, by decide⟩),
   opAt 2962 (.Dup ⟨4, by decide⟩),
   opAt 2963 (.Swap ⟨0, by decide⟩),
   opAt 2964 .SUB,
   opAt 2965 (.Dup ⟨3, by decide⟩),
   opAt 2966 .MSTORE,
   opAt 2967 .OR,
   opAt 2968 (.Swap ⟨1, by decide⟩),
   opAt 2969 .POP,
   pushAt 2970 1 31,
   opAt 2971 .NOT,
   opAt 2972 .ADD,
   pushAt 2973 2 4159,
   opAt 2974 (.Dup ⟨1, by decide⟩),
   opAt 2975 .GT,
   pushAt 2976 2 3957,
   opAt 2977 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2978 .POP,
   pushAt 2979 2 4128,
   opAt 2980 .MLOAD,
   opAt 2981 .SUB,
   pushAt 2982 2 4128,
   opAt 2983 .MSTORE,
   pushAt 2984 2 3942,
   opAt 2985 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2986 .JUMPDEST,
   pushAt 2987 2 4021,
   pushAt 2988 2 512,
   pushAt 2989 2 4804,
   opAt 2990 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2991 .JUMPDEST,
   pushAt 2992 0 0,
   opAt 2993 .NOT,
   opAt 2994 .ADD,
   pushAt 2995 3 3643,
   opAt 2996 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2997 .JUMPDEST,
   opAt 2998 .POP,
   pushAt 2999 2 5248,
   opAt 3000 .MLOAD,
   pushAt 3001 2 1280,
   pushAt 3002 2 1024,
   opAt 3003 .MCOPY,
   pushAt 3004 2 3273,
   opAt 3005 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3437 = true :=
  Artifact.isValidJumpDest_index 2582 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3481 = true :=
  Artifact.isValidJumpDest_index 2609 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3498 = true :=
  Artifact.isValidJumpDest_index 2617 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3505 = true :=
  Artifact.isValidJumpDest_index 2621 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3536 = true :=
  Artifact.isValidJumpDest_index 2645 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3643 = true :=
  Artifact.isValidJumpDest_index 2733 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3759 = true :=
  Artifact.isValidJumpDest_index 2812 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3875 = true :=
  Artifact.isValidJumpDest_index 2885 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3881 = true :=
  Artifact.isValidJumpDest_index 2889 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3942 = true :=
  Artifact.isValidJumpDest_index 2937 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3957 = true :=
  Artifact.isValidJumpDest_index 2946 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4010 = true :=
  Artifact.isValidJumpDest_index 2986 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4021 = true :=
  Artifact.isValidJumpDest_index 2991 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4030 = true :=
  Artifact.isValidJumpDest_index 2997 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast

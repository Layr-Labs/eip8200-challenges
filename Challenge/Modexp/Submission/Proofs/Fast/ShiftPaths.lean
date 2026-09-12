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
  [opAt 2604 .JUMPDEST,
   opAt 2605 (.Dup ⟨0, by decide⟩),
   opAt 2606 (.Dup ⟨3, by decide⟩),
   opAt 2607 .EQ,
   pushAt 2608 0 0,
   opAt 2609 .MLOAD,
   pushAt 2610 1 255,
   opAt 2611 .SHR,
   opAt 2612 .AND,
   opAt 2613 .ISZERO,
   pushAt 2614 2 3481,
   opAt 2615 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2616 (.Dup ⟨0, by decide⟩),
   pushAt 2617 1 96,
   pushAt 2618 2 1024,
   opAt 2619 .CALLDATACOPY,
   opAt 2620 (.Dup ⟨0, by decide⟩),
   pushAt 2621 1 96,
   pushAt 2622 2 8256,
   opAt 2623 .CALLDATACOPY,
   pushAt 2624 0 0,
   pushAt 2625 2 8224,
   opAt 2626 .MSTORE,
   pushAt 2627 2 3498,
   pushAt 2628 2 2048,
   pushAt 2629 2 4804,
   opAt 2630 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2631 .JUMPDEST,
   pushAt 2632 1 1,
   pushAt 2633 2 4096,
   opAt 2634 .MSTORE,
   pushAt 2635 2 1435,
   pushAt 2636 2 4096,
   pushAt 2637 2 2216,
   opAt 2638 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2639 .JUMPDEST,
   pushAt 2640 1 1,
   pushAt 2641 2 9408,
   opAt 2642 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2643 .JUMPDEST,
   opAt 2644 (.Dup ⟨0, by decide⟩),
   opAt 2645 .MLOAD,
   opAt 2646 .NOT,
   opAt 2647 (.Dup ⟨2, by decide⟩),
   opAt 2648 .ADD,
   opAt 2649 (.Dup ⟨2, by decide⟩),
   opAt 2650 (.Dup ⟨1, by decide⟩),
   opAt 2651 .LT,
   opAt 2652 (.Swap ⟨2, by decide⟩),
   opAt 2653 .POP,
   opAt 2654 (.Dup ⟨1, by decide⟩),
   pushAt 2655 2 5120,
   opAt 2656 .ADD,
   opAt 2657 .MSTORE,
   opAt 2658 (.Dup ⟨0, by decide⟩),
   opAt 2659 .ISZERO,
   pushAt 2660 2 3536,
   opAt 2661 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2662 1 31,
   opAt 2663 .NOT,
   opAt 2664 .ADD,
   pushAt 2665 2 3505,
   opAt 2666 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2667 .JUMPDEST,
   opAt 2668 .POP,
   opAt 2669 .POP,
   pushAt 2670 0 0,
   opAt 2671 .MLOAD,
   opAt 2672 (.Dup ⟨0, by decide⟩),
   pushAt 2673 0 0,
   opAt 2674 .SUB,
   opAt 2675 (.Dup ⟨1, by decide⟩),
   opAt 2676 .AND,
   opAt 2677 (.Dup ⟨0, by decide⟩),
   pushAt 2678 2 6144,
   opAt 2679 .MSTORE,
   opAt 2680 (.Dup ⟨0, by decide⟩),
   opAt 2681 (.Dup ⟨2, by decide⟩),
   opAt 2682 .DIV,
   opAt 2683 (.Dup ⟨0, by decide⟩),
   pushAt 2684 2 6176,
   opAt 2685 .MSTORE,
   opAt 2686 (.Dup ⟨1, by decide⟩),
   pushAt 2687 0 0,
   opAt 2688 .SUB,
   opAt 2689 (.Dup ⟨2, by decide⟩),
   opAt 2690 (.Swap ⟨0, by decide⟩),
   opAt 2691 .DIV,
   pushAt 2692 1 1,
   opAt 2693 .ADD,
   pushAt 2694 2 6208,
   opAt 2695 .MSTORE,
   opAt 2696 (.Dup ⟨0, by decide⟩),
   pushAt 2697 0 0,
   opAt 2698 .SUB,
   opAt 2699 (.Dup ⟨1, by decide⟩),
   opAt 2700 (.Swap ⟨0, by decide⟩),
   opAt 2701 .MOD,
   pushAt 2702 2 6240,
   opAt 2703 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2704 (.Dup ⟨0, by decide⟩),
   pushAt 2705 1 2,
   opAt 2706 .SUB,
   opAt 2707 (.Dup ⟨0, by decide⟩),
   opAt 2708 (.Dup ⟨2, by decide⟩),
   opAt 2709 .MUL,
   pushAt 2710 1 2,
   opAt 2711 .SUB,
   opAt 2712 .MUL,
   opAt 2713 (.Dup ⟨0, by decide⟩),
   opAt 2714 (.Dup ⟨2, by decide⟩),
   opAt 2715 .MUL,
   pushAt 2716 1 2,
   opAt 2717 .SUB,
   opAt 2718 .MUL,
   opAt 2719 (.Dup ⟨0, by decide⟩),
   opAt 2720 (.Dup ⟨2, by decide⟩),
   opAt 2721 .MUL,
   pushAt 2722 1 2,
   opAt 2723 .SUB,
   opAt 2724 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2725 (.Dup ⟨0, by decide⟩),
   opAt 2726 (.Dup ⟨2, by decide⟩),
   opAt 2727 .MUL,
   pushAt 2728 1 2,
   opAt 2729 .SUB,
   opAt 2730 .MUL,
   opAt 2731 (.Dup ⟨0, by decide⟩),
   opAt 2732 (.Dup ⟨2, by decide⟩),
   opAt 2733 .MUL,
   pushAt 2734 1 2,
   opAt 2735 .SUB,
   opAt 2736 .MUL,
   opAt 2737 (.Dup ⟨0, by decide⟩),
   opAt 2738 (.Dup ⟨2, by decide⟩),
   opAt 2739 .MUL,
   pushAt 2740 1 2,
   opAt 2741 .SUB,
   opAt 2742 .MUL,
   opAt 2743 (.Dup ⟨0, by decide⟩),
   opAt 2744 (.Dup ⟨2, by decide⟩),
   opAt 2745 .MUL,
   pushAt 2746 1 2,
   opAt 2747 .SUB,
   opAt 2748 .MUL,
   pushAt 2749 2 6272,
   opAt 2750 .MSTORE,
   opAt 2751 .POP,
   opAt 2752 .POP,
   opAt 2753 .POP,
   opAt 2754 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2755 .JUMPDEST,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   opAt 2757 .ISZERO,
   pushAt 2758 2 4030,
   opAt 2759 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2760 (.Dup ⟨1, by decide⟩),
   pushAt 2761 2 2048,
   pushAt 2762 2 8224,
   opAt 2763 .MCOPY,
   pushAt 2764 0 0,
   pushAt 2765 2 9440,
   opAt 2766 .MLOAD,
   opAt 2767 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2768 2 2048,
   opAt 2769 .MLOAD,
   pushAt 2770 2 6144,
   opAt 2771 .MLOAD,
   opAt 2772 (.Dup ⟨0, by decide⟩),
   opAt 2773 (.Dup ⟨2, by decide⟩),
   opAt 2774 .DIV,
   opAt 2775 (.Swap ⟨1, by decide⟩),
   opAt 2776 .MOD,
   pushAt 2777 2 6208,
   opAt 2778 .MLOAD,
   opAt 2779 .MUL,
   pushAt 2780 2 2080,
   opAt 2781 .MLOAD,
   pushAt 2782 2 6144,
   opAt 2783 .MLOAD,
   opAt 2784 (.Swap ⟨0, by decide⟩),
   opAt 2785 .DIV,
   opAt 2786 .ADD,
   pushAt 2787 2 6176,
   opAt 2788 .MLOAD,
   opAt 2789 (.Dup ⟨0, by decide⟩),
   pushAt 2790 2 6240,
   opAt 2791 .MLOAD,
   opAt 2792 (.Dup ⟨4, by decide⟩),
   opAt 2793 .MULMOD,
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .ADDMOD,
   opAt 2796 (.Swap ⟨0, by decide⟩),
   opAt 2797 .SUB,
   pushAt 2798 2 6272,
   opAt 2799 .MLOAD,
   opAt 2800 .MUL,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   pushAt 2802 0 0,
   opAt 2803 .MLOAD,
   opAt 2804 .MUL,
   pushAt 2805 2 2080,
   opAt 2806 .MLOAD,
   opAt 2807 .SUB,
   pushAt 2808 1 32,
   opAt 2809 .MLOAD,
   pushAt 2810 1 128,
   opAt 2811 .SHR,
   opAt 2812 (.Dup ⟨2, by decide⟩),
   pushAt 2813 1 128,
   opAt 2814 .SHR,
   opAt 2815 .MUL,
   opAt 2816 .GT,
   opAt 2817 (.Swap ⟨0, by decide⟩),
   opAt 2818 .SUB,
   opAt 2819 (.Swap ⟨0, by decide⟩),
   pushAt 2820 2 6176,
   opAt 2821 .MLOAD,
   opAt 2822 .GT,
   opAt 2823 .ISZERO,
   pushAt 2824 0 0,
   opAt 2825 .SUB,
   opAt 2826 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2827 0 0,
   pushAt 2828 2 9440,
   opAt 2829 .MLOAD,
   pushAt 2830 2 9408,
   opAt 2831 .MLOAD,
   pushAt 2832 2 5120,
   opAt 2833 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   opAt 2836 .MLOAD,
   pushAt 2837 0 0,
   opAt 2838 .NOT,
   opAt 2839 (.Dup ⟨5, by decide⟩),
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .MUL,
   opAt 2842 (.Swap ⟨1, by decide⟩),
   opAt 2843 (.Dup ⟨6, by decide⟩),
   opAt 2844 .MULMOD,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 .LT,
   opAt 2848 .SUB,
   opAt 2849 (.Dup ⟨4, by decide⟩),
   opAt 2850 (.Dup ⟨2, by decide⟩),
   opAt 2851 .ADD,
   opAt 2852 (.Dup ⟨0, by decide⟩),
   opAt 2853 (.Swap ⟨5, by decide⟩),
   opAt 2854 .GT,
   opAt 2855 .SUB,
   opAt 2856 .SUB,
   opAt 2857 (.Dup ⟨3, by decide⟩),
   opAt 2858 (.Dup ⟨3, by decide⟩),
   opAt 2859 .MLOAD,
   opAt 2860 .ADD,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 (.Swap ⟨4, by decide⟩),
   opAt 2863 .GT,
   opAt 2864 .ADD,
   opAt 2865 (.Swap ⟨2, by decide⟩),
   opAt 2866 (.Dup ⟨2, by decide⟩),
   pushAt 2867 1 31,
   opAt 2868 .NOT,
   opAt 2869 .ADD,
   opAt 2870 (.Swap ⟨2, by decide⟩),
   opAt 2871 .MSTORE,
   pushAt 2872 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2873 .ADD,
   pushAt 2874 2 8224,
   opAt 2875 (.Dup ⟨2, by decide⟩),
   opAt 2876 .GT,
   pushAt 2877 2 3759,
   opAt 2878 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2879 .POP,
   opAt 2880 .POP,
   pushAt 2881 2 8224,
   opAt 2882 .MLOAD,
   opAt 2883 (.Dup ⟨1, by decide⟩),
   opAt 2884 .ADD,
   opAt 2885 (.Dup ⟨1, by decide⟩),
   opAt 2886 (.Dup ⟨1, by decide⟩),
   opAt 2887 .LT,
   opAt 2888 (.Swap ⟨1, by decide⟩),
   opAt 2889 .POP,
   opAt 2890 (.Dup ⟨2, by decide⟩),
   opAt 2891 (.Dup ⟨1, by decide⟩),
   opAt 2892 .LT,
   opAt 2893 (.Swap ⟨0, by decide⟩),
   opAt 2894 (.Dup ⟨3, by decide⟩),
   opAt 2895 (.Swap ⟨0, by decide⟩),
   opAt 2896 .SUB,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   pushAt 2898 2 8224,
   opAt 2899 .MSTORE,
   opAt 2900 .POP,
   opAt 2901 .GT,
   opAt 2902 (.Swap ⟨0, by decide⟩),
   opAt 2903 .POP,
   opAt 2904 .ISZERO,
   pushAt 2905 2 3942,
   opAt 2906 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2907 .JUMPDEST,
   pushAt 2908 0 0,
   pushAt 2909 2 9440,
   opAt 2910 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2911 .JUMPDEST,
   opAt 2912 (.Dup ⟨0, by decide⟩),
   opAt 2913 .MLOAD,
   opAt 2914 (.Dup ⟨1, by decide⟩),
   pushAt 2915 2 8256,
   opAt 2916 (.Swap ⟨0, by decide⟩),
   opAt 2917 .SUB,
   opAt 2918 .MLOAD,
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .ADD,
   opAt 2921 (.Dup ⟨0, by decide⟩),
   opAt 2922 (.Dup ⟨2, by decide⟩),
   opAt 2923 .GT,
   opAt 2924 (.Swap ⟨1, by decide⟩),
   opAt 2925 .POP,
   opAt 2926 (.Dup ⟨3, by decide⟩),
   opAt 2927 .ADD,
   opAt 2928 (.Dup ⟨0, by decide⟩),
   opAt 2929 (.Dup ⟨4, by decide⟩),
   opAt 2930 .GT,
   opAt 2931 (.Swap ⟨3, by decide⟩),
   opAt 2932 .POP,
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 .MSTORE,
   opAt 2935 (.Swap ⟨0, by decide⟩),
   opAt 2936 (.Swap ⟨1, by decide⟩),
   opAt 2937 .OR,
   opAt 2938 (.Swap ⟨0, by decide⟩),
   pushAt 2939 1 31,
   opAt 2940 .NOT,
   opAt 2941 .ADD,
   pushAt 2942 2 8255,
   opAt 2943 (.Dup ⟨1, by decide⟩),
   opAt 2944 .GT,
   pushAt 2945 2 3881,
   opAt 2946 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2947 .POP,
   pushAt 2948 2 8224,
   opAt 2949 .MLOAD,
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 .ADD,
   opAt 2952 (.Dup ⟨0, by decide⟩),
   pushAt 2953 2 8224,
   opAt 2954 .MSTORE,
   opAt 2955 .LT,
   opAt 2956 .ISZERO,
   pushAt 2957 2 3875,
   opAt 2958 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2959 .JUMPDEST,
   pushAt 2960 2 8224,
   opAt 2961 .MLOAD,
   opAt 2962 .ISZERO,
   pushAt 2963 2 4010,
   opAt 2964 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2965 0 0,
   pushAt 2966 2 9440,
   opAt 2967 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2968 .JUMPDEST,
   opAt 2969 (.Dup ⟨0, by decide⟩),
   opAt 2970 .MLOAD,
   pushAt 2971 2 8256,
   opAt 2972 (.Dup ⟨2, by decide⟩),
   opAt 2973 .SUB,
   opAt 2974 .MLOAD,
   opAt 2975 (.Dup ⟨1, by decide⟩),
   opAt 2976 (.Dup ⟨1, by decide⟩),
   opAt 2977 .GT,
   opAt 2978 (.Swap ⟨1, by decide⟩),
   opAt 2979 .SUB,
   opAt 2980 (.Dup ⟨3, by decide⟩),
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 .LT,
   opAt 2983 (.Swap ⟨0, by decide⟩),
   opAt 2984 (.Dup ⟨4, by decide⟩),
   opAt 2985 (.Swap ⟨0, by decide⟩),
   opAt 2986 .SUB,
   opAt 2987 (.Dup ⟨3, by decide⟩),
   opAt 2988 .MSTORE,
   opAt 2989 .OR,
   opAt 2990 (.Swap ⟨1, by decide⟩),
   opAt 2991 .POP,
   pushAt 2992 1 31,
   opAt 2993 .NOT,
   opAt 2994 .ADD,
   pushAt 2995 2 8255,
   opAt 2996 (.Dup ⟨1, by decide⟩),
   opAt 2997 .GT,
   pushAt 2998 2 3957,
   opAt 2999 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3000 .POP,
   pushAt 3001 2 8224,
   opAt 3002 .MLOAD,
   opAt 3003 .SUB,
   pushAt 3004 2 8224,
   opAt 3005 .MSTORE,
   pushAt 3006 2 3942,
   opAt 3007 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3008 .JUMPDEST,
   pushAt 3009 2 4021,
   pushAt 3010 2 2048,
   pushAt 3011 2 4804,
   opAt 3012 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3013 .JUMPDEST,
   pushAt 3014 0 0,
   opAt 3015 .NOT,
   opAt 3016 .ADD,
   pushAt 3017 3 3643,
   opAt 3018 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3019 .JUMPDEST,
   opAt 3020 .POP,
   pushAt 3021 2 9344,
   opAt 3022 .MLOAD,
   pushAt 3023 2 5120,
   pushAt 3024 2 4096,
   opAt 3025 .MCOPY,
   pushAt 3026 2 3273,
   opAt 3027 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3437 = true :=
  Artifact.isValidJumpDest_index 2604 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3481 = true :=
  Artifact.isValidJumpDest_index 2631 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3498 = true :=
  Artifact.isValidJumpDest_index 2639 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3505 = true :=
  Artifact.isValidJumpDest_index 2643 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3536 = true :=
  Artifact.isValidJumpDest_index 2667 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3643 = true :=
  Artifact.isValidJumpDest_index 2755 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3759 = true :=
  Artifact.isValidJumpDest_index 2834 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3875 = true :=
  Artifact.isValidJumpDest_index 2907 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3881 = true :=
  Artifact.isValidJumpDest_index 2911 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3942 = true :=
  Artifact.isValidJumpDest_index 2959 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3957 = true :=
  Artifact.isValidJumpDest_index 2968 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4010 = true :=
  Artifact.isValidJumpDest_index 3008 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4021 = true :=
  Artifact.isValidJumpDest_index 3013 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4030 = true :=
  Artifact.isValidJumpDest_index 3019 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast

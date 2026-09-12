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
  [opAt 2605 .JUMPDEST,
   opAt 2606 (.Dup ⟨0, by decide⟩),
   opAt 2607 (.Dup ⟨3, by decide⟩),
   opAt 2608 .EQ,
   pushAt 2609 0 0,
   opAt 2610 .MLOAD,
   pushAt 2611 1 255,
   opAt 2612 .SHR,
   opAt 2613 .AND,
   opAt 2614 .ISZERO,
   pushAt 2615 2 3481,
   opAt 2616 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2617 (.Dup ⟨0, by decide⟩),
   pushAt 2618 1 96,
   pushAt 2619 2 256,
   opAt 2620 .CALLDATACOPY,
   opAt 2621 (.Dup ⟨0, by decide⟩),
   pushAt 2622 1 96,
   pushAt 2623 2 4160,
   opAt 2624 .CALLDATACOPY,
   pushAt 2625 0 0,
   pushAt 2626 2 4128,
   opAt 2627 .MSTORE,
   pushAt 2628 2 3498,
   pushAt 2629 2 512,
   pushAt 2630 2 4804,
   opAt 2631 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2632 .JUMPDEST,
   pushAt 2633 1 1,
   pushAt 2634 2 1024,
   opAt 2635 .MSTORE,
   pushAt 2636 2 1435,
   pushAt 2637 2 1024,
   pushAt 2638 2 2216,
   opAt 2639 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2640 .JUMPDEST,
   pushAt 2641 1 1,
   pushAt 2642 2 5312,
   opAt 2643 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2644 .JUMPDEST,
   opAt 2645 (.Dup ⟨0, by decide⟩),
   opAt 2646 .MLOAD,
   opAt 2647 .NOT,
   opAt 2648 (.Dup ⟨2, by decide⟩),
   opAt 2649 .ADD,
   opAt 2650 (.Dup ⟨2, by decide⟩),
   opAt 2651 (.Dup ⟨1, by decide⟩),
   opAt 2652 .LT,
   opAt 2653 (.Swap ⟨2, by decide⟩),
   opAt 2654 .POP,
   opAt 2655 (.Dup ⟨1, by decide⟩),
   pushAt 2656 2 1280,
   opAt 2657 .ADD,
   opAt 2658 .MSTORE,
   opAt 2659 (.Dup ⟨0, by decide⟩),
   opAt 2660 .ISZERO,
   pushAt 2661 2 3536,
   opAt 2662 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2663 1 31,
   opAt 2664 .NOT,
   opAt 2665 .ADD,
   pushAt 2666 2 3505,
   opAt 2667 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2668 .JUMPDEST,
   opAt 2669 .POP,
   opAt 2670 .POP,
   pushAt 2671 0 0,
   opAt 2672 .MLOAD,
   opAt 2673 (.Dup ⟨0, by decide⟩),
   pushAt 2674 0 0,
   opAt 2675 .SUB,
   opAt 2676 (.Dup ⟨1, by decide⟩),
   opAt 2677 .AND,
   opAt 2678 (.Dup ⟨0, by decide⟩),
   pushAt 2679 2 1536,
   opAt 2680 .MSTORE,
   opAt 2681 (.Dup ⟨0, by decide⟩),
   opAt 2682 (.Dup ⟨2, by decide⟩),
   opAt 2683 .DIV,
   opAt 2684 (.Dup ⟨0, by decide⟩),
   pushAt 2685 2 1568,
   opAt 2686 .MSTORE,
   opAt 2687 (.Dup ⟨1, by decide⟩),
   pushAt 2688 0 0,
   opAt 2689 .SUB,
   opAt 2690 (.Dup ⟨2, by decide⟩),
   opAt 2691 (.Swap ⟨0, by decide⟩),
   opAt 2692 .DIV,
   pushAt 2693 1 1,
   opAt 2694 .ADD,
   pushAt 2695 2 1600,
   opAt 2696 .MSTORE,
   opAt 2697 (.Dup ⟨0, by decide⟩),
   pushAt 2698 0 0,
   opAt 2699 .SUB,
   opAt 2700 (.Dup ⟨1, by decide⟩),
   opAt 2701 (.Swap ⟨0, by decide⟩),
   opAt 2702 .MOD,
   pushAt 2703 2 1632,
   opAt 2704 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2705 (.Dup ⟨0, by decide⟩),
   pushAt 2706 1 2,
   opAt 2707 .SUB,
   opAt 2708 (.Dup ⟨0, by decide⟩),
   opAt 2709 (.Dup ⟨2, by decide⟩),
   opAt 2710 .MUL,
   pushAt 2711 1 2,
   opAt 2712 .SUB,
   opAt 2713 .MUL,
   opAt 2714 (.Dup ⟨0, by decide⟩),
   opAt 2715 (.Dup ⟨2, by decide⟩),
   opAt 2716 .MUL,
   pushAt 2717 1 2,
   opAt 2718 .SUB,
   opAt 2719 .MUL,
   opAt 2720 (.Dup ⟨0, by decide⟩),
   opAt 2721 (.Dup ⟨2, by decide⟩),
   opAt 2722 .MUL,
   pushAt 2723 1 2,
   opAt 2724 .SUB,
   opAt 2725 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2726 (.Dup ⟨0, by decide⟩),
   opAt 2727 (.Dup ⟨2, by decide⟩),
   opAt 2728 .MUL,
   pushAt 2729 1 2,
   opAt 2730 .SUB,
   opAt 2731 .MUL,
   opAt 2732 (.Dup ⟨0, by decide⟩),
   opAt 2733 (.Dup ⟨2, by decide⟩),
   opAt 2734 .MUL,
   pushAt 2735 1 2,
   opAt 2736 .SUB,
   opAt 2737 .MUL,
   opAt 2738 (.Dup ⟨0, by decide⟩),
   opAt 2739 (.Dup ⟨2, by decide⟩),
   opAt 2740 .MUL,
   pushAt 2741 1 2,
   opAt 2742 .SUB,
   opAt 2743 .MUL,
   opAt 2744 (.Dup ⟨0, by decide⟩),
   opAt 2745 (.Dup ⟨2, by decide⟩),
   opAt 2746 .MUL,
   pushAt 2747 1 2,
   opAt 2748 .SUB,
   opAt 2749 .MUL,
   pushAt 2750 2 1664,
   opAt 2751 .MSTORE,
   opAt 2752 .POP,
   opAt 2753 .POP,
   opAt 2754 .POP,
   opAt 2755 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2756 .JUMPDEST,
   opAt 2757 (.Dup ⟨0, by decide⟩),
   opAt 2758 .ISZERO,
   pushAt 2759 2 4030,
   opAt 2760 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2761 (.Dup ⟨1, by decide⟩),
   pushAt 2762 2 512,
   pushAt 2763 2 4128,
   opAt 2764 .MCOPY,
   pushAt 2765 0 0,
   pushAt 2766 2 5344,
   opAt 2767 .MLOAD,
   opAt 2768 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2769 2 512,
   opAt 2770 .MLOAD,
   pushAt 2771 2 1536,
   opAt 2772 .MLOAD,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 .DIV,
   opAt 2776 (.Swap ⟨1, by decide⟩),
   opAt 2777 .MOD,
   pushAt 2778 2 1600,
   opAt 2779 .MLOAD,
   opAt 2780 .MUL,
   pushAt 2781 2 544,
   opAt 2782 .MLOAD,
   pushAt 2783 2 1536,
   opAt 2784 .MLOAD,
   opAt 2785 (.Swap ⟨0, by decide⟩),
   opAt 2786 .DIV,
   opAt 2787 .ADD,
   pushAt 2788 2 1568,
   opAt 2789 .MLOAD,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   pushAt 2791 2 1632,
   opAt 2792 .MLOAD,
   opAt 2793 (.Dup ⟨4, by decide⟩),
   opAt 2794 .MULMOD,
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .ADDMOD,
   opAt 2797 (.Swap ⟨0, by decide⟩),
   opAt 2798 .SUB,
   pushAt 2799 2 1664,
   opAt 2800 .MLOAD,
   opAt 2801 .MUL,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   pushAt 2803 0 0,
   opAt 2804 .MLOAD,
   opAt 2805 .MUL,
   pushAt 2806 2 544,
   opAt 2807 .MLOAD,
   opAt 2808 .SUB,
   pushAt 2809 1 32,
   opAt 2810 .MLOAD,
   pushAt 2811 1 128,
   opAt 2812 .SHR,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   pushAt 2814 1 128,
   opAt 2815 .SHR,
   opAt 2816 .MUL,
   opAt 2817 .GT,
   opAt 2818 (.Swap ⟨0, by decide⟩),
   opAt 2819 .SUB,
   opAt 2820 (.Swap ⟨0, by decide⟩),
   pushAt 2821 2 1568,
   opAt 2822 .MLOAD,
   opAt 2823 .GT,
   opAt 2824 .ISZERO,
   pushAt 2825 0 0,
   opAt 2826 .SUB,
   opAt 2827 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2828 0 0,
   pushAt 2829 2 5344,
   opAt 2830 .MLOAD,
   pushAt 2831 2 5312,
   opAt 2832 .MLOAD,
   pushAt 2833 2 1280,
   opAt 2834 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2835 .JUMPDEST,
   opAt 2836 (.Dup ⟨0, by decide⟩),
   opAt 2837 .MLOAD,
   pushAt 2838 0 0,
   opAt 2839 .NOT,
   opAt 2840 (.Dup ⟨5, by decide⟩),
   opAt 2841 (.Dup ⟨2, by decide⟩),
   opAt 2842 .MUL,
   opAt 2843 (.Swap ⟨1, by decide⟩),
   opAt 2844 (.Dup ⟨6, by decide⟩),
   opAt 2845 .MULMOD,
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 (.Dup ⟨1, by decide⟩),
   opAt 2848 .LT,
   opAt 2849 .SUB,
   opAt 2850 (.Dup ⟨4, by decide⟩),
   opAt 2851 (.Dup ⟨2, by decide⟩),
   opAt 2852 .ADD,
   opAt 2853 (.Dup ⟨0, by decide⟩),
   opAt 2854 (.Swap ⟨5, by decide⟩),
   opAt 2855 .GT,
   opAt 2856 .SUB,
   opAt 2857 .SUB,
   opAt 2858 (.Dup ⟨3, by decide⟩),
   opAt 2859 (.Dup ⟨3, by decide⟩),
   opAt 2860 .MLOAD,
   opAt 2861 .ADD,
   opAt 2862 (.Dup ⟨0, by decide⟩),
   opAt 2863 (.Swap ⟨4, by decide⟩),
   opAt 2864 .GT,
   opAt 2865 .ADD,
   opAt 2866 (.Swap ⟨2, by decide⟩),
   opAt 2867 (.Dup ⟨2, by decide⟩),
   pushAt 2868 1 31,
   opAt 2869 .NOT,
   opAt 2870 .ADD,
   opAt 2871 (.Swap ⟨2, by decide⟩),
   opAt 2872 .MSTORE,
   pushAt 2873 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2874 .ADD,
   pushAt 2875 2 4128,
   opAt 2876 (.Dup ⟨2, by decide⟩),
   opAt 2877 .GT,
   pushAt 2878 2 3759,
   opAt 2879 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2880 .POP,
   opAt 2881 .POP,
   pushAt 2882 2 4128,
   opAt 2883 .MLOAD,
   opAt 2884 (.Dup ⟨1, by decide⟩),
   opAt 2885 .ADD,
   opAt 2886 (.Dup ⟨1, by decide⟩),
   opAt 2887 (.Dup ⟨1, by decide⟩),
   opAt 2888 .LT,
   opAt 2889 (.Swap ⟨1, by decide⟩),
   opAt 2890 .POP,
   opAt 2891 (.Dup ⟨2, by decide⟩),
   opAt 2892 (.Dup ⟨1, by decide⟩),
   opAt 2893 .LT,
   opAt 2894 (.Swap ⟨0, by decide⟩),
   opAt 2895 (.Dup ⟨3, by decide⟩),
   opAt 2896 (.Swap ⟨0, by decide⟩),
   opAt 2897 .SUB,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   pushAt 2899 2 4128,
   opAt 2900 .MSTORE,
   opAt 2901 .POP,
   opAt 2902 .GT,
   opAt 2903 (.Swap ⟨0, by decide⟩),
   opAt 2904 .POP,
   opAt 2905 .ISZERO,
   pushAt 2906 2 3942,
   opAt 2907 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2908 .JUMPDEST,
   pushAt 2909 0 0,
   pushAt 2910 2 5344,
   opAt 2911 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2912 .JUMPDEST,
   opAt 2913 (.Dup ⟨0, by decide⟩),
   opAt 2914 .MLOAD,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   pushAt 2916 2 4160,
   opAt 2917 (.Swap ⟨0, by decide⟩),
   opAt 2918 .SUB,
   opAt 2919 .MLOAD,
   opAt 2920 (.Dup ⟨1, by decide⟩),
   opAt 2921 .ADD,
   opAt 2922 (.Dup ⟨0, by decide⟩),
   opAt 2923 (.Dup ⟨2, by decide⟩),
   opAt 2924 .GT,
   opAt 2925 (.Swap ⟨1, by decide⟩),
   opAt 2926 .POP,
   opAt 2927 (.Dup ⟨3, by decide⟩),
   opAt 2928 .ADD,
   opAt 2929 (.Dup ⟨0, by decide⟩),
   opAt 2930 (.Dup ⟨4, by decide⟩),
   opAt 2931 .GT,
   opAt 2932 (.Swap ⟨3, by decide⟩),
   opAt 2933 .POP,
   opAt 2934 (.Dup ⟨2, by decide⟩),
   opAt 2935 .MSTORE,
   opAt 2936 (.Swap ⟨0, by decide⟩),
   opAt 2937 (.Swap ⟨1, by decide⟩),
   opAt 2938 .OR,
   opAt 2939 (.Swap ⟨0, by decide⟩),
   pushAt 2940 1 31,
   opAt 2941 .NOT,
   opAt 2942 .ADD,
   pushAt 2943 2 4159,
   opAt 2944 (.Dup ⟨1, by decide⟩),
   opAt 2945 .GT,
   pushAt 2946 2 3881,
   opAt 2947 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2948 .POP,
   pushAt 2949 2 4128,
   opAt 2950 .MLOAD,
   opAt 2951 (.Dup ⟨1, by decide⟩),
   opAt 2952 .ADD,
   opAt 2953 (.Dup ⟨0, by decide⟩),
   pushAt 2954 2 4128,
   opAt 2955 .MSTORE,
   opAt 2956 .LT,
   opAt 2957 .ISZERO,
   pushAt 2958 2 3875,
   opAt 2959 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2960 .JUMPDEST,
   pushAt 2961 2 4128,
   opAt 2962 .MLOAD,
   opAt 2963 .ISZERO,
   pushAt 2964 2 4010,
   opAt 2965 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2966 0 0,
   pushAt 2967 2 5344,
   opAt 2968 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2969 .JUMPDEST,
   opAt 2970 (.Dup ⟨0, by decide⟩),
   opAt 2971 .MLOAD,
   pushAt 2972 2 4160,
   opAt 2973 (.Dup ⟨2, by decide⟩),
   opAt 2974 .SUB,
   opAt 2975 .MLOAD,
   opAt 2976 (.Dup ⟨1, by decide⟩),
   opAt 2977 (.Dup ⟨1, by decide⟩),
   opAt 2978 .GT,
   opAt 2979 (.Swap ⟨1, by decide⟩),
   opAt 2980 .SUB,
   opAt 2981 (.Dup ⟨3, by decide⟩),
   opAt 2982 (.Dup ⟨1, by decide⟩),
   opAt 2983 .LT,
   opAt 2984 (.Swap ⟨0, by decide⟩),
   opAt 2985 (.Dup ⟨4, by decide⟩),
   opAt 2986 (.Swap ⟨0, by decide⟩),
   opAt 2987 .SUB,
   opAt 2988 (.Dup ⟨3, by decide⟩),
   opAt 2989 .MSTORE,
   opAt 2990 .OR,
   opAt 2991 (.Swap ⟨1, by decide⟩),
   opAt 2992 .POP,
   pushAt 2993 1 31,
   opAt 2994 .NOT,
   opAt 2995 .ADD,
   pushAt 2996 2 4159,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .GT,
   pushAt 2999 2 3957,
   opAt 3000 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3001 .POP,
   pushAt 3002 2 4128,
   opAt 3003 .MLOAD,
   opAt 3004 .SUB,
   pushAt 3005 2 4128,
   opAt 3006 .MSTORE,
   pushAt 3007 2 3942,
   opAt 3008 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3009 .JUMPDEST,
   pushAt 3010 2 4021,
   pushAt 3011 2 512,
   pushAt 3012 2 4804,
   opAt 3013 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3014 .JUMPDEST,
   pushAt 3015 0 0,
   opAt 3016 .NOT,
   opAt 3017 .ADD,
   pushAt 3018 3 3643,
   opAt 3019 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3020 .JUMPDEST,
   opAt 3021 .POP,
   pushAt 3022 2 5248,
   opAt 3023 .MLOAD,
   pushAt 3024 2 1280,
   pushAt 3025 2 1024,
   opAt 3026 .MCOPY,
   pushAt 3027 2 3273,
   opAt 3028 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3437 = true :=
  Artifact.isValidJumpDest_index 2605 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3481 = true :=
  Artifact.isValidJumpDest_index 2632 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3498 = true :=
  Artifact.isValidJumpDest_index 2640 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3505 = true :=
  Artifact.isValidJumpDest_index 2644 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3536 = true :=
  Artifact.isValidJumpDest_index 2668 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3643 = true :=
  Artifact.isValidJumpDest_index 2756 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3759 = true :=
  Artifact.isValidJumpDest_index 2835 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3875 = true :=
  Artifact.isValidJumpDest_index 2908 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3881 = true :=
  Artifact.isValidJumpDest_index 2912 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3942 = true :=
  Artifact.isValidJumpDest_index 2960 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3957 = true :=
  Artifact.isValidJumpDest_index 2969 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4010 = true :=
  Artifact.isValidJumpDest_index 3009 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4021 = true :=
  Artifact.isValidJumpDest_index 3014 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4030 = true :=
  Artifact.isValidJumpDest_index 3020 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast

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
  [opAt 2580 .JUMPDEST,
   opAt 2581 (.Dup ⟨0, by decide⟩),
   opAt 2582 (.Dup ⟨3, by decide⟩),
   opAt 2583 .EQ,
   pushAt 2584 0 0,
   opAt 2585 .MLOAD,
   pushAt 2586 1 255,
   opAt 2587 .SHR,
   opAt 2588 .AND,
   opAt 2589 .ISZERO,
   pushAt 2590 2 3481,
   opAt 2591 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2592 (.Dup ⟨0, by decide⟩),
   pushAt 2593 1 96,
   pushAt 2594 2 256,
   opAt 2595 .CALLDATACOPY,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   pushAt 2597 1 96,
   pushAt 2598 2 4160,
   opAt 2599 .CALLDATACOPY,
   pushAt 2600 0 0,
   pushAt 2601 2 4128,
   opAt 2602 .MSTORE,
   pushAt 2603 2 3498,
   pushAt 2604 2 512,
   pushAt 2605 2 4804,
   opAt 2606 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2607 .JUMPDEST,
   pushAt 2608 1 1,
   pushAt 2609 2 1024,
   opAt 2610 .MSTORE,
   pushAt 2611 2 1435,
   pushAt 2612 2 1024,
   pushAt 2613 2 2216,
   opAt 2614 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2615 .JUMPDEST,
   pushAt 2616 1 1,
   pushAt 2617 2 5312,
   opAt 2618 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2619 .JUMPDEST,
   opAt 2620 (.Dup ⟨0, by decide⟩),
   opAt 2621 .MLOAD,
   opAt 2622 .NOT,
   opAt 2623 (.Dup ⟨2, by decide⟩),
   opAt 2624 .ADD,
   opAt 2625 (.Dup ⟨2, by decide⟩),
   opAt 2626 (.Dup ⟨1, by decide⟩),
   opAt 2627 .LT,
   opAt 2628 (.Swap ⟨2, by decide⟩),
   opAt 2629 .POP,
   opAt 2630 (.Dup ⟨1, by decide⟩),
   pushAt 2631 2 1280,
   opAt 2632 .ADD,
   opAt 2633 .MSTORE,
   opAt 2634 (.Dup ⟨0, by decide⟩),
   opAt 2635 .ISZERO,
   pushAt 2636 2 3536,
   opAt 2637 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2638 1 31,
   opAt 2639 .NOT,
   opAt 2640 .ADD,
   pushAt 2641 2 3505,
   opAt 2642 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2643 .JUMPDEST,
   opAt 2644 .POP,
   opAt 2645 .POP,
   pushAt 2646 0 0,
   opAt 2647 .MLOAD,
   opAt 2648 (.Dup ⟨0, by decide⟩),
   pushAt 2649 0 0,
   opAt 2650 .SUB,
   opAt 2651 (.Dup ⟨1, by decide⟩),
   opAt 2652 .AND,
   opAt 2653 (.Dup ⟨0, by decide⟩),
   pushAt 2654 2 1536,
   opAt 2655 .MSTORE,
   opAt 2656 (.Dup ⟨0, by decide⟩),
   opAt 2657 (.Dup ⟨2, by decide⟩),
   opAt 2658 .DIV,
   opAt 2659 (.Dup ⟨0, by decide⟩),
   pushAt 2660 2 1568,
   opAt 2661 .MSTORE,
   opAt 2662 (.Dup ⟨1, by decide⟩),
   pushAt 2663 0 0,
   opAt 2664 .SUB,
   opAt 2665 (.Dup ⟨2, by decide⟩),
   opAt 2666 (.Swap ⟨0, by decide⟩),
   opAt 2667 .DIV,
   pushAt 2668 1 1,
   opAt 2669 .ADD,
   pushAt 2670 2 1600,
   opAt 2671 .MSTORE,
   opAt 2672 (.Dup ⟨0, by decide⟩),
   pushAt 2673 0 0,
   opAt 2674 .SUB,
   opAt 2675 (.Dup ⟨1, by decide⟩),
   opAt 2676 (.Swap ⟨0, by decide⟩),
   opAt 2677 .MOD,
   pushAt 2678 2 1632,
   opAt 2679 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2680 (.Dup ⟨0, by decide⟩),
   pushAt 2681 1 2,
   opAt 2682 .SUB,
   opAt 2683 (.Dup ⟨0, by decide⟩),
   opAt 2684 (.Dup ⟨2, by decide⟩),
   opAt 2685 .MUL,
   pushAt 2686 1 2,
   opAt 2687 .SUB,
   opAt 2688 .MUL,
   opAt 2689 (.Dup ⟨0, by decide⟩),
   opAt 2690 (.Dup ⟨2, by decide⟩),
   opAt 2691 .MUL,
   pushAt 2692 1 2,
   opAt 2693 .SUB,
   opAt 2694 .MUL,
   opAt 2695 (.Dup ⟨0, by decide⟩),
   opAt 2696 (.Dup ⟨2, by decide⟩),
   opAt 2697 .MUL,
   pushAt 2698 1 2,
   opAt 2699 .SUB,
   opAt 2700 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2701 (.Dup ⟨0, by decide⟩),
   opAt 2702 (.Dup ⟨2, by decide⟩),
   opAt 2703 .MUL,
   pushAt 2704 1 2,
   opAt 2705 .SUB,
   opAt 2706 .MUL,
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
   opAt 2724 .MUL,
   pushAt 2725 2 1664,
   opAt 2726 .MSTORE,
   opAt 2727 .POP,
   opAt 2728 .POP,
   opAt 2729 .POP,
   opAt 2730 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2731 .JUMPDEST,
   opAt 2732 (.Dup ⟨0, by decide⟩),
   opAt 2733 .ISZERO,
   pushAt 2734 2 4030,
   opAt 2735 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2736 (.Dup ⟨1, by decide⟩),
   pushAt 2737 2 512,
   pushAt 2738 2 4128,
   opAt 2739 .MCOPY,
   pushAt 2740 0 0,
   pushAt 2741 2 5344,
   opAt 2742 .MLOAD,
   opAt 2743 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2744 2 512,
   opAt 2745 .MLOAD,
   pushAt 2746 2 1536,
   opAt 2747 .MLOAD,
   opAt 2748 (.Dup ⟨0, by decide⟩),
   opAt 2749 (.Dup ⟨2, by decide⟩),
   opAt 2750 .DIV,
   opAt 2751 (.Swap ⟨1, by decide⟩),
   opAt 2752 .MOD,
   pushAt 2753 2 1600,
   opAt 2754 .MLOAD,
   opAt 2755 .MUL,
   pushAt 2756 2 544,
   opAt 2757 .MLOAD,
   pushAt 2758 2 1536,
   opAt 2759 .MLOAD,
   opAt 2760 (.Swap ⟨0, by decide⟩),
   opAt 2761 .DIV,
   opAt 2762 .ADD,
   pushAt 2763 2 1568,
   opAt 2764 .MLOAD,
   opAt 2765 (.Dup ⟨0, by decide⟩),
   pushAt 2766 2 1632,
   opAt 2767 .MLOAD,
   opAt 2768 (.Dup ⟨4, by decide⟩),
   opAt 2769 .MULMOD,
   opAt 2770 (.Dup ⟨2, by decide⟩),
   opAt 2771 .ADDMOD,
   opAt 2772 (.Swap ⟨0, by decide⟩),
   opAt 2773 .SUB,
   pushAt 2774 2 1664,
   opAt 2775 .MLOAD,
   opAt 2776 .MUL,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   pushAt 2778 0 0,
   opAt 2779 .MLOAD,
   opAt 2780 .MUL,
   pushAt 2781 2 544,
   opAt 2782 .MLOAD,
   opAt 2783 .SUB,
   pushAt 2784 1 32,
   opAt 2785 .MLOAD,
   pushAt 2786 1 128,
   opAt 2787 .SHR,
   opAt 2788 (.Dup ⟨2, by decide⟩),
   pushAt 2789 1 128,
   opAt 2790 .SHR,
   opAt 2791 .MUL,
   opAt 2792 .GT,
   opAt 2793 (.Swap ⟨0, by decide⟩),
   opAt 2794 .SUB,
   opAt 2795 (.Swap ⟨0, by decide⟩),
   pushAt 2796 2 1568,
   opAt 2797 .MLOAD,
   opAt 2798 .GT,
   opAt 2799 .ISZERO,
   pushAt 2800 0 0,
   opAt 2801 .SUB,
   opAt 2802 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2803 0 0,
   pushAt 2804 1 31,
   opAt 2805 .NOT,
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
   opAt 2817 (.Dup ⟨6, by decide⟩),
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .MUL,
   opAt 2820 (.Swap ⟨1, by decide⟩),
   opAt 2821 (.Dup ⟨7, by decide⟩),
   opAt 2822 .MULMOD,
   opAt 2823 (.Dup ⟨1, by decide⟩),
   opAt 2824 (.Dup ⟨1, by decide⟩),
   opAt 2825 .LT,
   opAt 2826 .SUB,
   opAt 2827 (.Dup ⟨5, by decide⟩),
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 .ADD,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Swap ⟨6, by decide⟩),
   opAt 2832 .GT,
   opAt 2833 .SUB,
   opAt 2834 .SUB,
   opAt 2835 (.Dup ⟨4, by decide⟩),
   opAt 2836 (.Dup ⟨3, by decide⟩),
   opAt 2837 .MLOAD,
   opAt 2838 .ADD,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Swap ⟨5, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 .ADD,
   opAt 2843 (.Swap ⟨3, by decide⟩),
   opAt 2844 (.Dup ⟨2, by decide⟩),
   opAt 2845 (.Dup ⟨4, by decide⟩),
   opAt 2846 .ADD,
   opAt 2847 (.Swap ⟨2, by decide⟩),
   opAt 2848 .MSTORE,
   opAt 2849 (.Dup ⟨2, by decide⟩),
   opAt 2850 .ADD,
   pushAt 2851 32 4128,
   opAt 2852 (.Dup ⟨2, by decide⟩),
   opAt 2853 .GT,
   pushAt 2854 2 3762,
   opAt 2855 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2856 .POP,
   opAt 2857 .POP,
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
  Artifact.isValidJumpDest_index 2580 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3481 = true :=
  Artifact.isValidJumpDest_index 2607 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3498 = true :=
  Artifact.isValidJumpDest_index 2615 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3505 = true :=
  Artifact.isValidJumpDest_index 2619 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3536 = true :=
  Artifact.isValidJumpDest_index 2643 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3643 = true :=
  Artifact.isValidJumpDest_index 2731 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3762 = true :=
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

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
   pushAt 2607 2 4824,
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
   pushAt 2736 2 4050,
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
  [pushAt 2805 1 31,
   opAt 2806 .NOT,
   opAt 2807 (.Swap ⟨0, by decide⟩),
   pushAt 2808 0 0,
   pushAt 2809 2 5344,
   opAt 2810 .MLOAD,
   pushAt 2811 2 5312,
   opAt 2812 .MLOAD,
   pushAt 2813 2 1280,
   opAt 2814 .ADD,
   opAt 2815 (.Dup ⟨0, by decide⟩),
   pushAt 2816 1 32,
   opAt 2817 .AND,
   opAt 2818 .ISZERO,
   pushAt 2819 2 3811,
   opAt 2820 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def mac2PathA : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2821 .JUMPDEST,
   opAt 2822 (.Dup ⟨0, by decide⟩),
   opAt 2823 .MLOAD,
   pushAt 2824 0 0,
   opAt 2825 .NOT,
   opAt 2826 (.Dup ⟨5, by decide⟩),
   opAt 2827 (.Dup ⟨2, by decide⟩),
   opAt 2828 .MUL,
   opAt 2829 (.Swap ⟨1, by decide⟩),
   opAt 2830 (.Dup ⟨6, by decide⟩),
   opAt 2831 .MULMOD,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   opAt 2833 (.Dup ⟨1, by decide⟩),
   opAt 2834 .LT,
   opAt 2835 .SUB,
   opAt 2836 (.Dup ⟨4, by decide⟩),
   opAt 2837 (.Dup ⟨2, by decide⟩),
   opAt 2838 .ADD,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Swap ⟨5, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 .SUB,
   opAt 2843 .SUB,
   opAt 2844 (.Dup ⟨3, by decide⟩),
   opAt 2845 (.Dup ⟨3, by decide⟩),
   opAt 2846 .MLOAD,
   opAt 2847 .ADD,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   opAt 2849 (.Swap ⟨4, by decide⟩),
   opAt 2850 .GT,
   opAt 2851 .ADD,
   opAt 2852 (.Swap ⟨2, by decide⟩),
   opAt 2853 (.Dup ⟨2, by decide⟩),
   opAt 2854 (.Dup ⟨6, by decide⟩),
   opAt 2855 .ADD,
   opAt 2856 (.Swap ⟨2, by decide⟩),
   opAt 2857 .MSTORE,
   opAt 2858 (.Dup ⟨4, by decide⟩),
   opAt 2859 .ADD]
def mac2PathB : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2860 .JUMPDEST,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 .MLOAD,
   pushAt 2863 0 0,
   opAt 2864 .NOT,
   opAt 2865 (.Dup ⟨5, by decide⟩),
   opAt 2866 (.Dup ⟨2, by decide⟩),
   opAt 2867 .MUL,
   opAt 2868 (.Swap ⟨1, by decide⟩),
   opAt 2869 (.Dup ⟨6, by decide⟩),
   opAt 2870 .MULMOD,
   opAt 2871 (.Dup ⟨1, by decide⟩),
   opAt 2872 (.Dup ⟨1, by decide⟩),
   opAt 2873 .LT,
   opAt 2874 .SUB,
   opAt 2875 (.Dup ⟨4, by decide⟩),
   opAt 2876 (.Dup ⟨2, by decide⟩),
   opAt 2877 .ADD,
   opAt 2878 (.Dup ⟨0, by decide⟩),
   opAt 2879 (.Swap ⟨5, by decide⟩),
   opAt 2880 .GT,
   opAt 2881 .SUB,
   opAt 2882 .SUB,
   opAt 2883 (.Dup ⟨3, by decide⟩),
   opAt 2884 (.Dup ⟨3, by decide⟩),
   opAt 2885 .MLOAD,
   opAt 2886 .ADD,
   opAt 2887 (.Dup ⟨0, by decide⟩),
   opAt 2888 (.Swap ⟨4, by decide⟩),
   opAt 2889 .GT,
   opAt 2890 .ADD,
   opAt 2891 (.Swap ⟨2, by decide⟩),
   opAt 2892 (.Dup ⟨2, by decide⟩),
   opAt 2893 (.Dup ⟨6, by decide⟩),
   opAt 2894 .ADD,
   opAt 2895 (.Swap ⟨2, by decide⟩),
   opAt 2896 .MSTORE,
   opAt 2897 (.Dup ⟨4, by decide⟩),
   opAt 2898 .ADD]
def mac2PathTail : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2899 2 4128,
   opAt 2900 (.Dup ⟨2, by decide⟩),
   opAt 2901 .GT,
   pushAt 2902 2 3772,
   opAt 2903 .JUMPI]
def blk3077 := mac2PathA ++ mac2PathB ++ mac2PathTail

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2904 .POP,
   opAt 2905 .POP,
   pushAt 2906 2 4128,
   opAt 2907 .MLOAD,
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 .ADD,
   opAt 2910 (.Dup ⟨1, by decide⟩),
   opAt 2911 (.Dup ⟨1, by decide⟩),
   opAt 2912 .LT,
   opAt 2913 (.Swap ⟨1, by decide⟩),
   opAt 2914 .POP,
   opAt 2915 (.Dup ⟨2, by decide⟩),
   opAt 2916 (.Dup ⟨1, by decide⟩),
   opAt 2917 .LT,
   opAt 2918 (.Swap ⟨0, by decide⟩),
   opAt 2919 (.Dup ⟨3, by decide⟩),
   opAt 2920 (.Swap ⟨0, by decide⟩),
   opAt 2921 .SUB,
   opAt 2922 (.Dup ⟨0, by decide⟩),
   pushAt 2923 2 4128,
   opAt 2924 .MSTORE,
   opAt 2925 .POP,
   opAt 2926 .GT,
   opAt 2927 (.Swap ⟨0, by decide⟩),
   opAt 2928 .POP,
   opAt 2929 (.Swap ⟨0, by decide⟩),
   opAt 2930 .POP,
   opAt 2931 .ISZERO,
   pushAt 2932 2 3962,
   opAt 2933 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2934 .JUMPDEST,
   pushAt 2935 0 0,
   pushAt 2936 2 5344,
   opAt 2937 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2938 .JUMPDEST,
   opAt 2939 (.Dup ⟨0, by decide⟩),
   opAt 2940 .MLOAD,
   opAt 2941 (.Dup ⟨1, by decide⟩),
   pushAt 2942 2 4160,
   opAt 2943 (.Swap ⟨0, by decide⟩),
   opAt 2944 .SUB,
   opAt 2945 .MLOAD,
   opAt 2946 (.Dup ⟨1, by decide⟩),
   opAt 2947 .ADD,
   opAt 2948 (.Dup ⟨0, by decide⟩),
   opAt 2949 (.Dup ⟨2, by decide⟩),
   opAt 2950 .GT,
   opAt 2951 (.Swap ⟨1, by decide⟩),
   opAt 2952 .POP,
   opAt 2953 (.Dup ⟨3, by decide⟩),
   opAt 2954 .ADD,
   opAt 2955 (.Dup ⟨0, by decide⟩),
   opAt 2956 (.Dup ⟨4, by decide⟩),
   opAt 2957 .GT,
   opAt 2958 (.Swap ⟨3, by decide⟩),
   opAt 2959 .POP,
   opAt 2960 (.Dup ⟨2, by decide⟩),
   opAt 2961 .MSTORE,
   opAt 2962 (.Swap ⟨0, by decide⟩),
   opAt 2963 (.Swap ⟨1, by decide⟩),
   opAt 2964 .OR,
   opAt 2965 (.Swap ⟨0, by decide⟩),
   pushAt 2966 1 31,
   opAt 2967 .NOT,
   opAt 2968 .ADD,
   pushAt 2969 2 4159,
   opAt 2970 (.Dup ⟨1, by decide⟩),
   opAt 2971 .GT,
   pushAt 2972 2 3901,
   opAt 2973 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2974 .POP,
   pushAt 2975 2 4128,
   opAt 2976 .MLOAD,
   opAt 2977 (.Dup ⟨1, by decide⟩),
   opAt 2978 .ADD,
   opAt 2979 (.Dup ⟨0, by decide⟩),
   pushAt 2980 2 4128,
   opAt 2981 .MSTORE,
   opAt 2982 .LT,
   opAt 2983 .ISZERO,
   pushAt 2984 2 3895,
   opAt 2985 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2986 .JUMPDEST,
   pushAt 2987 2 4128,
   opAt 2988 .MLOAD,
   opAt 2989 .ISZERO,
   pushAt 2990 2 4030,
   opAt 2991 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2992 0 0,
   pushAt 2993 2 5344,
   opAt 2994 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2995 .JUMPDEST,
   opAt 2996 (.Dup ⟨0, by decide⟩),
   opAt 2997 .MLOAD,
   pushAt 2998 2 4160,
   opAt 2999 (.Dup ⟨2, by decide⟩),
   opAt 3000 .SUB,
   opAt 3001 .MLOAD,
   opAt 3002 (.Dup ⟨1, by decide⟩),
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .GT,
   opAt 3005 (.Swap ⟨1, by decide⟩),
   opAt 3006 .SUB,
   opAt 3007 (.Dup ⟨3, by decide⟩),
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 .LT,
   opAt 3010 (.Swap ⟨0, by decide⟩),
   opAt 3011 (.Dup ⟨4, by decide⟩),
   opAt 3012 (.Swap ⟨0, by decide⟩),
   opAt 3013 .SUB,
   opAt 3014 (.Dup ⟨3, by decide⟩),
   opAt 3015 .MSTORE,
   opAt 3016 .OR,
   opAt 3017 (.Swap ⟨1, by decide⟩),
   opAt 3018 .POP,
   pushAt 3019 1 31,
   opAt 3020 .NOT,
   opAt 3021 .ADD,
   pushAt 3022 2 4159,
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 .GT,
   pushAt 3025 2 3977,
   opAt 3026 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3027 .POP,
   pushAt 3028 2 4128,
   opAt 3029 .MLOAD,
   opAt 3030 .SUB,
   pushAt 3031 2 4128,
   opAt 3032 .MSTORE,
   pushAt 3033 2 3962,
   opAt 3034 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3035 .JUMPDEST,
   pushAt 3036 2 4041,
   pushAt 3037 2 512,
   pushAt 3038 2 4824,
   opAt 3039 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3040 .JUMPDEST,
   pushAt 3041 0 0,
   opAt 3042 .NOT,
   opAt 3043 .ADD,
   pushAt 3044 3 3643,
   opAt 3045 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3046 .JUMPDEST,
   opAt 3047 .POP,
   pushAt 3048 2 5248,
   opAt 3049 .MLOAD,
   pushAt 3050 2 1280,
   pushAt 3051 2 1024,
   opAt 3052 .MCOPY,
   pushAt 3053 2 3273,
   opAt 3054 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3772 = true :=
  Artifact.isValidJumpDest_index 2821 (by rfl)

theorem jumpDestMacB :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3811 = true :=
  Artifact.isValidJumpDest_index 2860 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3895 = true :=
  Artifact.isValidJumpDest_index 2934 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3901 = true :=
  Artifact.isValidJumpDest_index 2938 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3962 = true :=
  Artifact.isValidJumpDest_index 2986 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3977 = true :=
  Artifact.isValidJumpDest_index 2995 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4030 = true :=
  Artifact.isValidJumpDest_index 3035 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4041 = true :=
  Artifact.isValidJumpDest_index 3040 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4050 = true :=
  Artifact.isValidJumpDest_index 3046 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast

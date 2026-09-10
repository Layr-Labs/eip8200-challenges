import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the appended shift-reduce blocks

Instruction indices 2862 .. 3523, one lemma each.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open EvmSemantics.EVM

private theorem pc_succ (p : Challenge.EvmProof.ProgramArtifact) (i : Nat) (instr : Instr)
    (hget : p.instructions[i]? = some instr) :
    p.instructionPC (i+1) = p.instructionPC i + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

@[simp] theorem pc2862 : Artifact.submissionArtifact.instructionPC 2756 = 3816 := by rfl

@[simp] theorem pc2863 : Artifact.submissionArtifact.instructionPC 2757 = 3817 := by
  change Artifact.submissionArtifact.instructionPC (2756+1) = 3817
  rw [pc_succ Artifact.submissionArtifact 2756 (.op .JUMPDEST) (by rfl), pc2862]
  rfl

@[simp] theorem pc2864 : Artifact.submissionArtifact.instructionPC 2758 = 3818 := by
  change Artifact.submissionArtifact.instructionPC (2757+1) = 3818
  rw [pc_succ Artifact.submissionArtifact 2757 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2863]
  rfl

@[simp] theorem pc2865 : Artifact.submissionArtifact.instructionPC 2759 = 3819 := by
  change Artifact.submissionArtifact.instructionPC (2758+1) = 3819
  rw [pc_succ Artifact.submissionArtifact 2758 (.op (.Dup ⟨3, by decide⟩)) (by rfl), pc2864]
  rfl

@[simp] theorem pc2866 : Artifact.submissionArtifact.instructionPC 2760 = 3820 := by
  change Artifact.submissionArtifact.instructionPC (2759+1) = 3820
  rw [pc_succ Artifact.submissionArtifact 2759 (.op .EQ) (by rfl), pc2865]
  rfl

@[simp] theorem pc2867 : Artifact.submissionArtifact.instructionPC 2761 = 3821 := by
  change Artifact.submissionArtifact.instructionPC (2760+1) = 3821
  rw [pc_succ Artifact.submissionArtifact 2760 (.push 0 0) (by rfl), pc2866]
  rfl

@[simp] theorem pc2868 : Artifact.submissionArtifact.instructionPC 2762 = 3822 := by
  change Artifact.submissionArtifact.instructionPC (2761+1) = 3822
  rw [pc_succ Artifact.submissionArtifact 2761 (.op .MLOAD) (by rfl), pc2867]
  rfl

@[simp] theorem pc2869 : Artifact.submissionArtifact.instructionPC 2763 = 3824 := by
  change Artifact.submissionArtifact.instructionPC (2762+1) = 3824
  rw [pc_succ Artifact.submissionArtifact 2762 (.push 1 255) (by rfl), pc2868]
  rfl

@[simp] theorem pc2870 : Artifact.submissionArtifact.instructionPC 2764 = 3825 := by
  change Artifact.submissionArtifact.instructionPC (2763+1) = 3825
  rw [pc_succ Artifact.submissionArtifact 2763 (.op .SHR) (by rfl), pc2869]
  rfl

@[simp] theorem pc2871 : Artifact.submissionArtifact.instructionPC 2765 = 3826 := by
  change Artifact.submissionArtifact.instructionPC (2764+1) = 3826
  rw [pc_succ Artifact.submissionArtifact 2764 (.op .AND) (by rfl), pc2870]
  rfl

@[simp] theorem pc2872 : Artifact.submissionArtifact.instructionPC 2766 = 3827 := by
  change Artifact.submissionArtifact.instructionPC (2765+1) = 3827
  rw [pc_succ Artifact.submissionArtifact 2765 (.op .ISZERO) (by rfl), pc2871]
  rfl

@[simp] theorem pc2873 : Artifact.submissionArtifact.instructionPC 2767 = 3830 := by
  change Artifact.submissionArtifact.instructionPC (2766+1) = 3830
  rw [pc_succ Artifact.submissionArtifact 2766 (.push 2 3860) (by rfl), pc2872]
  rfl

@[simp] theorem pc2874 : Artifact.submissionArtifact.instructionPC 2768 = 3831 := by
  change Artifact.submissionArtifact.instructionPC (2767+1) = 3831
  rw [pc_succ Artifact.submissionArtifact 2767 (.op .JUMPI) (by rfl), pc2873]
  rfl

@[simp] theorem pc2875 : Artifact.submissionArtifact.instructionPC 2769 = 3832 := by
  change Artifact.submissionArtifact.instructionPC (2768+1) = 3832
  rw [pc_succ Artifact.submissionArtifact 2768 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2874]
  rfl

@[simp] theorem pc2876 : Artifact.submissionArtifact.instructionPC 2770 = 3834 := by
  change Artifact.submissionArtifact.instructionPC (2769+1) = 3834
  rw [pc_succ Artifact.submissionArtifact 2769 (.push 1 96) (by rfl), pc2875]
  rfl

@[simp] theorem pc2877 : Artifact.submissionArtifact.instructionPC 2771 = 3837 := by
  change Artifact.submissionArtifact.instructionPC (2770+1) = 3837
  rw [pc_succ Artifact.submissionArtifact 2770 (.push 2 1024) (by rfl), pc2876]
  rfl

@[simp] theorem pc2878 : Artifact.submissionArtifact.instructionPC 2772 = 3838 := by
  change Artifact.submissionArtifact.instructionPC (2771+1) = 3838
  rw [pc_succ Artifact.submissionArtifact 2771 (.op .CALLDATACOPY) (by rfl), pc2877]
  rfl

@[simp] theorem pc2879 : Artifact.submissionArtifact.instructionPC 2773 = 3839 := by
  change Artifact.submissionArtifact.instructionPC (2772+1) = 3839
  rw [pc_succ Artifact.submissionArtifact 2772 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2878]
  rfl

@[simp] theorem pc2880 : Artifact.submissionArtifact.instructionPC 2774 = 3841 := by
  change Artifact.submissionArtifact.instructionPC (2773+1) = 3841
  rw [pc_succ Artifact.submissionArtifact 2773 (.push 1 96) (by rfl), pc2879]
  rfl

@[simp] theorem pc2881 : Artifact.submissionArtifact.instructionPC 2775 = 3844 := by
  change Artifact.submissionArtifact.instructionPC (2774+1) = 3844
  rw [pc_succ Artifact.submissionArtifact 2774 (.push 2 8256) (by rfl), pc2880]
  rfl

@[simp] theorem pc2882 : Artifact.submissionArtifact.instructionPC 2776 = 3845 := by
  change Artifact.submissionArtifact.instructionPC (2775+1) = 3845
  rw [pc_succ Artifact.submissionArtifact 2775 (.op .CALLDATACOPY) (by rfl), pc2881]
  rfl

@[simp] theorem pc2883 : Artifact.submissionArtifact.instructionPC 2777 = 3846 := by
  change Artifact.submissionArtifact.instructionPC (2776+1) = 3846
  rw [pc_succ Artifact.submissionArtifact 2776 (.push 0 0) (by rfl), pc2882]
  rfl

@[simp] theorem pc2884 : Artifact.submissionArtifact.instructionPC 2778 = 3849 := by
  change Artifact.submissionArtifact.instructionPC (2777+1) = 3849
  rw [pc_succ Artifact.submissionArtifact 2777 (.push 2 8224) (by rfl), pc2883]
  rfl

@[simp] theorem pc2885 : Artifact.submissionArtifact.instructionPC 2779 = 3850 := by
  change Artifact.submissionArtifact.instructionPC (2778+1) = 3850
  rw [pc_succ Artifact.submissionArtifact 2778 (.op .MSTORE) (by rfl), pc2884]
  rfl

@[simp] theorem pc2886 : Artifact.submissionArtifact.instructionPC 2780 = 3853 := by
  change Artifact.submissionArtifact.instructionPC (2779+1) = 3853
  rw [pc_succ Artifact.submissionArtifact 2779 (.push 2 3865) (by rfl), pc2885]
  rfl

@[simp] theorem pc2887 : Artifact.submissionArtifact.instructionPC 2781 = 3856 := by
  change Artifact.submissionArtifact.instructionPC (2780+1) = 3856
  rw [pc_succ Artifact.submissionArtifact 2780 (.push 2 2048) (by rfl), pc2886]
  rfl

@[simp] theorem pc2888 : Artifact.submissionArtifact.instructionPC 2782 = 3859 := by
  change Artifact.submissionArtifact.instructionPC (2781+1) = 3859
  rw [pc_succ Artifact.submissionArtifact 2781 (.push 2 2304) (by rfl), pc2887]
  rfl

@[simp] theorem pc2889 : Artifact.submissionArtifact.instructionPC 2783 = 3860 := by
  change Artifact.submissionArtifact.instructionPC (2782+1) = 3860
  rw [pc_succ Artifact.submissionArtifact 2782 (.op .JUMP) (by rfl), pc2888]
  rfl

@[simp] theorem pc2890 : Artifact.submissionArtifact.instructionPC 2784 = 3861 := by
  change Artifact.submissionArtifact.instructionPC (2783+1) = 3861
  rw [pc_succ Artifact.submissionArtifact 2783 (.op .JUMPDEST) (by rfl), pc2889]
  rfl

@[simp] theorem pc2891 : Artifact.submissionArtifact.instructionPC 2785 = 3864 := by
  change Artifact.submissionArtifact.instructionPC (2784+1) = 3864
  rw [pc_succ Artifact.submissionArtifact 2784 (.push 2 1533) (by rfl), pc2890]
  rfl

@[simp] theorem pc2892 : Artifact.submissionArtifact.instructionPC 2786 = 3865 := by
  change Artifact.submissionArtifact.instructionPC (2785+1) = 3865
  rw [pc_succ Artifact.submissionArtifact 2785 (.op .JUMP) (by rfl), pc2891]
  rfl

@[simp] theorem pc2893 : Artifact.submissionArtifact.instructionPC 2787 = 3866 := by
  change Artifact.submissionArtifact.instructionPC (2786+1) = 3866
  rw [pc_succ Artifact.submissionArtifact 2786 (.op .JUMPDEST) (by rfl), pc2892]
  rfl

@[simp] theorem pc2894 : Artifact.submissionArtifact.instructionPC 2788 = 3868 := by
  change Artifact.submissionArtifact.instructionPC (2787+1) = 3868
  rw [pc_succ Artifact.submissionArtifact 2787 (.push 1 1) (by rfl), pc2893]
  rfl

@[simp] theorem pc2895 : Artifact.submissionArtifact.instructionPC 2789 = 3871 := by
  change Artifact.submissionArtifact.instructionPC (2788+1) = 3871
  rw [pc_succ Artifact.submissionArtifact 2788 (.push 2 9408) (by rfl), pc2894]
  rfl

@[simp] theorem pc2896 : Artifact.submissionArtifact.instructionPC 2790 = 3872 := by
  change Artifact.submissionArtifact.instructionPC (2789+1) = 3872
  rw [pc_succ Artifact.submissionArtifact 2789 (.op .MLOAD) (by rfl), pc2895]
  rfl

@[simp] theorem pc2897 : Artifact.submissionArtifact.instructionPC 2791 = 3873 := by
  change Artifact.submissionArtifact.instructionPC (2790+1) = 3873
  rw [pc_succ Artifact.submissionArtifact 2790 (.op .JUMPDEST) (by rfl), pc2896]
  rfl

@[simp] theorem pc2898 : Artifact.submissionArtifact.instructionPC 2792 = 3874 := by
  change Artifact.submissionArtifact.instructionPC (2791+1) = 3874
  rw [pc_succ Artifact.submissionArtifact 2791 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2897]
  rfl

@[simp] theorem pc2899 : Artifact.submissionArtifact.instructionPC 2793 = 3875 := by
  change Artifact.submissionArtifact.instructionPC (2792+1) = 3875
  rw [pc_succ Artifact.submissionArtifact 2792 (.op .MLOAD) (by rfl), pc2898]
  rfl

@[simp] theorem pc2900 : Artifact.submissionArtifact.instructionPC 2794 = 3876 := by
  change Artifact.submissionArtifact.instructionPC (2793+1) = 3876
  rw [pc_succ Artifact.submissionArtifact 2793 (.op .NOT) (by rfl), pc2899]
  rfl

@[simp] theorem pc2901 : Artifact.submissionArtifact.instructionPC 2795 = 3877 := by
  change Artifact.submissionArtifact.instructionPC (2794+1) = 3877
  rw [pc_succ Artifact.submissionArtifact 2794 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2900]
  rfl

@[simp] theorem pc2902 : Artifact.submissionArtifact.instructionPC 2796 = 3878 := by
  change Artifact.submissionArtifact.instructionPC (2795+1) = 3878
  rw [pc_succ Artifact.submissionArtifact 2795 (.op .ADD) (by rfl), pc2901]
  rfl

@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2797 = 3879 := by
  change Artifact.submissionArtifact.instructionPC (2796+1) = 3879
  rw [pc_succ Artifact.submissionArtifact 2796 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2902]
  rfl

@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2798 = 3880 := by
  change Artifact.submissionArtifact.instructionPC (2797+1) = 3880
  rw [pc_succ Artifact.submissionArtifact 2797 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc2903]
  rfl

@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2799 = 3881 := by
  change Artifact.submissionArtifact.instructionPC (2798+1) = 3881
  rw [pc_succ Artifact.submissionArtifact 2798 (.op .LT) (by rfl), pc2904]
  rfl

@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2800 = 3882 := by
  change Artifact.submissionArtifact.instructionPC (2799+1) = 3882
  rw [pc_succ Artifact.submissionArtifact 2799 (.op (.Swap ⟨2, by decide⟩)) (by rfl), pc2905]
  rfl

@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2801 = 3883 := by
  change Artifact.submissionArtifact.instructionPC (2800+1) = 3883
  rw [pc_succ Artifact.submissionArtifact 2800 (.op .POP) (by rfl), pc2906]
  rfl

@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2802 = 3884 := by
  change Artifact.submissionArtifact.instructionPC (2801+1) = 3884
  rw [pc_succ Artifact.submissionArtifact 2801 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc2907]
  rfl

@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2803 = 3887 := by
  change Artifact.submissionArtifact.instructionPC (2802+1) = 3887
  rw [pc_succ Artifact.submissionArtifact 2802 (.push 2 5120) (by rfl), pc2908]
  rfl

@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2804 = 3888 := by
  change Artifact.submissionArtifact.instructionPC (2803+1) = 3888
  rw [pc_succ Artifact.submissionArtifact 2803 (.op .ADD) (by rfl), pc2909]
  rfl

@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2805 = 3889 := by
  change Artifact.submissionArtifact.instructionPC (2804+1) = 3889
  rw [pc_succ Artifact.submissionArtifact 2804 (.op .MSTORE) (by rfl), pc2910]
  rfl

@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2806 = 3890 := by
  change Artifact.submissionArtifact.instructionPC (2805+1) = 3890
  rw [pc_succ Artifact.submissionArtifact 2805 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2911]
  rfl

@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2807 = 3891 := by
  change Artifact.submissionArtifact.instructionPC (2806+1) = 3891
  rw [pc_succ Artifact.submissionArtifact 2806 (.op .ISZERO) (by rfl), pc2912]
  rfl

@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2808 = 3894 := by
  change Artifact.submissionArtifact.instructionPC (2807+1) = 3894
  rw [pc_succ Artifact.submissionArtifact 2807 (.push 2 3903) (by rfl), pc2913]
  rfl

@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2809 = 3895 := by
  change Artifact.submissionArtifact.instructionPC (2808+1) = 3895
  rw [pc_succ Artifact.submissionArtifact 2808 (.op .JUMPI) (by rfl), pc2914]
  rfl

@[simp] theorem pc2915_compact : Artifact.submissionArtifact.instructionPC 2810 = 3897 := by
  change Artifact.submissionArtifact.instructionPC (2809+1) = 3897
  rw [pc_succ Artifact.submissionArtifact 2809 (.push 1 31) (by rfl), pc2915]
  rfl

@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2811 = 3898 := by
  change Artifact.submissionArtifact.instructionPC (2810+1) = 3898
  rw [pc_succ Artifact.submissionArtifact 2810 (.op .NOT) (by rfl), pc2915_compact]
  rfl

@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2812 = 3899 := by
  change Artifact.submissionArtifact.instructionPC (2811+1) = 3899
  rw [pc_succ Artifact.submissionArtifact 2811 (.op .ADD) (by rfl), pc2916]
  rfl

@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2813 = 3902 := by
  change Artifact.submissionArtifact.instructionPC (2812+1) = 3902
  rw [pc_succ Artifact.submissionArtifact 2812 (.push 2 3872) (by rfl), pc2917]
  rfl

@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2814 = 3903 := by
  change Artifact.submissionArtifact.instructionPC (2813+1) = 3903
  rw [pc_succ Artifact.submissionArtifact 2813 (.op .JUMP) (by rfl), pc2918]
  rfl

@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2815 = 3904 := by
  change Artifact.submissionArtifact.instructionPC (2814+1) = 3904
  rw [pc_succ Artifact.submissionArtifact 2814 (.op .JUMPDEST) (by rfl), pc2919]
  rfl

@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2816 = 3905 := by
  change Artifact.submissionArtifact.instructionPC (2815+1) = 3905
  rw [pc_succ Artifact.submissionArtifact 2815 (.op .POP) (by rfl), pc2920]
  rfl

@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2817 = 3906 := by
  change Artifact.submissionArtifact.instructionPC (2816+1) = 3906
  rw [pc_succ Artifact.submissionArtifact 2816 (.op .POP) (by rfl), pc2921]
  rfl

@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2818 = 3907 := by
  change Artifact.submissionArtifact.instructionPC (2817+1) = 3907
  rw [pc_succ Artifact.submissionArtifact 2817 (.push 0 0) (by rfl), pc2922]
  rfl

@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2819 = 3908 := by
  change Artifact.submissionArtifact.instructionPC (2818+1) = 3908
  rw [pc_succ Artifact.submissionArtifact 2818 (.op .MLOAD) (by rfl), pc2923]
  rfl

@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2820 = 3909 := by
  change Artifact.submissionArtifact.instructionPC (2819+1) = 3909
  rw [pc_succ Artifact.submissionArtifact 2819 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2924]
  rfl

@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2821 = 3910 := by
  change Artifact.submissionArtifact.instructionPC (2820+1) = 3910
  rw [pc_succ Artifact.submissionArtifact 2820 (.push 0 0) (by rfl), pc2925]
  rfl

@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2822 = 3911 := by
  change Artifact.submissionArtifact.instructionPC (2821+1) = 3911
  rw [pc_succ Artifact.submissionArtifact 2821 (.op .SUB) (by rfl), pc2926]
  rfl

@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2823 = 3912 := by
  change Artifact.submissionArtifact.instructionPC (2822+1) = 3912
  rw [pc_succ Artifact.submissionArtifact 2822 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc2927]
  rfl

@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2824 = 3913 := by
  change Artifact.submissionArtifact.instructionPC (2823+1) = 3913
  rw [pc_succ Artifact.submissionArtifact 2823 (.op .AND) (by rfl), pc2928]
  rfl

@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2825 = 3914 := by
  change Artifact.submissionArtifact.instructionPC (2824+1) = 3914
  rw [pc_succ Artifact.submissionArtifact 2824 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2929]
  rfl

@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2826 = 3917 := by
  change Artifact.submissionArtifact.instructionPC (2825+1) = 3917
  rw [pc_succ Artifact.submissionArtifact 2825 (.push 2 6144) (by rfl), pc2930]
  rfl

@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2827 = 3918 := by
  change Artifact.submissionArtifact.instructionPC (2826+1) = 3918
  rw [pc_succ Artifact.submissionArtifact 2826 (.op .MSTORE) (by rfl), pc2931]
  rfl

@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2828 = 3919 := by
  change Artifact.submissionArtifact.instructionPC (2827+1) = 3919
  rw [pc_succ Artifact.submissionArtifact 2827 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2932]
  rfl

@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2829 = 3920 := by
  change Artifact.submissionArtifact.instructionPC (2828+1) = 3920
  rw [pc_succ Artifact.submissionArtifact 2828 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2933]
  rfl

@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2830 = 3921 := by
  change Artifact.submissionArtifact.instructionPC (2829+1) = 3921
  rw [pc_succ Artifact.submissionArtifact 2829 (.op .DIV) (by rfl), pc2934]
  rfl

@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2831 = 3922 := by
  change Artifact.submissionArtifact.instructionPC (2830+1) = 3922
  rw [pc_succ Artifact.submissionArtifact 2830 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2935]
  rfl

@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2832 = 3925 := by
  change Artifact.submissionArtifact.instructionPC (2831+1) = 3925
  rw [pc_succ Artifact.submissionArtifact 2831 (.push 2 6176) (by rfl), pc2936]
  rfl

@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2833 = 3926 := by
  change Artifact.submissionArtifact.instructionPC (2832+1) = 3926
  rw [pc_succ Artifact.submissionArtifact 2832 (.op .MSTORE) (by rfl), pc2937]
  rfl

@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2834 = 3927 := by
  change Artifact.submissionArtifact.instructionPC (2833+1) = 3927
  rw [pc_succ Artifact.submissionArtifact 2833 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc2938]
  rfl

@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2835 = 3928 := by
  change Artifact.submissionArtifact.instructionPC (2834+1) = 3928
  rw [pc_succ Artifact.submissionArtifact 2834 (.push 0 0) (by rfl), pc2939]
  rfl

@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2836 = 3929 := by
  change Artifact.submissionArtifact.instructionPC (2835+1) = 3929
  rw [pc_succ Artifact.submissionArtifact 2835 (.op .SUB) (by rfl), pc2940]
  rfl

@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2837 = 3930 := by
  change Artifact.submissionArtifact.instructionPC (2836+1) = 3930
  rw [pc_succ Artifact.submissionArtifact 2836 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2941]
  rfl

@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2838 = 3931 := by
  change Artifact.submissionArtifact.instructionPC (2837+1) = 3931
  rw [pc_succ Artifact.submissionArtifact 2837 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc2942]
  rfl

@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2839 = 3932 := by
  change Artifact.submissionArtifact.instructionPC (2838+1) = 3932
  rw [pc_succ Artifact.submissionArtifact 2838 (.op .DIV) (by rfl), pc2943]
  rfl

@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2840 = 3934 := by
  change Artifact.submissionArtifact.instructionPC (2839+1) = 3934
  rw [pc_succ Artifact.submissionArtifact 2839 (.push 1 1) (by rfl), pc2944]
  rfl

@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2841 = 3935 := by
  change Artifact.submissionArtifact.instructionPC (2840+1) = 3935
  rw [pc_succ Artifact.submissionArtifact 2840 (.op .ADD) (by rfl), pc2945]
  rfl

@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2842 = 3938 := by
  change Artifact.submissionArtifact.instructionPC (2841+1) = 3938
  rw [pc_succ Artifact.submissionArtifact 2841 (.push 2 6208) (by rfl), pc2946]
  rfl

@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2843 = 3939 := by
  change Artifact.submissionArtifact.instructionPC (2842+1) = 3939
  rw [pc_succ Artifact.submissionArtifact 2842 (.op .MSTORE) (by rfl), pc2947]
  rfl

@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2844 = 3940 := by
  change Artifact.submissionArtifact.instructionPC (2843+1) = 3940
  rw [pc_succ Artifact.submissionArtifact 2843 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2948]
  rfl

@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 2845 = 3941 := by
  change Artifact.submissionArtifact.instructionPC (2844+1) = 3941
  rw [pc_succ Artifact.submissionArtifact 2844 (.push 0 0) (by rfl), pc2949]
  rfl

@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 2846 = 3942 := by
  change Artifact.submissionArtifact.instructionPC (2845+1) = 3942
  rw [pc_succ Artifact.submissionArtifact 2845 (.op .SUB) (by rfl), pc2950]
  rfl

@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 2847 = 3943 := by
  change Artifact.submissionArtifact.instructionPC (2846+1) = 3943
  rw [pc_succ Artifact.submissionArtifact 2846 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc2951]
  rfl

@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 2848 = 3944 := by
  change Artifact.submissionArtifact.instructionPC (2847+1) = 3944
  rw [pc_succ Artifact.submissionArtifact 2847 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc2952]
  rfl

@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 2849 = 3945 := by
  change Artifact.submissionArtifact.instructionPC (2848+1) = 3945
  rw [pc_succ Artifact.submissionArtifact 2848 (.op .MOD) (by rfl), pc2953]
  rfl

@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 2850 = 3948 := by
  change Artifact.submissionArtifact.instructionPC (2849+1) = 3948
  rw [pc_succ Artifact.submissionArtifact 2849 (.push 2 6240) (by rfl), pc2954]
  rfl

@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 2851 = 3949 := by
  change Artifact.submissionArtifact.instructionPC (2850+1) = 3949
  rw [pc_succ Artifact.submissionArtifact 2850 (.op .MSTORE) (by rfl), pc2955]
  rfl

@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 2852 = 3950 := by
  change Artifact.submissionArtifact.instructionPC (2851+1) = 3950
  rw [pc_succ Artifact.submissionArtifact 2851 (.op .JUMPDEST) (by rfl), pc2956]
  rfl

@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 2853 = 3951 := by
  change Artifact.submissionArtifact.instructionPC (2852+1) = 3951
  rw [pc_succ Artifact.submissionArtifact 2852 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2957]
  rfl

@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 2854 = 3954 := by
  change Artifact.submissionArtifact.instructionPC (2853+1) = 3954
  rw [pc_succ Artifact.submissionArtifact 2853 (.push 2 3) (by rfl), pc2958]
  rfl

@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 2855 = 3955 := by
  change Artifact.submissionArtifact.instructionPC (2854+1) = 3955
  rw [pc_succ Artifact.submissionArtifact 2854 (.op .MUL) (by rfl), pc2959]
  rfl

@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 2856 = 3957 := by
  change Artifact.submissionArtifact.instructionPC (2855+1) = 3957
  rw [pc_succ Artifact.submissionArtifact 2855 (.push 1 2) (by rfl), pc2960]
  rfl

@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 2857 = 3958 := by
  change Artifact.submissionArtifact.instructionPC (2856+1) = 3958
  rw [pc_succ Artifact.submissionArtifact 2856 (.op .XOR) (by rfl), pc2961]
  rfl

@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 2858 = 3959 := by
  change Artifact.submissionArtifact.instructionPC (2857+1) = 3959
  rw [pc_succ Artifact.submissionArtifact 2857 (.op .JUMPDEST) (by rfl), pc2962]
  rfl

@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 2859 = 3960 := by
  change Artifact.submissionArtifact.instructionPC (2858+1) = 3960
  rw [pc_succ Artifact.submissionArtifact 2858 (.op .JUMPDEST) (by rfl), pc2963]
  rfl

@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 2860 = 3961 := by
  change Artifact.submissionArtifact.instructionPC (2859+1) = 3961
  rw [pc_succ Artifact.submissionArtifact 2859 (.op .JUMPDEST) (by rfl), pc2964]
  rfl

@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 2861 = 3962 := by
  change Artifact.submissionArtifact.instructionPC (2860+1) = 3962
  rw [pc_succ Artifact.submissionArtifact 2860 (.op .JUMPDEST) (by rfl), pc2965]
  rfl

@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 2862 = 3963 := by
  change Artifact.submissionArtifact.instructionPC (2861+1) = 3963
  rw [pc_succ Artifact.submissionArtifact 2861 (.op .JUMPDEST) (by rfl), pc2966]
  rfl

@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 2863 = 3964 := by
  change Artifact.submissionArtifact.instructionPC (2862+1) = 3964
  rw [pc_succ Artifact.submissionArtifact 2862 (.op .JUMPDEST) (by rfl), pc2967]
  rfl

@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 2864 = 3965 := by
  change Artifact.submissionArtifact.instructionPC (2863+1) = 3965
  rw [pc_succ Artifact.submissionArtifact 2863 (.op .JUMPDEST) (by rfl), pc2968]
  rfl

@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 2865 = 3966 := by
  change Artifact.submissionArtifact.instructionPC (2864+1) = 3966
  rw [pc_succ Artifact.submissionArtifact 2864 (.op .JUMPDEST) (by rfl), pc2969]
  rfl

@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 2866 = 3967 := by
  change Artifact.submissionArtifact.instructionPC (2865+1) = 3967
  rw [pc_succ Artifact.submissionArtifact 2865 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2970]
  rfl

@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 2867 = 3968 := by
  change Artifact.submissionArtifact.instructionPC (2866+1) = 3968
  rw [pc_succ Artifact.submissionArtifact 2866 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2971]
  rfl

@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 2868 = 3969 := by
  change Artifact.submissionArtifact.instructionPC (2867+1) = 3969
  rw [pc_succ Artifact.submissionArtifact 2867 (.op .MUL) (by rfl), pc2972]
  rfl

@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 2869 = 3971 := by
  change Artifact.submissionArtifact.instructionPC (2868+1) = 3971
  rw [pc_succ Artifact.submissionArtifact 2868 (.push 1 2) (by rfl), pc2973]
  rfl

@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 2870 = 3972 := by
  change Artifact.submissionArtifact.instructionPC (2869+1) = 3972
  rw [pc_succ Artifact.submissionArtifact 2869 (.op .SUB) (by rfl), pc2974]
  rfl

@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 2871 = 3973 := by
  change Artifact.submissionArtifact.instructionPC (2870+1) = 3973
  rw [pc_succ Artifact.submissionArtifact 2870 (.op .MUL) (by rfl), pc2975]
  rfl

@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 2872 = 3974 := by
  change Artifact.submissionArtifact.instructionPC (2871+1) = 3974
  rw [pc_succ Artifact.submissionArtifact 2871 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2976]
  rfl

@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 2873 = 3975 := by
  change Artifact.submissionArtifact.instructionPC (2872+1) = 3975
  rw [pc_succ Artifact.submissionArtifact 2872 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2977]
  rfl

@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 2874 = 3976 := by
  change Artifact.submissionArtifact.instructionPC (2873+1) = 3976
  rw [pc_succ Artifact.submissionArtifact 2873 (.op .MUL) (by rfl), pc2978]
  rfl

@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 2875 = 3978 := by
  change Artifact.submissionArtifact.instructionPC (2874+1) = 3978
  rw [pc_succ Artifact.submissionArtifact 2874 (.push 1 2) (by rfl), pc2979]
  rfl

@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 2876 = 3979 := by
  change Artifact.submissionArtifact.instructionPC (2875+1) = 3979
  rw [pc_succ Artifact.submissionArtifact 2875 (.op .SUB) (by rfl), pc2980]
  rfl

@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 2877 = 3980 := by
  change Artifact.submissionArtifact.instructionPC (2876+1) = 3980
  rw [pc_succ Artifact.submissionArtifact 2876 (.op .MUL) (by rfl), pc2981]
  rfl

@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 2878 = 3981 := by
  change Artifact.submissionArtifact.instructionPC (2877+1) = 3981
  rw [pc_succ Artifact.submissionArtifact 2877 (.op .JUMPDEST) (by rfl), pc2982]
  rfl

@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 2879 = 3982 := by
  change Artifact.submissionArtifact.instructionPC (2878+1) = 3982
  rw [pc_succ Artifact.submissionArtifact 2878 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2983]
  rfl

@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 2880 = 3983 := by
  change Artifact.submissionArtifact.instructionPC (2879+1) = 3983
  rw [pc_succ Artifact.submissionArtifact 2879 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2984]
  rfl

@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 2881 = 3984 := by
  change Artifact.submissionArtifact.instructionPC (2880+1) = 3984
  rw [pc_succ Artifact.submissionArtifact 2880 (.op .MUL) (by rfl), pc2985]
  rfl

@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 2882 = 3986 := by
  change Artifact.submissionArtifact.instructionPC (2881+1) = 3986
  rw [pc_succ Artifact.submissionArtifact 2881 (.push 1 2) (by rfl), pc2986]
  rfl

@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 2883 = 3987 := by
  change Artifact.submissionArtifact.instructionPC (2882+1) = 3987
  rw [pc_succ Artifact.submissionArtifact 2882 (.op .SUB) (by rfl), pc2987]
  rfl

@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 2884 = 3988 := by
  change Artifact.submissionArtifact.instructionPC (2883+1) = 3988
  rw [pc_succ Artifact.submissionArtifact 2883 (.op .MUL) (by rfl), pc2988]
  rfl

@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 2885 = 3989 := by
  change Artifact.submissionArtifact.instructionPC (2884+1) = 3989
  rw [pc_succ Artifact.submissionArtifact 2884 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2989]
  rfl

@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 2886 = 3990 := by
  change Artifact.submissionArtifact.instructionPC (2885+1) = 3990
  rw [pc_succ Artifact.submissionArtifact 2885 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2990]
  rfl

@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 2887 = 3991 := by
  change Artifact.submissionArtifact.instructionPC (2886+1) = 3991
  rw [pc_succ Artifact.submissionArtifact 2886 (.op .MUL) (by rfl), pc2991]
  rfl

@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 2888 = 3993 := by
  change Artifact.submissionArtifact.instructionPC (2887+1) = 3993
  rw [pc_succ Artifact.submissionArtifact 2887 (.push 1 2) (by rfl), pc2992]
  rfl

@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 2889 = 3994 := by
  change Artifact.submissionArtifact.instructionPC (2888+1) = 3994
  rw [pc_succ Artifact.submissionArtifact 2888 (.op .SUB) (by rfl), pc2993]
  rfl

@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 2890 = 3995 := by
  change Artifact.submissionArtifact.instructionPC (2889+1) = 3995
  rw [pc_succ Artifact.submissionArtifact 2889 (.op .MUL) (by rfl), pc2994]
  rfl

@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 2891 = 3996 := by
  change Artifact.submissionArtifact.instructionPC (2890+1) = 3996
  rw [pc_succ Artifact.submissionArtifact 2890 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc2995]
  rfl

@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 2892 = 3997 := by
  change Artifact.submissionArtifact.instructionPC (2891+1) = 3997
  rw [pc_succ Artifact.submissionArtifact 2891 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc2996]
  rfl

@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 2893 = 3998 := by
  change Artifact.submissionArtifact.instructionPC (2892+1) = 3998
  rw [pc_succ Artifact.submissionArtifact 2892 (.op .MUL) (by rfl), pc2997]
  rfl

@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 2894 = 4000 := by
  change Artifact.submissionArtifact.instructionPC (2893+1) = 4000
  rw [pc_succ Artifact.submissionArtifact 2893 (.push 1 2) (by rfl), pc2998]
  rfl

@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 2895 = 4001 := by
  change Artifact.submissionArtifact.instructionPC (2894+1) = 4001
  rw [pc_succ Artifact.submissionArtifact 2894 (.op .SUB) (by rfl), pc2999]
  rfl

@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 2896 = 4002 := by
  change Artifact.submissionArtifact.instructionPC (2895+1) = 4002
  rw [pc_succ Artifact.submissionArtifact 2895 (.op .MUL) (by rfl), pc3000]
  rfl

@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 2897 = 4003 := by
  change Artifact.submissionArtifact.instructionPC (2896+1) = 4003
  rw [pc_succ Artifact.submissionArtifact 2896 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3001]
  rfl

@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 2898 = 4004 := by
  change Artifact.submissionArtifact.instructionPC (2897+1) = 4004
  rw [pc_succ Artifact.submissionArtifact 2897 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3002]
  rfl

@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 2899 = 4005 := by
  change Artifact.submissionArtifact.instructionPC (2898+1) = 4005
  rw [pc_succ Artifact.submissionArtifact 2898 (.op .MUL) (by rfl), pc3003]
  rfl

@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 2900 = 4007 := by
  change Artifact.submissionArtifact.instructionPC (2899+1) = 4007
  rw [pc_succ Artifact.submissionArtifact 2899 (.push 1 2) (by rfl), pc3004]
  rfl

@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 2901 = 4008 := by
  change Artifact.submissionArtifact.instructionPC (2900+1) = 4008
  rw [pc_succ Artifact.submissionArtifact 2900 (.op .SUB) (by rfl), pc3005]
  rfl

@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 2902 = 4009 := by
  change Artifact.submissionArtifact.instructionPC (2901+1) = 4009
  rw [pc_succ Artifact.submissionArtifact 2901 (.op .MUL) (by rfl), pc3006]
  rfl

@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 2903 = 4012 := by
  change Artifact.submissionArtifact.instructionPC (2902+1) = 4012
  rw [pc_succ Artifact.submissionArtifact 2902 (.push 2 6272) (by rfl), pc3007]
  rfl

@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 2904 = 4013 := by
  change Artifact.submissionArtifact.instructionPC (2903+1) = 4013
  rw [pc_succ Artifact.submissionArtifact 2903 (.op .MSTORE) (by rfl), pc3008]
  rfl

@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 2905 = 4014 := by
  change Artifact.submissionArtifact.instructionPC (2904+1) = 4014
  rw [pc_succ Artifact.submissionArtifact 2904 (.op .POP) (by rfl), pc3009]
  rfl

@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 2906 = 4015 := by
  change Artifact.submissionArtifact.instructionPC (2905+1) = 4015
  rw [pc_succ Artifact.submissionArtifact 2905 (.op .POP) (by rfl), pc3010]
  rfl

@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 2907 = 4016 := by
  change Artifact.submissionArtifact.instructionPC (2906+1) = 4016
  rw [pc_succ Artifact.submissionArtifact 2906 (.op .POP) (by rfl), pc3011]
  rfl

@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 2908 = 4017 := by
  change Artifact.submissionArtifact.instructionPC (2907+1) = 4017
  rw [pc_succ Artifact.submissionArtifact 2907 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3012]
  rfl

@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 2909 = 4018 := by
  change Artifact.submissionArtifact.instructionPC (2908+1) = 4018
  rw [pc_succ Artifact.submissionArtifact 2908 (.op .JUMPDEST) (by rfl), pc3013]
  rfl

@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 2910 = 4019 := by
  change Artifact.submissionArtifact.instructionPC (2909+1) = 4019
  rw [pc_succ Artifact.submissionArtifact 2909 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3014]
  rfl

@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 2911 = 4020 := by
  change Artifact.submissionArtifact.instructionPC (2910+1) = 4020
  rw [pc_succ Artifact.submissionArtifact 2910 (.op .ISZERO) (by rfl), pc3015]
  rfl

@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 2912 = 4023 := by
  change Artifact.submissionArtifact.instructionPC (2911+1) = 4023
  rw [pc_succ Artifact.submissionArtifact 2911 (.push 2 4452) (by rfl), pc3016]
  rfl

@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 2913 = 4024 := by
  change Artifact.submissionArtifact.instructionPC (2912+1) = 4024
  rw [pc_succ Artifact.submissionArtifact 2912 (.op .JUMPI) (by rfl), pc3017]
  rfl

@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 2914 = 4025 := by
  change Artifact.submissionArtifact.instructionPC (2913+1) = 4025
  rw [pc_succ Artifact.submissionArtifact 2913 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3018]
  rfl

@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 2915 = 4028 := by
  change Artifact.submissionArtifact.instructionPC (2914+1) = 4028
  rw [pc_succ Artifact.submissionArtifact 2914 (.push 2 2048) (by rfl), pc3019]
  rfl

@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 2916 = 4031 := by
  change Artifact.submissionArtifact.instructionPC (2915+1) = 4031
  rw [pc_succ Artifact.submissionArtifact 2915 (.push 2 8224) (by rfl), pc3020]
  rfl

@[simp] theorem pc3022 : Artifact.submissionArtifact.instructionPC 2917 = 4032 := by
  change Artifact.submissionArtifact.instructionPC (2916+1) = 4032
  rw [pc_succ Artifact.submissionArtifact 2916 (.op .MCOPY) (by rfl), pc3021]
  rfl

@[simp] theorem pc3023 : Artifact.submissionArtifact.instructionPC 2918 = 4033 := by
  change Artifact.submissionArtifact.instructionPC (2917+1) = 4033
  rw [pc_succ Artifact.submissionArtifact 2917 (.push 0 0) (by rfl), pc3022]
  rfl

@[simp] theorem pc3024 : Artifact.submissionArtifact.instructionPC 2919 = 4036 := by
  change Artifact.submissionArtifact.instructionPC (2918+1) = 4036
  rw [pc_succ Artifact.submissionArtifact 2918 (.push 2 9440) (by rfl), pc3023]
  rfl

@[simp] theorem pc3025 : Artifact.submissionArtifact.instructionPC 2920 = 4037 := by
  change Artifact.submissionArtifact.instructionPC (2919+1) = 4037
  rw [pc_succ Artifact.submissionArtifact 2919 (.op .MLOAD) (by rfl), pc3024]
  rfl

@[simp] theorem pc3026 : Artifact.submissionArtifact.instructionPC 2921 = 4038 := by
  change Artifact.submissionArtifact.instructionPC (2920+1) = 4038
  rw [pc_succ Artifact.submissionArtifact 2920 (.op .MSTORE) (by rfl), pc3025]
  rfl

@[simp] theorem pc3027 : Artifact.submissionArtifact.instructionPC 2922 = 4039 := by
  change Artifact.submissionArtifact.instructionPC (2921+1) = 4039
  rw [pc_succ Artifact.submissionArtifact 2921 (.op .JUMPDEST) (by rfl), pc3026]
  rfl

@[simp] theorem pc3028 : Artifact.submissionArtifact.instructionPC 2923 = 4048 := by
  change Artifact.submissionArtifact.instructionPC (2922+1) = 4048
  rw [pc_succ Artifact.submissionArtifact 2922 (.push 8 2048) (by rfl), pc3027]
  rfl

@[simp] theorem pc3029 : Artifact.submissionArtifact.instructionPC 2924 = 4049 := by
  change Artifact.submissionArtifact.instructionPC (2923+1) = 4049
  rw [pc_succ Artifact.submissionArtifact 2923 (.op .MLOAD) (by rfl), pc3028]
  rfl

@[simp] theorem pc3030 : Artifact.submissionArtifact.instructionPC 2925 = 4052 := by
  change Artifact.submissionArtifact.instructionPC (2924+1) = 4052
  rw [pc_succ Artifact.submissionArtifact 2924 (.push 2 6144) (by rfl), pc3029]
  rfl

@[simp] theorem pc3031 : Artifact.submissionArtifact.instructionPC 2926 = 4053 := by
  change Artifact.submissionArtifact.instructionPC (2925+1) = 4053
  rw [pc_succ Artifact.submissionArtifact 2925 (.op .MLOAD) (by rfl), pc3030]
  rfl

@[simp] theorem pc3032 : Artifact.submissionArtifact.instructionPC 2927 = 4054 := by
  change Artifact.submissionArtifact.instructionPC (2926+1) = 4054
  rw [pc_succ Artifact.submissionArtifact 2926 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3031]
  rfl

@[simp] theorem pc3033 : Artifact.submissionArtifact.instructionPC 2928 = 4057 := by
  change Artifact.submissionArtifact.instructionPC (2927+1) = 4057
  rw [pc_succ Artifact.submissionArtifact 2927 (.push 2 6208) (by rfl), pc3032]
  rfl

@[simp] theorem pc3034 : Artifact.submissionArtifact.instructionPC 2929 = 4058 := by
  change Artifact.submissionArtifact.instructionPC (2928+1) = 4058
  rw [pc_succ Artifact.submissionArtifact 2928 (.op .MLOAD) (by rfl), pc3033]
  rfl

@[simp] theorem pc3035 : Artifact.submissionArtifact.instructionPC 2930 = 4059 := by
  change Artifact.submissionArtifact.instructionPC (2929+1) = 4059
  rw [pc_succ Artifact.submissionArtifact 2929 (.op .MUL) (by rfl), pc3034]
  rfl

@[simp] theorem pc3036 : Artifact.submissionArtifact.instructionPC 2931 = 4060 := by
  change Artifact.submissionArtifact.instructionPC (2930+1) = 4060
  rw [pc_succ Artifact.submissionArtifact 2930 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3035]
  rfl

@[simp] theorem pc3037 : Artifact.submissionArtifact.instructionPC 2932 = 4063 := by
  change Artifact.submissionArtifact.instructionPC (2931+1) = 4063
  rw [pc_succ Artifact.submissionArtifact 2931 (.push 2 2080) (by rfl), pc3036]
  rfl

@[simp] theorem pc3038 : Artifact.submissionArtifact.instructionPC 2933 = 4064 := by
  change Artifact.submissionArtifact.instructionPC (2932+1) = 4064
  rw [pc_succ Artifact.submissionArtifact 2932 (.op .MLOAD) (by rfl), pc3037]
  rfl

@[simp] theorem pc3039 : Artifact.submissionArtifact.instructionPC 2934 = 4065 := by
  change Artifact.submissionArtifact.instructionPC (2933+1) = 4065
  rw [pc_succ Artifact.submissionArtifact 2933 (.op .DIV) (by rfl), pc3038]
  rfl

@[simp] theorem pc3040 : Artifact.submissionArtifact.instructionPC 2935 = 4066 := by
  change Artifact.submissionArtifact.instructionPC (2934+1) = 4066
  rw [pc_succ Artifact.submissionArtifact 2934 (.op .ADD) (by rfl), pc3039]
  rfl

@[simp] theorem pc3041 : Artifact.submissionArtifact.instructionPC 2936 = 4067 := by
  change Artifact.submissionArtifact.instructionPC (2935+1) = 4067
  rw [pc_succ Artifact.submissionArtifact 2935 (.op (.Swap ⟨1, by decide⟩)) (by rfl), pc3040]
  rfl

@[simp] theorem pc3042 : Artifact.submissionArtifact.instructionPC 2937 = 4068 := by
  change Artifact.submissionArtifact.instructionPC (2936+1) = 4068
  rw [pc_succ Artifact.submissionArtifact 2936 (.op .DIV) (by rfl), pc3041]
  rfl

@[simp] theorem pc3047 : Artifact.submissionArtifact.instructionPC 2938 = 4069 := by
  change Artifact.submissionArtifact.instructionPC (2937+1) = 4069
  rw [pc_succ Artifact.submissionArtifact 2937 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3042]
  rfl

@[simp] theorem pc3048 : Artifact.submissionArtifact.instructionPC 2939 = 4072 := by
  change Artifact.submissionArtifact.instructionPC (2938+1) = 4072
  rw [pc_succ Artifact.submissionArtifact 2938 (.push 2 6176) (by rfl), pc3047]
  rfl

@[simp] theorem pc3049 : Artifact.submissionArtifact.instructionPC 2940 = 4073 := by
  change Artifact.submissionArtifact.instructionPC (2939+1) = 4073
  rw [pc_succ Artifact.submissionArtifact 2939 (.op .MLOAD) (by rfl), pc3048]
  rfl

@[simp] theorem pc3050 : Artifact.submissionArtifact.instructionPC 2941 = 4074 := by
  change Artifact.submissionArtifact.instructionPC (2940+1) = 4074
  rw [pc_succ Artifact.submissionArtifact 2940 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3049]
  rfl

@[simp] theorem pc3051 : Artifact.submissionArtifact.instructionPC 2942 = 4077 := by
  change Artifact.submissionArtifact.instructionPC (2941+1) = 4077
  rw [pc_succ Artifact.submissionArtifact 2941 (.push 2 6240) (by rfl), pc3050]
  rfl

@[simp] theorem pc3052 : Artifact.submissionArtifact.instructionPC 2943 = 4078 := by
  change Artifact.submissionArtifact.instructionPC (2942+1) = 4078
  rw [pc_succ Artifact.submissionArtifact 2942 (.op .MLOAD) (by rfl), pc3051]
  rfl

@[simp] theorem pc3053 : Artifact.submissionArtifact.instructionPC 2944 = 4079 := by
  change Artifact.submissionArtifact.instructionPC (2943+1) = 4079
  rw [pc_succ Artifact.submissionArtifact 2943 (.op (.Dup ⟨4, by decide⟩)) (by rfl), pc3052]
  rfl

@[simp] theorem pc3054 : Artifact.submissionArtifact.instructionPC 2945 = 4080 := by
  change Artifact.submissionArtifact.instructionPC (2944+1) = 4080
  rw [pc_succ Artifact.submissionArtifact 2944 (.op .MULMOD) (by rfl), pc3053]
  rfl

@[simp] theorem pc3056 : Artifact.submissionArtifact.instructionPC 2946 = 4081 := by
  change Artifact.submissionArtifact.instructionPC (2945+1) = 4081
  rw [pc_succ Artifact.submissionArtifact 2945 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3054]
  rfl

@[simp] theorem pc3057 : Artifact.submissionArtifact.instructionPC 2947 = 4082 := by
  change Artifact.submissionArtifact.instructionPC (2946+1) = 4082
  rw [pc_succ Artifact.submissionArtifact 2946 (.op .ADDMOD) (by rfl), pc3056]
  rfl

@[simp] theorem pc3058 : Artifact.submissionArtifact.instructionPC 2948 = 4083 := by
  change Artifact.submissionArtifact.instructionPC (2947+1) = 4083
  rw [pc_succ Artifact.submissionArtifact 2947 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3057]
  rfl

@[simp] theorem pc3059 : Artifact.submissionArtifact.instructionPC 2949 = 4084 := by
  change Artifact.submissionArtifact.instructionPC (2948+1) = 4084
  rw [pc_succ Artifact.submissionArtifact 2948 (.op .SUB) (by rfl), pc3058]
  rfl

@[simp] theorem pc3060 : Artifact.submissionArtifact.instructionPC 2950 = 4087 := by
  change Artifact.submissionArtifact.instructionPC (2949+1) = 4087
  rw [pc_succ Artifact.submissionArtifact 2949 (.push 2 6272) (by rfl), pc3059]
  rfl

@[simp] theorem pc3061 : Artifact.submissionArtifact.instructionPC 2951 = 4088 := by
  change Artifact.submissionArtifact.instructionPC (2950+1) = 4088
  rw [pc_succ Artifact.submissionArtifact 2950 (.op .MLOAD) (by rfl), pc3060]
  rfl

@[simp] theorem pc3062 : Artifact.submissionArtifact.instructionPC 2952 = 4089 := by
  change Artifact.submissionArtifact.instructionPC (2951+1) = 4089
  rw [pc_succ Artifact.submissionArtifact 2951 (.op .MUL) (by rfl), pc3061]
  rfl

@[simp] theorem pc3063 : Artifact.submissionArtifact.instructionPC 2953 = 4090 := by
  change Artifact.submissionArtifact.instructionPC (2952+1) = 4090
  rw [pc_succ Artifact.submissionArtifact 2952 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3062]
  rfl

@[simp] theorem pc3064 : Artifact.submissionArtifact.instructionPC 2954 = 4091 := by
  change Artifact.submissionArtifact.instructionPC (2953+1) = 4091
  rw [pc_succ Artifact.submissionArtifact 2953 (.push 0 0) (by rfl), pc3063]
  rfl

@[simp] theorem pc3065 : Artifact.submissionArtifact.instructionPC 2955 = 4092 := by
  change Artifact.submissionArtifact.instructionPC (2954+1) = 4092
  rw [pc_succ Artifact.submissionArtifact 2954 (.op .LT) (by rfl), pc3064]
  rfl

@[simp] theorem pc3066 : Artifact.submissionArtifact.instructionPC 2956 = 4093 := by
  change Artifact.submissionArtifact.instructionPC (2955+1) = 4093
  rw [pc_succ Artifact.submissionArtifact 2955 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3065]
  rfl

@[simp] theorem pc3067 : Artifact.submissionArtifact.instructionPC 2957 = 4094 := by
  change Artifact.submissionArtifact.instructionPC (2956+1) = 4094
  rw [pc_succ Artifact.submissionArtifact 2956 (.op .SUB) (by rfl), pc3066]
  rfl

@[simp] theorem pc3068 : Artifact.submissionArtifact.instructionPC 2958 = 4095 := by
  change Artifact.submissionArtifact.instructionPC (2957+1) = 4095
  rw [pc_succ Artifact.submissionArtifact 2957 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3067]
  rfl

@[simp] theorem pc3069 : Artifact.submissionArtifact.instructionPC 2966 = 4105 := by rfl

@[simp] theorem pc3070 : Artifact.submissionArtifact.instructionPC 2967 = 4106 := by
  change Artifact.submissionArtifact.instructionPC (2966+1) = 4106
  rw [pc_succ Artifact.submissionArtifact 2966 (.op .JUMPDEST) (by rfl), pc3069]
  rfl

@[simp] theorem pc3071 : Artifact.submissionArtifact.instructionPC 2968 = 4107 := by
  change Artifact.submissionArtifact.instructionPC (2967+1) = 4107
  rw [pc_succ Artifact.submissionArtifact 2967 (.push 0 0) (by rfl), pc3070]
  rfl

@[simp] theorem pc3072 : Artifact.submissionArtifact.instructionPC 2969 = 4110 := by
  change Artifact.submissionArtifact.instructionPC (2968+1) = 4110
  rw [pc_succ Artifact.submissionArtifact 2968 (.push 2 9440) (by rfl), pc3071]
  rfl

@[simp] theorem pc3073 : Artifact.submissionArtifact.instructionPC 2970 = 4111 := by
  change Artifact.submissionArtifact.instructionPC (2969+1) = 4111
  rw [pc_succ Artifact.submissionArtifact 2969 (.op .MLOAD) (by rfl), pc3072]
  rfl

@[simp] theorem pc3074 : Artifact.submissionArtifact.instructionPC 2971 = 4114 := by
  change Artifact.submissionArtifact.instructionPC (2970+1) = 4114
  rw [pc_succ Artifact.submissionArtifact 2970 (.push 2 9408) (by rfl), pc3073]
  rfl

@[simp] theorem pc3075 : Artifact.submissionArtifact.instructionPC 2972 = 4115 := by
  change Artifact.submissionArtifact.instructionPC (2971+1) = 4115
  rw [pc_succ Artifact.submissionArtifact 2971 (.op .MLOAD) (by rfl), pc3074]
  rfl

@[simp] theorem pc3076 : Artifact.submissionArtifact.instructionPC 2973 = 4118 := by
  change Artifact.submissionArtifact.instructionPC (2972+1) = 4118
  rw [pc_succ Artifact.submissionArtifact 2972 (.push 2 5120) (by rfl), pc3075]
  rfl

@[simp] theorem pc3077 : Artifact.submissionArtifact.instructionPC 2974 = 4119 := by
  change Artifact.submissionArtifact.instructionPC (2973+1) = 4119
  rw [pc_succ Artifact.submissionArtifact 2973 (.op .ADD) (by rfl), pc3076]
  rfl

@[simp] theorem pc3078 : Artifact.submissionArtifact.instructionPC 2975 = 4120 := by
  change Artifact.submissionArtifact.instructionPC (2974+1) = 4120
  rw [pc_succ Artifact.submissionArtifact 2974 (.op .JUMPDEST) (by rfl), pc3077]
  rfl

@[simp] theorem pc3079 : Artifact.submissionArtifact.instructionPC 2976 = 4121 := by
  change Artifact.submissionArtifact.instructionPC (2975+1) = 4121
  rw [pc_succ Artifact.submissionArtifact 2975 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3078]
  rfl

@[simp] theorem pc3080 : Artifact.submissionArtifact.instructionPC 2977 = 4122 := by
  change Artifact.submissionArtifact.instructionPC (2976+1) = 4122
  rw [pc_succ Artifact.submissionArtifact 2976 (.op .MLOAD) (by rfl), pc3079]
  rfl

@[simp] theorem pc3081 : Artifact.submissionArtifact.instructionPC 2978 = 4155 := by
  change Artifact.submissionArtifact.instructionPC (2977+1) = 4155
  rw [pc_succ Artifact.submissionArtifact 2977 (.push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935) (by rfl), pc3080]
  rfl

@[simp] theorem pc3082 : Artifact.submissionArtifact.instructionPC 2979 = 4156 := by
  change Artifact.submissionArtifact.instructionPC (2978+1) = 4156
  rw [pc_succ Artifact.submissionArtifact 2978 (.op (.Dup ⟨5, by decide⟩)) (by rfl), pc3081]
  rfl

@[simp] theorem pc3083 : Artifact.submissionArtifact.instructionPC 2980 = 4157 := by
  change Artifact.submissionArtifact.instructionPC (2979+1) = 4157
  rw [pc_succ Artifact.submissionArtifact 2979 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3082]
  rfl

@[simp] theorem pc3084 : Artifact.submissionArtifact.instructionPC 2981 = 4158 := by
  change Artifact.submissionArtifact.instructionPC (2980+1) = 4158
  rw [pc_succ Artifact.submissionArtifact 2980 (.op .MUL) (by rfl), pc3083]
  rfl

@[simp] theorem pc3085 : Artifact.submissionArtifact.instructionPC 2982 = 4159 := by
  change Artifact.submissionArtifact.instructionPC (2981+1) = 4159
  rw [pc_succ Artifact.submissionArtifact 2981 (.op (.Swap ⟨1, by decide⟩)) (by rfl), pc3084]
  rfl

@[simp] theorem pc3086 : Artifact.submissionArtifact.instructionPC 2983 = 4160 := by
  change Artifact.submissionArtifact.instructionPC (2982+1) = 4160
  rw [pc_succ Artifact.submissionArtifact 2982 (.op (.Dup ⟨6, by decide⟩)) (by rfl), pc3085]
  rfl

@[simp] theorem pc3087 : Artifact.submissionArtifact.instructionPC 2984 = 4161 := by
  change Artifact.submissionArtifact.instructionPC (2983+1) = 4161
  rw [pc_succ Artifact.submissionArtifact 2983 (.op .MULMOD) (by rfl), pc3086]
  rfl

@[simp] theorem pc3088 : Artifact.submissionArtifact.instructionPC 2985 = 4162 := by
  change Artifact.submissionArtifact.instructionPC (2984+1) = 4162
  rw [pc_succ Artifact.submissionArtifact 2984 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3087]
  rfl

@[simp] theorem pc3089 : Artifact.submissionArtifact.instructionPC 2986 = 4163 := by
  change Artifact.submissionArtifact.instructionPC (2985+1) = 4163
  rw [pc_succ Artifact.submissionArtifact 2985 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3088]
  rfl

@[simp] theorem pc3090 : Artifact.submissionArtifact.instructionPC 2987 = 4164 := by
  change Artifact.submissionArtifact.instructionPC (2986+1) = 4164
  rw [pc_succ Artifact.submissionArtifact 2986 (.op .LT) (by rfl), pc3089]
  rfl

@[simp] theorem pc3091 : Artifact.submissionArtifact.instructionPC 2988 = 4165 := by
  change Artifact.submissionArtifact.instructionPC (2987+1) = 4165
  rw [pc_succ Artifact.submissionArtifact 2987 (.op .SUB) (by rfl), pc3090]
  rfl

@[simp] theorem pc3092 : Artifact.submissionArtifact.instructionPC 2989 = 4166 := by
  change Artifact.submissionArtifact.instructionPC (2988+1) = 4166
  rw [pc_succ Artifact.submissionArtifact 2988 (.op (.Dup ⟨4, by decide⟩)) (by rfl), pc3091]
  rfl

@[simp] theorem pc3093 : Artifact.submissionArtifact.instructionPC 2990 = 4167 := by
  change Artifact.submissionArtifact.instructionPC (2989+1) = 4167
  rw [pc_succ Artifact.submissionArtifact 2989 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3092]
  rfl

@[simp] theorem pc3094 : Artifact.submissionArtifact.instructionPC 2991 = 4168 := by
  change Artifact.submissionArtifact.instructionPC (2990+1) = 4168
  rw [pc_succ Artifact.submissionArtifact 2990 (.op .ADD) (by rfl), pc3093]
  rfl

@[simp] theorem pc3095 : Artifact.submissionArtifact.instructionPC 2992 = 4169 := by
  change Artifact.submissionArtifact.instructionPC (2991+1) = 4169
  rw [pc_succ Artifact.submissionArtifact 2991 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3094]
  rfl

@[simp] theorem pc3096 : Artifact.submissionArtifact.instructionPC 2993 = 4170 := by
  change Artifact.submissionArtifact.instructionPC (2992+1) = 4170
  rw [pc_succ Artifact.submissionArtifact 2992 (.op (.Swap ⟨5, by decide⟩)) (by rfl), pc3095]
  rfl

@[simp] theorem pc3097 : Artifact.submissionArtifact.instructionPC 2994 = 4171 := by
  change Artifact.submissionArtifact.instructionPC (2993+1) = 4171
  rw [pc_succ Artifact.submissionArtifact 2993 (.op .GT) (by rfl), pc3096]
  rfl

@[simp] theorem pc3098 : Artifact.submissionArtifact.instructionPC 2995 = 4172 := by
  change Artifact.submissionArtifact.instructionPC (2994+1) = 4172
  rw [pc_succ Artifact.submissionArtifact 2994 (.op .SUB) (by rfl), pc3097]
  rfl

@[simp] theorem pc3099 : Artifact.submissionArtifact.instructionPC 2996 = 4173 := by
  change Artifact.submissionArtifact.instructionPC (2995+1) = 4173
  rw [pc_succ Artifact.submissionArtifact 2995 (.op .SUB) (by rfl), pc3098]
  rfl

@[simp] theorem pc3100 : Artifact.submissionArtifact.instructionPC 2997 = 4174 := by
  change Artifact.submissionArtifact.instructionPC (2996+1) = 4174
  rw [pc_succ Artifact.submissionArtifact 2996 (.op (.Dup ⟨3, by decide⟩)) (by rfl), pc3099]
  rfl

@[simp] theorem pc3101 : Artifact.submissionArtifact.instructionPC 2998 = 4175 := by
  change Artifact.submissionArtifact.instructionPC (2997+1) = 4175
  rw [pc_succ Artifact.submissionArtifact 2997 (.op (.Dup ⟨3, by decide⟩)) (by rfl), pc3100]
  rfl

@[simp] theorem pc3102 : Artifact.submissionArtifact.instructionPC 2999 = 4176 := by
  change Artifact.submissionArtifact.instructionPC (2998+1) = 4176
  rw [pc_succ Artifact.submissionArtifact 2998 (.op .MLOAD) (by rfl), pc3101]
  rfl

@[simp] theorem pc3103 : Artifact.submissionArtifact.instructionPC 3000 = 4177 := by
  change Artifact.submissionArtifact.instructionPC (2999+1) = 4177
  rw [pc_succ Artifact.submissionArtifact 2999 (.op .ADD) (by rfl), pc3102]
  rfl

@[simp] theorem pc3104 : Artifact.submissionArtifact.instructionPC 3001 = 4178 := by
  change Artifact.submissionArtifact.instructionPC (3000+1) = 4178
  rw [pc_succ Artifact.submissionArtifact 3000 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3103]
  rfl

@[simp] theorem pc3105 : Artifact.submissionArtifact.instructionPC 3002 = 4179 := by
  change Artifact.submissionArtifact.instructionPC (3001+1) = 4179
  rw [pc_succ Artifact.submissionArtifact 3001 (.op (.Swap ⟨4, by decide⟩)) (by rfl), pc3104]
  rfl

@[simp] theorem pc3106 : Artifact.submissionArtifact.instructionPC 3003 = 4180 := by
  change Artifact.submissionArtifact.instructionPC (3002+1) = 4180
  rw [pc_succ Artifact.submissionArtifact 3002 (.op .GT) (by rfl), pc3105]
  rfl

@[simp] theorem pc3107 : Artifact.submissionArtifact.instructionPC 3004 = 4181 := by
  change Artifact.submissionArtifact.instructionPC (3003+1) = 4181
  rw [pc_succ Artifact.submissionArtifact 3003 (.op .ADD) (by rfl), pc3106]
  rfl

@[simp] theorem pc3108 : Artifact.submissionArtifact.instructionPC 3005 = 4182 := by
  change Artifact.submissionArtifact.instructionPC (3004+1) = 4182
  rw [pc_succ Artifact.submissionArtifact 3004 (.op (.Swap ⟨2, by decide⟩)) (by rfl), pc3107]
  rfl

@[simp] theorem pc3109 : Artifact.submissionArtifact.instructionPC 3006 = 4183 := by
  change Artifact.submissionArtifact.instructionPC (3005+1) = 4183
  rw [pc_succ Artifact.submissionArtifact 3005 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3108]
  rfl

@[simp] theorem pc3110 : Artifact.submissionArtifact.instructionPC 3007 = 4216 := by
  change Artifact.submissionArtifact.instructionPC (3006+1) = 4216
  rw [pc_succ Artifact.submissionArtifact 3006 (.push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904) (by rfl), pc3109]
  rfl

@[simp] theorem pc3111 : Artifact.submissionArtifact.instructionPC 3008 = 4217 := by
  change Artifact.submissionArtifact.instructionPC (3007+1) = 4217
  rw [pc_succ Artifact.submissionArtifact 3007 (.op .ADD) (by rfl), pc3110]
  rfl

@[simp] theorem pc3112 : Artifact.submissionArtifact.instructionPC 3009 = 4218 := by
  change Artifact.submissionArtifact.instructionPC (3008+1) = 4218
  rw [pc_succ Artifact.submissionArtifact 3008 (.op (.Swap ⟨2, by decide⟩)) (by rfl), pc3111]
  rfl

@[simp] theorem pc3113 : Artifact.submissionArtifact.instructionPC 3010 = 4219 := by
  change Artifact.submissionArtifact.instructionPC (3009+1) = 4219
  rw [pc_succ Artifact.submissionArtifact 3009 (.op .MSTORE) (by rfl), pc3112]
  rfl

@[simp] theorem pc3114 : Artifact.submissionArtifact.instructionPC 3011 = 4252 := by
  change Artifact.submissionArtifact.instructionPC (3010+1) = 4252
  rw [pc_succ Artifact.submissionArtifact 3010 (.push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904) (by rfl), pc3113]
  rfl

@[simp] theorem pc3120 : Artifact.submissionArtifact.instructionPC 3012 = 4253 := by
  change Artifact.submissionArtifact.instructionPC (3011+1) = 4253
  rw [pc_succ Artifact.submissionArtifact 3011 (.op .ADD) (by rfl), pc3114]
  rfl

@[simp] theorem pc3121 : Artifact.submissionArtifact.instructionPC 3013 = 4256 := by
  change Artifact.submissionArtifact.instructionPC (3012+1) = 4256
  rw [pc_succ Artifact.submissionArtifact 3012 (.push 2 8224) (by rfl), pc3120]
  rfl

@[simp] theorem pc3122 : Artifact.submissionArtifact.instructionPC 3014 = 4257 := by
  change Artifact.submissionArtifact.instructionPC (3013+1) = 4257
  rw [pc_succ Artifact.submissionArtifact 3013 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3121]
  rfl

@[simp] theorem pc3123 : Artifact.submissionArtifact.instructionPC 3015 = 4258 := by
  change Artifact.submissionArtifact.instructionPC (3014+1) = 4258
  rw [pc_succ Artifact.submissionArtifact 3014 (.op .GT) (by rfl), pc3122]
  rfl

@[simp] theorem pc3124 : Artifact.submissionArtifact.instructionPC 3016 = 4261 := by
  change Artifact.submissionArtifact.instructionPC (3015+1) = 4261
  rw [pc_succ Artifact.submissionArtifact 3015 (.push 2 4119) (by rfl), pc3123]
  rfl

@[simp] theorem pc3125 : Artifact.submissionArtifact.instructionPC 3017 = 4262 := by
  change Artifact.submissionArtifact.instructionPC (3016+1) = 4262
  rw [pc_succ Artifact.submissionArtifact 3016 (.op .JUMPI) (by rfl), pc3124]
  rfl

@[simp] theorem pc3126 : Artifact.submissionArtifact.instructionPC 3018 = 4263 := by
  change Artifact.submissionArtifact.instructionPC (3017+1) = 4263
  rw [pc_succ Artifact.submissionArtifact 3017 (.op .POP) (by rfl), pc3125]
  rfl

@[simp] theorem pc3127 : Artifact.submissionArtifact.instructionPC 3019 = 4264 := by
  change Artifact.submissionArtifact.instructionPC (3018+1) = 4264
  rw [pc_succ Artifact.submissionArtifact 3018 (.op .POP) (by rfl), pc3126]
  rfl

@[simp] theorem pc3128 : Artifact.submissionArtifact.instructionPC 3020 = 4267 := by
  change Artifact.submissionArtifact.instructionPC (3019+1) = 4267
  rw [pc_succ Artifact.submissionArtifact 3019 (.push 2 8224) (by rfl), pc3127]
  rfl

@[simp] theorem pc3129 : Artifact.submissionArtifact.instructionPC 3021 = 4268 := by
  change Artifact.submissionArtifact.instructionPC (3020+1) = 4268
  rw [pc_succ Artifact.submissionArtifact 3020 (.op .MLOAD) (by rfl), pc3128]
  rfl

@[simp] theorem pc3130 : Artifact.submissionArtifact.instructionPC 3022 = 4269 := by
  change Artifact.submissionArtifact.instructionPC (3021+1) = 4269
  rw [pc_succ Artifact.submissionArtifact 3021 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3129]
  rfl

@[simp] theorem pc3131 : Artifact.submissionArtifact.instructionPC 3023 = 4270 := by
  change Artifact.submissionArtifact.instructionPC (3022+1) = 4270
  rw [pc_succ Artifact.submissionArtifact 3022 (.op .ADD) (by rfl), pc3130]
  rfl

@[simp] theorem pc3132 : Artifact.submissionArtifact.instructionPC 3024 = 4271 := by
  change Artifact.submissionArtifact.instructionPC (3023+1) = 4271
  rw [pc_succ Artifact.submissionArtifact 3023 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3131]
  rfl

@[simp] theorem pc3133 : Artifact.submissionArtifact.instructionPC 3025 = 4272 := by
  change Artifact.submissionArtifact.instructionPC (3024+1) = 4272
  rw [pc_succ Artifact.submissionArtifact 3024 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3132]
  rfl

@[simp] theorem pc3134 : Artifact.submissionArtifact.instructionPC 3026 = 4273 := by
  change Artifact.submissionArtifact.instructionPC (3025+1) = 4273
  rw [pc_succ Artifact.submissionArtifact 3025 (.op .LT) (by rfl), pc3133]
  rfl

@[simp] theorem pc3135 : Artifact.submissionArtifact.instructionPC 3027 = 4274 := by
  change Artifact.submissionArtifact.instructionPC (3026+1) = 4274
  rw [pc_succ Artifact.submissionArtifact 3026 (.op (.Swap ⟨1, by decide⟩)) (by rfl), pc3134]
  rfl

@[simp] theorem pc3136 : Artifact.submissionArtifact.instructionPC 3028 = 4275 := by
  change Artifact.submissionArtifact.instructionPC (3027+1) = 4275
  rw [pc_succ Artifact.submissionArtifact 3027 (.op .POP) (by rfl), pc3135]
  rfl

@[simp] theorem pc3137 : Artifact.submissionArtifact.instructionPC 3029 = 4276 := by
  change Artifact.submissionArtifact.instructionPC (3028+1) = 4276
  rw [pc_succ Artifact.submissionArtifact 3028 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3136]
  rfl

@[simp] theorem pc3138 : Artifact.submissionArtifact.instructionPC 3030 = 4277 := by
  change Artifact.submissionArtifact.instructionPC (3029+1) = 4277
  rw [pc_succ Artifact.submissionArtifact 3029 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3137]
  rfl

@[simp] theorem pc3139 : Artifact.submissionArtifact.instructionPC 3031 = 4278 := by
  change Artifact.submissionArtifact.instructionPC (3030+1) = 4278
  rw [pc_succ Artifact.submissionArtifact 3030 (.op .LT) (by rfl), pc3138]
  rfl

@[simp] theorem pc3140 : Artifact.submissionArtifact.instructionPC 3032 = 4279 := by
  change Artifact.submissionArtifact.instructionPC (3031+1) = 4279
  rw [pc_succ Artifact.submissionArtifact 3031 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3139]
  rfl

@[simp] theorem pc3141 : Artifact.submissionArtifact.instructionPC 3033 = 4280 := by
  change Artifact.submissionArtifact.instructionPC (3032+1) = 4280
  rw [pc_succ Artifact.submissionArtifact 3032 (.op (.Dup ⟨3, by decide⟩)) (by rfl), pc3140]
  rfl

@[simp] theorem pc3142 : Artifact.submissionArtifact.instructionPC 3034 = 4281 := by
  change Artifact.submissionArtifact.instructionPC (3033+1) = 4281
  rw [pc_succ Artifact.submissionArtifact 3033 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3141]
  rfl

@[simp] theorem pc3143 : Artifact.submissionArtifact.instructionPC 3035 = 4282 := by
  change Artifact.submissionArtifact.instructionPC (3034+1) = 4282
  rw [pc_succ Artifact.submissionArtifact 3034 (.op .SUB) (by rfl), pc3142]
  rfl

@[simp] theorem pc3144 : Artifact.submissionArtifact.instructionPC 3036 = 4283 := by
  change Artifact.submissionArtifact.instructionPC (3035+1) = 4283
  rw [pc_succ Artifact.submissionArtifact 3035 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3143]
  rfl

@[simp] theorem pc3145 : Artifact.submissionArtifact.instructionPC 3037 = 4286 := by
  change Artifact.submissionArtifact.instructionPC (3036+1) = 4286
  rw [pc_succ Artifact.submissionArtifact 3036 (.push 2 8224) (by rfl), pc3144]
  rfl

@[simp] theorem pc3146 : Artifact.submissionArtifact.instructionPC 3038 = 4287 := by
  change Artifact.submissionArtifact.instructionPC (3037+1) = 4287
  rw [pc_succ Artifact.submissionArtifact 3037 (.op .MSTORE) (by rfl), pc3145]
  rfl

@[simp] theorem pc3147 : Artifact.submissionArtifact.instructionPC 3039 = 4288 := by
  change Artifact.submissionArtifact.instructionPC (3038+1) = 4288
  rw [pc_succ Artifact.submissionArtifact 3038 (.op .POP) (by rfl), pc3146]
  rfl

@[simp] theorem pc3148 : Artifact.submissionArtifact.instructionPC 3040 = 4289 := by
  change Artifact.submissionArtifact.instructionPC (3039+1) = 4289
  rw [pc_succ Artifact.submissionArtifact 3039 (.op .GT) (by rfl), pc3147]
  rfl

@[simp] theorem pc3149 : Artifact.submissionArtifact.instructionPC 3041 = 4290 := by
  change Artifact.submissionArtifact.instructionPC (3040+1) = 4290
  rw [pc_succ Artifact.submissionArtifact 3040 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3148]
  rfl

@[simp] theorem pc3150 : Artifact.submissionArtifact.instructionPC 3042 = 4291 := by
  change Artifact.submissionArtifact.instructionPC (3041+1) = 4291
  rw [pc_succ Artifact.submissionArtifact 3041 (.op .POP) (by rfl), pc3149]
  rfl

@[simp] theorem pc3151 : Artifact.submissionArtifact.instructionPC 3043 = 4292 := by
  change Artifact.submissionArtifact.instructionPC (3042+1) = 4292
  rw [pc_succ Artifact.submissionArtifact 3042 (.op .ISZERO) (by rfl), pc3150]
  rfl

@[simp] theorem pc3152 : Artifact.submissionArtifact.instructionPC 3044 = 4295 := by
  change Artifact.submissionArtifact.instructionPC (3043+1) = 4295
  rw [pc_succ Artifact.submissionArtifact 3043 (.push 2 4363) (by rfl), pc3151]
  rfl

@[simp] theorem pc3153 : Artifact.submissionArtifact.instructionPC 3045 = 4296 := by
  change Artifact.submissionArtifact.instructionPC (3044+1) = 4296
  rw [pc_succ Artifact.submissionArtifact 3044 (.op .JUMPI) (by rfl), pc3152]
  rfl

@[simp] theorem pc3154 : Artifact.submissionArtifact.instructionPC 3046 = 4297 := by
  change Artifact.submissionArtifact.instructionPC (3045+1) = 4297
  rw [pc_succ Artifact.submissionArtifact 3045 (.op .JUMPDEST) (by rfl), pc3153]
  rfl

@[simp] theorem pc3155 : Artifact.submissionArtifact.instructionPC 3047 = 4298 := by
  change Artifact.submissionArtifact.instructionPC (3046+1) = 4298
  rw [pc_succ Artifact.submissionArtifact 3046 (.push 0 0) (by rfl), pc3154]
  rfl

@[simp] theorem pc3156 : Artifact.submissionArtifact.instructionPC 3048 = 4301 := by
  change Artifact.submissionArtifact.instructionPC (3047+1) = 4301
  rw [pc_succ Artifact.submissionArtifact 3047 (.push 2 9440) (by rfl), pc3155]
  rfl

@[simp] theorem pc3157 : Artifact.submissionArtifact.instructionPC 3049 = 4302 := by
  change Artifact.submissionArtifact.instructionPC (3048+1) = 4302
  rw [pc_succ Artifact.submissionArtifact 3048 (.op .MLOAD) (by rfl), pc3156]
  rfl

@[simp] theorem pc3158 : Artifact.submissionArtifact.instructionPC 3050 = 4303 := by
  change Artifact.submissionArtifact.instructionPC (3049+1) = 4303
  rw [pc_succ Artifact.submissionArtifact 3049 (.op .JUMPDEST) (by rfl), pc3157]
  rfl

@[simp] theorem pc3159 : Artifact.submissionArtifact.instructionPC 3051 = 4304 := by
  change Artifact.submissionArtifact.instructionPC (3050+1) = 4304
  rw [pc_succ Artifact.submissionArtifact 3050 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3158]
  rfl

@[simp] theorem pc3160 : Artifact.submissionArtifact.instructionPC 3052 = 4305 := by
  change Artifact.submissionArtifact.instructionPC (3051+1) = 4305
  rw [pc_succ Artifact.submissionArtifact 3051 (.op .MLOAD) (by rfl), pc3159]
  rfl

@[simp] theorem pc3161 : Artifact.submissionArtifact.instructionPC 3053 = 4306 := by
  change Artifact.submissionArtifact.instructionPC (3052+1) = 4306
  rw [pc_succ Artifact.submissionArtifact 3052 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3160]
  rfl

@[simp] theorem pc3162 : Artifact.submissionArtifact.instructionPC 3054 = 4309 := by
  change Artifact.submissionArtifact.instructionPC (3053+1) = 4309
  rw [pc_succ Artifact.submissionArtifact 3053 (.push 2 8256) (by rfl), pc3161]
  rfl

@[simp] theorem pc3163 : Artifact.submissionArtifact.instructionPC 3055 = 4310 := by
  change Artifact.submissionArtifact.instructionPC (3054+1) = 4310
  rw [pc_succ Artifact.submissionArtifact 3054 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3162]
  rfl

@[simp] theorem pc3164 : Artifact.submissionArtifact.instructionPC 3056 = 4311 := by
  change Artifact.submissionArtifact.instructionPC (3055+1) = 4311
  rw [pc_succ Artifact.submissionArtifact 3055 (.op .SUB) (by rfl), pc3163]
  rfl

@[simp] theorem pc3165 : Artifact.submissionArtifact.instructionPC 3057 = 4312 := by
  change Artifact.submissionArtifact.instructionPC (3056+1) = 4312
  rw [pc_succ Artifact.submissionArtifact 3056 (.op .MLOAD) (by rfl), pc3164]
  rfl

@[simp] theorem pc3166 : Artifact.submissionArtifact.instructionPC 3058 = 4313 := by
  change Artifact.submissionArtifact.instructionPC (3057+1) = 4313
  rw [pc_succ Artifact.submissionArtifact 3057 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3165]
  rfl

@[simp] theorem pc3167 : Artifact.submissionArtifact.instructionPC 3059 = 4314 := by
  change Artifact.submissionArtifact.instructionPC (3058+1) = 4314
  rw [pc_succ Artifact.submissionArtifact 3058 (.op .ADD) (by rfl), pc3166]
  rfl

@[simp] theorem pc3168 : Artifact.submissionArtifact.instructionPC 3060 = 4315 := by
  change Artifact.submissionArtifact.instructionPC (3059+1) = 4315
  rw [pc_succ Artifact.submissionArtifact 3059 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3167]
  rfl

@[simp] theorem pc3169 : Artifact.submissionArtifact.instructionPC 3061 = 4316 := by
  change Artifact.submissionArtifact.instructionPC (3060+1) = 4316
  rw [pc_succ Artifact.submissionArtifact 3060 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3168]
  rfl

@[simp] theorem pc3170 : Artifact.submissionArtifact.instructionPC 3062 = 4317 := by
  change Artifact.submissionArtifact.instructionPC (3061+1) = 4317
  rw [pc_succ Artifact.submissionArtifact 3061 (.op .GT) (by rfl), pc3169]
  rfl

@[simp] theorem pc3171 : Artifact.submissionArtifact.instructionPC 3063 = 4318 := by
  change Artifact.submissionArtifact.instructionPC (3062+1) = 4318
  rw [pc_succ Artifact.submissionArtifact 3062 (.op (.Swap ⟨1, by decide⟩)) (by rfl), pc3170]
  rfl

@[simp] theorem pc3172 : Artifact.submissionArtifact.instructionPC 3064 = 4319 := by
  change Artifact.submissionArtifact.instructionPC (3063+1) = 4319
  rw [pc_succ Artifact.submissionArtifact 3063 (.op .POP) (by rfl), pc3171]
  rfl

@[simp] theorem pc3173 : Artifact.submissionArtifact.instructionPC 3065 = 4320 := by
  change Artifact.submissionArtifact.instructionPC (3064+1) = 4320
  rw [pc_succ Artifact.submissionArtifact 3064 (.op (.Dup ⟨3, by decide⟩)) (by rfl), pc3172]
  rfl

@[simp] theorem pc3174 : Artifact.submissionArtifact.instructionPC 3066 = 4321 := by
  change Artifact.submissionArtifact.instructionPC (3065+1) = 4321
  rw [pc_succ Artifact.submissionArtifact 3065 (.op .ADD) (by rfl), pc3173]
  rfl

@[simp] theorem pc3175 : Artifact.submissionArtifact.instructionPC 3067 = 4322 := by
  change Artifact.submissionArtifact.instructionPC (3066+1) = 4322
  rw [pc_succ Artifact.submissionArtifact 3066 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3174]
  rfl

@[simp] theorem pc3176 : Artifact.submissionArtifact.instructionPC 3068 = 4323 := by
  change Artifact.submissionArtifact.instructionPC (3067+1) = 4323
  rw [pc_succ Artifact.submissionArtifact 3067 (.op (.Dup ⟨4, by decide⟩)) (by rfl), pc3175]
  rfl

@[simp] theorem pc3177 : Artifact.submissionArtifact.instructionPC 3069 = 4324 := by
  change Artifact.submissionArtifact.instructionPC (3068+1) = 4324
  rw [pc_succ Artifact.submissionArtifact 3068 (.op .GT) (by rfl), pc3176]
  rfl

@[simp] theorem pc3178 : Artifact.submissionArtifact.instructionPC 3070 = 4325 := by
  change Artifact.submissionArtifact.instructionPC (3069+1) = 4325
  rw [pc_succ Artifact.submissionArtifact 3069 (.op (.Swap ⟨3, by decide⟩)) (by rfl), pc3177]
  rfl

@[simp] theorem pc3179 : Artifact.submissionArtifact.instructionPC 3071 = 4326 := by
  change Artifact.submissionArtifact.instructionPC (3070+1) = 4326
  rw [pc_succ Artifact.submissionArtifact 3070 (.op .POP) (by rfl), pc3178]
  rfl

@[simp] theorem pc3180 : Artifact.submissionArtifact.instructionPC 3072 = 4327 := by
  change Artifact.submissionArtifact.instructionPC (3071+1) = 4327
  rw [pc_succ Artifact.submissionArtifact 3071 (.op (.Dup ⟨2, by decide⟩)) (by rfl), pc3179]
  rfl

@[simp] theorem pc3181 : Artifact.submissionArtifact.instructionPC 3073 = 4328 := by
  change Artifact.submissionArtifact.instructionPC (3072+1) = 4328
  rw [pc_succ Artifact.submissionArtifact 3072 (.op .MSTORE) (by rfl), pc3180]
  rfl

@[simp] theorem pc3182 : Artifact.submissionArtifact.instructionPC 3074 = 4329 := by
  change Artifact.submissionArtifact.instructionPC (3073+1) = 4329
  rw [pc_succ Artifact.submissionArtifact 3073 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3181]
  rfl

@[simp] theorem pc3183 : Artifact.submissionArtifact.instructionPC 3075 = 4330 := by
  change Artifact.submissionArtifact.instructionPC (3074+1) = 4330
  rw [pc_succ Artifact.submissionArtifact 3074 (.op (.Swap ⟨1, by decide⟩)) (by rfl), pc3182]
  rfl

@[simp] theorem pc3184 : Artifact.submissionArtifact.instructionPC 3076 = 4331 := by
  change Artifact.submissionArtifact.instructionPC (3075+1) = 4331
  rw [pc_succ Artifact.submissionArtifact 3075 (.op .OR) (by rfl), pc3183]
  rfl

@[simp] theorem pc3185 : Artifact.submissionArtifact.instructionPC 3077 = 4332 := by
  change Artifact.submissionArtifact.instructionPC (3076+1) = 4332
  rw [pc_succ Artifact.submissionArtifact 3076 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3184]
  rfl

@[simp] theorem pc3185_compact : Artifact.submissionArtifact.instructionPC 3078 = 4334 := by
  change Artifact.submissionArtifact.instructionPC (3077+1) = 4334
  rw [pc_succ Artifact.submissionArtifact 3077 (.push 1 31) (by rfl), pc3185]
  rfl

@[simp] theorem pc3186 : Artifact.submissionArtifact.instructionPC 3079 = 4335 := by
  change Artifact.submissionArtifact.instructionPC (3078+1) = 4335
  rw [pc_succ Artifact.submissionArtifact 3078 (.op .NOT) (by rfl), pc3185_compact]
  rfl

@[simp] theorem pc3187 : Artifact.submissionArtifact.instructionPC 3080 = 4336 := by
  change Artifact.submissionArtifact.instructionPC (3079+1) = 4336
  rw [pc_succ Artifact.submissionArtifact 3079 (.op .ADD) (by rfl), pc3186]
  rfl

@[simp] theorem pc3188 : Artifact.submissionArtifact.instructionPC 3081 = 4339 := by
  change Artifact.submissionArtifact.instructionPC (3080+1) = 4339
  rw [pc_succ Artifact.submissionArtifact 3080 (.push 2 8255) (by rfl), pc3187]
  rfl

@[simp] theorem pc3189 : Artifact.submissionArtifact.instructionPC 3082 = 4340 := by
  change Artifact.submissionArtifact.instructionPC (3081+1) = 4340
  rw [pc_succ Artifact.submissionArtifact 3081 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3188]
  rfl

@[simp] theorem pc3190 : Artifact.submissionArtifact.instructionPC 3083 = 4341 := by
  change Artifact.submissionArtifact.instructionPC (3082+1) = 4341
  rw [pc_succ Artifact.submissionArtifact 3082 (.op .GT) (by rfl), pc3189]
  rfl

@[simp] theorem pc3191 : Artifact.submissionArtifact.instructionPC 3084 = 4344 := by
  change Artifact.submissionArtifact.instructionPC (3083+1) = 4344
  rw [pc_succ Artifact.submissionArtifact 3083 (.push 2 4302) (by rfl), pc3190]
  rfl

@[simp] theorem pc3192 : Artifact.submissionArtifact.instructionPC 3085 = 4345 := by
  change Artifact.submissionArtifact.instructionPC (3084+1) = 4345
  rw [pc_succ Artifact.submissionArtifact 3084 (.op .JUMPI) (by rfl), pc3191]
  rfl

@[simp] theorem pc3193 : Artifact.submissionArtifact.instructionPC 3086 = 4346 := by
  change Artifact.submissionArtifact.instructionPC (3085+1) = 4346
  rw [pc_succ Artifact.submissionArtifact 3085 (.op .POP) (by rfl), pc3192]
  rfl

@[simp] theorem pc3194 : Artifact.submissionArtifact.instructionPC 3087 = 4349 := by
  change Artifact.submissionArtifact.instructionPC (3086+1) = 4349
  rw [pc_succ Artifact.submissionArtifact 3086 (.push 2 8224) (by rfl), pc3193]
  rfl

@[simp] theorem pc3195 : Artifact.submissionArtifact.instructionPC 3088 = 4350 := by
  change Artifact.submissionArtifact.instructionPC (3087+1) = 4350
  rw [pc_succ Artifact.submissionArtifact 3087 (.op .MLOAD) (by rfl), pc3194]
  rfl

@[simp] theorem pc3196 : Artifact.submissionArtifact.instructionPC 3089 = 4351 := by
  change Artifact.submissionArtifact.instructionPC (3088+1) = 4351
  rw [pc_succ Artifact.submissionArtifact 3088 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3195]
  rfl

@[simp] theorem pc3197 : Artifact.submissionArtifact.instructionPC 3090 = 4352 := by
  change Artifact.submissionArtifact.instructionPC (3089+1) = 4352
  rw [pc_succ Artifact.submissionArtifact 3089 (.op .ADD) (by rfl), pc3196]
  rfl

@[simp] theorem pc3198 : Artifact.submissionArtifact.instructionPC 3091 = 4353 := by
  change Artifact.submissionArtifact.instructionPC (3090+1) = 4353
  rw [pc_succ Artifact.submissionArtifact 3090 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3197]
  rfl

@[simp] theorem pc3199 : Artifact.submissionArtifact.instructionPC 3092 = 4356 := by
  change Artifact.submissionArtifact.instructionPC (3091+1) = 4356
  rw [pc_succ Artifact.submissionArtifact 3091 (.push 2 8224) (by rfl), pc3198]
  rfl

@[simp] theorem pc3200 : Artifact.submissionArtifact.instructionPC 3093 = 4357 := by
  change Artifact.submissionArtifact.instructionPC (3092+1) = 4357
  rw [pc_succ Artifact.submissionArtifact 3092 (.op .MSTORE) (by rfl), pc3199]
  rfl

@[simp] theorem pc3201 : Artifact.submissionArtifact.instructionPC 3094 = 4358 := by
  change Artifact.submissionArtifact.instructionPC (3093+1) = 4358
  rw [pc_succ Artifact.submissionArtifact 3093 (.op .LT) (by rfl), pc3200]
  rfl

@[simp] theorem pc3202 : Artifact.submissionArtifact.instructionPC 3095 = 4359 := by
  change Artifact.submissionArtifact.instructionPC (3094+1) = 4359
  rw [pc_succ Artifact.submissionArtifact 3094 (.op .ISZERO) (by rfl), pc3201]
  rfl

@[simp] theorem pc3203 : Artifact.submissionArtifact.instructionPC 3096 = 4362 := by
  change Artifact.submissionArtifact.instructionPC (3095+1) = 4362
  rw [pc_succ Artifact.submissionArtifact 3095 (.push 2 4296) (by rfl), pc3202]
  rfl

@[simp] theorem pc3204 : Artifact.submissionArtifact.instructionPC 3097 = 4363 := by
  change Artifact.submissionArtifact.instructionPC (3096+1) = 4363
  rw [pc_succ Artifact.submissionArtifact 3096 (.op .JUMPI) (by rfl), pc3203]
  rfl

@[simp] theorem pc3205 : Artifact.submissionArtifact.instructionPC 3098 = 4364 := by
  change Artifact.submissionArtifact.instructionPC (3097+1) = 4364
  rw [pc_succ Artifact.submissionArtifact 3097 (.op .JUMPDEST) (by rfl), pc3204]
  rfl

@[simp] theorem pc3206 : Artifact.submissionArtifact.instructionPC 3099 = 4367 := by
  change Artifact.submissionArtifact.instructionPC (3098+1) = 4367
  rw [pc_succ Artifact.submissionArtifact 3098 (.push 2 8224) (by rfl), pc3205]
  rfl

@[simp] theorem pc3207 : Artifact.submissionArtifact.instructionPC 3100 = 4368 := by
  change Artifact.submissionArtifact.instructionPC (3099+1) = 4368
  rw [pc_succ Artifact.submissionArtifact 3099 (.op .MLOAD) (by rfl), pc3206]
  rfl

@[simp] theorem pc3208 : Artifact.submissionArtifact.instructionPC 3101 = 4369 := by
  change Artifact.submissionArtifact.instructionPC (3100+1) = 4369
  rw [pc_succ Artifact.submissionArtifact 3100 (.op .ISZERO) (by rfl), pc3207]
  rfl

@[simp] theorem pc3209 : Artifact.submissionArtifact.instructionPC 3102 = 4372 := by
  change Artifact.submissionArtifact.instructionPC (3101+1) = 4372
  rw [pc_succ Artifact.submissionArtifact 3101 (.push 2 4432) (by rfl), pc3208]
  rfl

@[simp] theorem pc3210 : Artifact.submissionArtifact.instructionPC 3103 = 4373 := by
  change Artifact.submissionArtifact.instructionPC (3102+1) = 4373
  rw [pc_succ Artifact.submissionArtifact 3102 (.op .JUMPI) (by rfl), pc3209]
  rfl

@[simp] theorem pc3211 : Artifact.submissionArtifact.instructionPC 3104 = 4374 := by
  change Artifact.submissionArtifact.instructionPC (3103+1) = 4374
  rw [pc_succ Artifact.submissionArtifact 3103 (.push 0 0) (by rfl), pc3210]
  rfl

@[simp] theorem pc3212 : Artifact.submissionArtifact.instructionPC 3105 = 4377 := by
  change Artifact.submissionArtifact.instructionPC (3104+1) = 4377
  rw [pc_succ Artifact.submissionArtifact 3104 (.push 2 9440) (by rfl), pc3211]
  rfl

@[simp] theorem pc3213 : Artifact.submissionArtifact.instructionPC 3106 = 4378 := by
  change Artifact.submissionArtifact.instructionPC (3105+1) = 4378
  rw [pc_succ Artifact.submissionArtifact 3105 (.op .MLOAD) (by rfl), pc3212]
  rfl

@[simp] theorem pc3214 : Artifact.submissionArtifact.instructionPC 3107 = 4379 := by
  change Artifact.submissionArtifact.instructionPC (3106+1) = 4379
  rw [pc_succ Artifact.submissionArtifact 3106 (.op .JUMPDEST) (by rfl), pc3213]
  rfl

@[simp] theorem pc3215 : Artifact.submissionArtifact.instructionPC 3108 = 4380 := by
  change Artifact.submissionArtifact.instructionPC (3107+1) = 4380
  rw [pc_succ Artifact.submissionArtifact 3107 (.op (.Dup ⟨0, by decide⟩)) (by rfl), pc3214]
  rfl

@[simp] theorem pc3216 : Artifact.submissionArtifact.instructionPC 3109 = 4381 := by
  change Artifact.submissionArtifact.instructionPC (3108+1) = 4381
  rw [pc_succ Artifact.submissionArtifact 3108 (.op .MLOAD) (by rfl), pc3215]
  rfl

@[simp] theorem pc3217 : Artifact.submissionArtifact.instructionPC 3110 = 4382 := by
  change Artifact.submissionArtifact.instructionPC (3109+1) = 4382
  rw [pc_succ Artifact.submissionArtifact 3109 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3216]
  rfl

@[simp] theorem pc3218 : Artifact.submissionArtifact.instructionPC 3111 = 4385 := by
  change Artifact.submissionArtifact.instructionPC (3110+1) = 4385
  rw [pc_succ Artifact.submissionArtifact 3110 (.push 2 8256) (by rfl), pc3217]
  rfl

@[simp] theorem pc3219 : Artifact.submissionArtifact.instructionPC 3112 = 4386 := by
  change Artifact.submissionArtifact.instructionPC (3111+1) = 4386
  rw [pc_succ Artifact.submissionArtifact 3111 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3218]
  rfl

@[simp] theorem pc3220 : Artifact.submissionArtifact.instructionPC 3113 = 4387 := by
  change Artifact.submissionArtifact.instructionPC (3112+1) = 4387
  rw [pc_succ Artifact.submissionArtifact 3112 (.op .SUB) (by rfl), pc3219]
  rfl

@[simp] theorem pc3221 : Artifact.submissionArtifact.instructionPC 3114 = 4388 := by
  change Artifact.submissionArtifact.instructionPC (3113+1) = 4388
  rw [pc_succ Artifact.submissionArtifact 3113 (.op .MLOAD) (by rfl), pc3220]
  rfl

@[simp] theorem pc3222 : Artifact.submissionArtifact.instructionPC 3115 = 4389 := by
  change Artifact.submissionArtifact.instructionPC (3114+1) = 4389
  rw [pc_succ Artifact.submissionArtifact 3114 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3221]
  rfl

@[simp] theorem pc3223 : Artifact.submissionArtifact.instructionPC 3116 = 4390 := by
  change Artifact.submissionArtifact.instructionPC (3115+1) = 4390
  rw [pc_succ Artifact.submissionArtifact 3115 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3222]
  rfl

@[simp] theorem pc3224 : Artifact.submissionArtifact.instructionPC 3117 = 4391 := by
  change Artifact.submissionArtifact.instructionPC (3116+1) = 4391
  rw [pc_succ Artifact.submissionArtifact 3116 (.op .GT) (by rfl), pc3223]
  rfl

@[simp] theorem pc3225 : Artifact.submissionArtifact.instructionPC 3118 = 4392 := by
  change Artifact.submissionArtifact.instructionPC (3117+1) = 4392
  rw [pc_succ Artifact.submissionArtifact 3117 (.op (.Swap ⟨1, by decide⟩)) (by rfl), pc3224]
  rfl

@[simp] theorem pc3226 : Artifact.submissionArtifact.instructionPC 3119 = 4393 := by
  change Artifact.submissionArtifact.instructionPC (3118+1) = 4393
  rw [pc_succ Artifact.submissionArtifact 3118 (.op .SUB) (by rfl), pc3225]
  rfl

@[simp] theorem pc3227 : Artifact.submissionArtifact.instructionPC 3120 = 4394 := by
  change Artifact.submissionArtifact.instructionPC (3119+1) = 4394
  rw [pc_succ Artifact.submissionArtifact 3119 (.op (.Dup ⟨3, by decide⟩)) (by rfl), pc3226]
  rfl

@[simp] theorem pc3228 : Artifact.submissionArtifact.instructionPC 3121 = 4395 := by
  change Artifact.submissionArtifact.instructionPC (3120+1) = 4395
  rw [pc_succ Artifact.submissionArtifact 3120 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3227]
  rfl

@[simp] theorem pc3229 : Artifact.submissionArtifact.instructionPC 3122 = 4396 := by
  change Artifact.submissionArtifact.instructionPC (3121+1) = 4396
  rw [pc_succ Artifact.submissionArtifact 3121 (.op .LT) (by rfl), pc3228]
  rfl

@[simp] theorem pc3230 : Artifact.submissionArtifact.instructionPC 3123 = 4397 := by
  change Artifact.submissionArtifact.instructionPC (3122+1) = 4397
  rw [pc_succ Artifact.submissionArtifact 3122 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3229]
  rfl

@[simp] theorem pc3231 : Artifact.submissionArtifact.instructionPC 3124 = 4398 := by
  change Artifact.submissionArtifact.instructionPC (3123+1) = 4398
  rw [pc_succ Artifact.submissionArtifact 3123 (.op (.Dup ⟨4, by decide⟩)) (by rfl), pc3230]
  rfl

@[simp] theorem pc3232 : Artifact.submissionArtifact.instructionPC 3125 = 4399 := by
  change Artifact.submissionArtifact.instructionPC (3124+1) = 4399
  rw [pc_succ Artifact.submissionArtifact 3124 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3231]
  rfl

@[simp] theorem pc3233 : Artifact.submissionArtifact.instructionPC 3126 = 4400 := by
  change Artifact.submissionArtifact.instructionPC (3125+1) = 4400
  rw [pc_succ Artifact.submissionArtifact 3125 (.op .SUB) (by rfl), pc3232]
  rfl

@[simp] theorem pc3234 : Artifact.submissionArtifact.instructionPC 3127 = 4401 := by
  change Artifact.submissionArtifact.instructionPC (3126+1) = 4401
  rw [pc_succ Artifact.submissionArtifact 3126 (.op (.Dup ⟨3, by decide⟩)) (by rfl), pc3233]
  rfl

@[simp] theorem pc3235 : Artifact.submissionArtifact.instructionPC 3128 = 4402 := by
  change Artifact.submissionArtifact.instructionPC (3127+1) = 4402
  rw [pc_succ Artifact.submissionArtifact 3127 (.op .MSTORE) (by rfl), pc3234]
  rfl

@[simp] theorem pc3236 : Artifact.submissionArtifact.instructionPC 3129 = 4403 := by
  change Artifact.submissionArtifact.instructionPC (3128+1) = 4403
  rw [pc_succ Artifact.submissionArtifact 3128 (.op .OR) (by rfl), pc3235]
  rfl

@[simp] theorem pc3237 : Artifact.submissionArtifact.instructionPC 3130 = 4404 := by
  change Artifact.submissionArtifact.instructionPC (3129+1) = 4404
  rw [pc_succ Artifact.submissionArtifact 3129 (.op (.Swap ⟨1, by decide⟩)) (by rfl), pc3236]
  rfl

@[simp] theorem pc3238 : Artifact.submissionArtifact.instructionPC 3131 = 4405 := by
  change Artifact.submissionArtifact.instructionPC (3130+1) = 4405
  rw [pc_succ Artifact.submissionArtifact 3130 (.op .POP) (by rfl), pc3237]
  rfl

@[simp] theorem pc3238_compact : Artifact.submissionArtifact.instructionPC 3132 = 4407 := by
  change Artifact.submissionArtifact.instructionPC (3131+1) = 4407
  rw [pc_succ Artifact.submissionArtifact 3131 (.push 1 31) (by rfl), pc3238]
  rfl

@[simp] theorem pc3239 : Artifact.submissionArtifact.instructionPC 3133 = 4408 := by
  change Artifact.submissionArtifact.instructionPC (3132+1) = 4408
  rw [pc_succ Artifact.submissionArtifact 3132 (.op .NOT) (by rfl), pc3238_compact]
  rfl

@[simp] theorem pc3240 : Artifact.submissionArtifact.instructionPC 3134 = 4409 := by
  change Artifact.submissionArtifact.instructionPC (3133+1) = 4409
  rw [pc_succ Artifact.submissionArtifact 3133 (.op .ADD) (by rfl), pc3239]
  rfl

@[simp] theorem pc3241 : Artifact.submissionArtifact.instructionPC 3135 = 4412 := by
  change Artifact.submissionArtifact.instructionPC (3134+1) = 4412
  rw [pc_succ Artifact.submissionArtifact 3134 (.push 2 8255) (by rfl), pc3240]
  rfl

@[simp] theorem pc3242 : Artifact.submissionArtifact.instructionPC 3136 = 4413 := by
  change Artifact.submissionArtifact.instructionPC (3135+1) = 4413
  rw [pc_succ Artifact.submissionArtifact 3135 (.op (.Dup ⟨1, by decide⟩)) (by rfl), pc3241]
  rfl

@[simp] theorem pc3243 : Artifact.submissionArtifact.instructionPC 3137 = 4414 := by
  change Artifact.submissionArtifact.instructionPC (3136+1) = 4414
  rw [pc_succ Artifact.submissionArtifact 3136 (.op .GT) (by rfl), pc3242]
  rfl

@[simp] theorem pc3244 : Artifact.submissionArtifact.instructionPC 3138 = 4417 := by
  change Artifact.submissionArtifact.instructionPC (3137+1) = 4417
  rw [pc_succ Artifact.submissionArtifact 3137 (.push 2 4378) (by rfl), pc3243]
  rfl

@[simp] theorem pc3245 : Artifact.submissionArtifact.instructionPC 3139 = 4418 := by
  change Artifact.submissionArtifact.instructionPC (3138+1) = 4418
  rw [pc_succ Artifact.submissionArtifact 3138 (.op .JUMPI) (by rfl), pc3244]
  rfl

@[simp] theorem pc3246 : Artifact.submissionArtifact.instructionPC 3140 = 4419 := by
  change Artifact.submissionArtifact.instructionPC (3139+1) = 4419
  rw [pc_succ Artifact.submissionArtifact 3139 (.op .POP) (by rfl), pc3245]
  rfl

@[simp] theorem pc3247 : Artifact.submissionArtifact.instructionPC 3141 = 4422 := by
  change Artifact.submissionArtifact.instructionPC (3140+1) = 4422
  rw [pc_succ Artifact.submissionArtifact 3140 (.push 2 8224) (by rfl), pc3246]
  rfl

@[simp] theorem pc3248 : Artifact.submissionArtifact.instructionPC 3142 = 4423 := by
  change Artifact.submissionArtifact.instructionPC (3141+1) = 4423
  rw [pc_succ Artifact.submissionArtifact 3141 (.op .MLOAD) (by rfl), pc3247]
  rfl

@[simp] theorem pc3249 : Artifact.submissionArtifact.instructionPC 3143 = 4424 := by
  change Artifact.submissionArtifact.instructionPC (3142+1) = 4424
  rw [pc_succ Artifact.submissionArtifact 3142 (.op .SUB) (by rfl), pc3248]
  rfl

@[simp] theorem pc3250 : Artifact.submissionArtifact.instructionPC 3144 = 4427 := by
  change Artifact.submissionArtifact.instructionPC (3143+1) = 4427
  rw [pc_succ Artifact.submissionArtifact 3143 (.push 2 8224) (by rfl), pc3249]
  rfl

@[simp] theorem pc3251 : Artifact.submissionArtifact.instructionPC 3145 = 4428 := by
  change Artifact.submissionArtifact.instructionPC (3144+1) = 4428
  rw [pc_succ Artifact.submissionArtifact 3144 (.op .MSTORE) (by rfl), pc3250]
  rfl

@[simp] theorem pc3252 : Artifact.submissionArtifact.instructionPC 3146 = 4431 := by
  change Artifact.submissionArtifact.instructionPC (3145+1) = 4431
  rw [pc_succ Artifact.submissionArtifact 3145 (.push 2 4363) (by rfl), pc3251]
  rfl

@[simp] theorem pc3253 : Artifact.submissionArtifact.instructionPC 3147 = 4432 := by
  change Artifact.submissionArtifact.instructionPC (3146+1) = 4432
  rw [pc_succ Artifact.submissionArtifact 3146 (.op .JUMP) (by rfl), pc3252]
  rfl

@[simp] theorem pc3254 : Artifact.submissionArtifact.instructionPC 3148 = 4433 := by
  change Artifact.submissionArtifact.instructionPC (3147+1) = 4433
  rw [pc_succ Artifact.submissionArtifact 3147 (.op .JUMPDEST) (by rfl), pc3253]
  rfl

@[simp] theorem pc3255 : Artifact.submissionArtifact.instructionPC 3149 = 4436 := by
  change Artifact.submissionArtifact.instructionPC (3148+1) = 4436
  rw [pc_succ Artifact.submissionArtifact 3148 (.push 2 4443) (by rfl), pc3254]
  rfl

@[simp] theorem pc3256 : Artifact.submissionArtifact.instructionPC 3150 = 4439 := by
  change Artifact.submissionArtifact.instructionPC (3149+1) = 4439
  rw [pc_succ Artifact.submissionArtifact 3149 (.push 2 2048) (by rfl), pc3255]
  rfl

@[simp] theorem pc3257 : Artifact.submissionArtifact.instructionPC 3151 = 4442 := by
  change Artifact.submissionArtifact.instructionPC (3150+1) = 4442
  rw [pc_succ Artifact.submissionArtifact 3150 (.push 2 2304) (by rfl), pc3256]
  rfl

@[simp] theorem pc3258 : Artifact.submissionArtifact.instructionPC 3152 = 4443 := by
  change Artifact.submissionArtifact.instructionPC (3151+1) = 4443
  rw [pc_succ Artifact.submissionArtifact 3151 (.op .JUMP) (by rfl), pc3257]
  rfl

@[simp] theorem pc3259 : Artifact.submissionArtifact.instructionPC 3153 = 4444 := by
  change Artifact.submissionArtifact.instructionPC (3152+1) = 4444
  rw [pc_succ Artifact.submissionArtifact 3152 (.op .JUMPDEST) (by rfl), pc3258]
  rfl

@[simp] theorem pc3260 : Artifact.submissionArtifact.instructionPC 3154 = 4446 := by
  change Artifact.submissionArtifact.instructionPC (3153+1) = 4446
  rw [pc_succ Artifact.submissionArtifact 3153 (.push 1 1) (by rfl), pc3259]
  rfl

@[simp] theorem pc3261 : Artifact.submissionArtifact.instructionPC 3155 = 4447 := by
  change Artifact.submissionArtifact.instructionPC (3154+1) = 4447
  rw [pc_succ Artifact.submissionArtifact 3154 (.op (.Swap ⟨0, by decide⟩)) (by rfl), pc3260]
  rfl

@[simp] theorem pc3262 : Artifact.submissionArtifact.instructionPC 3156 = 4448 := by
  change Artifact.submissionArtifact.instructionPC (3155+1) = 4448
  rw [pc_succ Artifact.submissionArtifact 3155 (.op .SUB) (by rfl), pc3261]
  rfl

@[simp] theorem pc3263 : Artifact.submissionArtifact.instructionPC 3157 = 4451 := by
  change Artifact.submissionArtifact.instructionPC (3156+1) = 4451
  rw [pc_succ Artifact.submissionArtifact 3156 (.push 2 4017) (by rfl), pc3262]
  rfl

@[simp] theorem pc3264 : Artifact.submissionArtifact.instructionPC 3158 = 4452 := by
  change Artifact.submissionArtifact.instructionPC (3157+1) = 4452
  rw [pc_succ Artifact.submissionArtifact 3157 (.op .JUMP) (by rfl), pc3263]
  rfl

@[simp] theorem pc3265 : Artifact.submissionArtifact.instructionPC 3159 = 4453 := by
  change Artifact.submissionArtifact.instructionPC (3158+1) = 4453
  rw [pc_succ Artifact.submissionArtifact 3158 (.op .JUMPDEST) (by rfl), pc3264]
  rfl

@[simp] theorem pc3266 : Artifact.submissionArtifact.instructionPC 3160 = 4454 := by
  change Artifact.submissionArtifact.instructionPC (3159+1) = 4454
  rw [pc_succ Artifact.submissionArtifact 3159 (.op .POP) (by rfl), pc3265]
  rfl

@[simp] theorem pc3267 : Artifact.submissionArtifact.instructionPC 3161 = 4457 := by
  change Artifact.submissionArtifact.instructionPC (3160+1) = 4457
  rw [pc_succ Artifact.submissionArtifact 3160 (.push 2 1756) (by rfl), pc3266]
  rfl

@[simp] theorem pcSaturate2987 : Artifact.submissionArtifact.instructionPC 2959 = 4098 := by rfl

@[simp] theorem pcSaturate2988 : Artifact.submissionArtifact.instructionPC 2960 = 4099 := by
  change Artifact.submissionArtifact.instructionPC (2959+1) = 4099
  rw [pc_succ Artifact.submissionArtifact 2959 (.op .MLOAD) (by rfl), pcSaturate2987]
  rfl

@[simp] theorem pcSaturate2989 : Artifact.submissionArtifact.instructionPC 2961 = 4100 := by
  change Artifact.submissionArtifact.instructionPC (2960+1) = 4100
  rw [pc_succ Artifact.submissionArtifact 2960 (.op .JUMPDEST) (by rfl), pcSaturate2988]
  rfl

@[simp] theorem pcSaturate2990 : Artifact.submissionArtifact.instructionPC 2962 = 4101 := by
  change Artifact.submissionArtifact.instructionPC (2961+1) = 4101
  rw [pc_succ Artifact.submissionArtifact 2961 (.op .GT) (by rfl), pcSaturate2989]
  rfl

@[simp] theorem pcSaturate2991 : Artifact.submissionArtifact.instructionPC 2963 = 4102 := by
  change Artifact.submissionArtifact.instructionPC (2962+1) = 4102
  rw [pc_succ Artifact.submissionArtifact 2962 (.op .ISZERO) (by rfl), pcSaturate2990]
  rfl

@[simp] theorem pcSaturate2992 : Artifact.submissionArtifact.instructionPC 2964 = 4103 := by
  change Artifact.submissionArtifact.instructionPC (2963+1) = 4103
  rw [pc_succ Artifact.submissionArtifact 2963 (.push 0 0) (by rfl), pcSaturate2991]
  rfl

@[simp] theorem pcSaturate2993 : Artifact.submissionArtifact.instructionPC 2965 = 4104 := by
  change Artifact.submissionArtifact.instructionPC (2964+1) = 4104
  rw [pc_succ Artifact.submissionArtifact 2964 (.op .SUB) (by rfl), pcSaturate2992]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

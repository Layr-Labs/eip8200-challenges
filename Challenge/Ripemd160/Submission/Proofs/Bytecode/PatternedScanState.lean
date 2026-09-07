import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-!
# States and paths of the scalar-SWAR patterned-1000 guard

The guard carries the expected word forward instead of storing thirty-two of
them, so the scan is one loop: `wordPath` derives the word and routes the four
straddling offsets to `straddlePath`, and `comparePath` folds the difference
into the accumulator and advances the offset and the scalar.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/-- Push the five constants and start the scan. -/
def setupPath : List Located :=
  [opAt 2870 .JUMPDEST,
   pushAt 2871 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 2872 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 2873 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 2874 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 2875 (.Dup ⟨2, by decide⟩), opAt 2876 (.Dup ⟨2, by decide⟩),
   opAt 2877 .AND, pushAt 2878 0 0, pushAt 2879 0 0, pushAt 2880 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 2881 .JUMPDEST, opAt 2882 (.Dup ⟨0, by decide⟩),
   opAt 2883 (.Dup ⟨5, by decide⟩), opAt 2884 .MUL,
   opAt 2885 (.Dup ⟨0, by decide⟩), opAt 2886 (.Dup ⟨7, by decide⟩),
   opAt 2887 .AND, opAt 2888 (.Dup ⟨5, by decide⟩), opAt 2889 .ADD,
   opAt 2890 (.Dup ⟨1, by decide⟩), opAt 2891 (.Dup ⟨9, by decide⟩),
   opAt 2892 .XOR, opAt 2893 (.Dup ⟨10, by decide⟩), opAt 2894 .AND,
   opAt 2895 .XOR, opAt 2896 (.Dup ⟨3, by decide⟩), pushAt 2897 1 0xff,
   opAt 2898 .AND, pushAt 2899 1 0xe0, opAt 2900 .EQ, pushAt 2901 2 0x164b,
   opAt 2902 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 2903 .JUMPDEST, opAt 2904 (.Dup ⟨3, by decide⟩),
   opAt 2905 .CALLDATALOAD, opAt 2906 .XOR, opAt 2907 (.Dup ⟨4, by decide⟩),
   opAt 2908 .OR, opAt 2909 (.Swap ⟨3, by decide⟩), opAt 2910 .POP,
   opAt 2911 .POP, opAt 2912 (.Dup ⟨0, by decide⟩), pushAt 2913 1 0xa0,
   opAt 2914 .ADD, pushAt 2915 1 0xff, opAt 2916 .AND,
   opAt 2917 (.Swap ⟨0, by decide⟩), opAt 2918 .POP,
   opAt 2919 (.Dup ⟨1, by decide⟩), pushAt 2920 1 0x20, opAt 2921 .ADD,
   opAt 2922 (.Swap ⟨1, by decide⟩), opAt 2923 .POP,
   opAt 2924 (.Dup ⟨1, by decide⟩), pushAt 2925 2 0x03e0, opAt 2926 .GT,
   pushAt 2927 2 0x15d3, opAt 2928 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 2929 2 0x03e0, opAt 2930 .CALLDATALOAD,
   pushAt 2931 8 0x88add2f71c41668b, pushAt 2932 1 0xc0, opAt 2933 .SHL,
   opAt 2934 .XOR, opAt 2935 (.Dup ⟨3, by decide⟩), opAt 2936 .OR,
   opAt 2937 (.Swap ⟨2, by decide⟩), opAt 2938 .POP,
   opAt 2939 (.Swap ⟨1, by decide⟩), opAt 2940 (.Swap ⟨6, by decide⟩),
   opAt 2941 .POP, opAt 2942 .POP, opAt 2943 .POP, opAt 2944 .POP,
   opAt 2945 .POP, opAt 2946 .POP, opAt 2947 .POP, pushAt 2948 2 0x03ee,
   opAt 2949 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 2950 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 2951 0 0, opAt 2952 .MSTORE, pushAt 2953 1 0x20, pushAt 2954 0 0,
   opAt 2955 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 2956 .JUMPDEST, opAt 2957 (.Dup ⟨6, by decide⟩),
   opAt 2958 (.Dup ⟨4, by decide⟩), pushAt 2959 1 0x08, opAt 2960 .SHR,
   pushAt 2961 1 0x05, opAt 2962 .MUL, pushAt 2963 1 0x1b, opAt 2964 .SUB,
   pushAt 2965 1 0x08, opAt 2966 .MUL, opAt 2967 .SHR, pushAt 2968 1 0x0b,
   opAt 2969 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 2970 (.Dup ⟨1, by decide⟩), opAt 2971 (.Dup ⟨9, by decide⟩),
   opAt 2972 .AND, opAt 2973 (.Dup ⟨1, by decide⟩), opAt 2974 .ADD,
   opAt 2975 (.Dup ⟨2, by decide⟩), opAt 2976 (.Dup ⟨12, by decide⟩),
   opAt 2977 .AND, opAt 2978 .XOR, opAt 2979 (.Swap ⟨1, by decide⟩),
   opAt 2980 .POP, opAt 2981 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 2982 (.Dup ⟨2, by decide⟩), pushAt 2983 1 0x0b, opAt 2984 .ADD,
   opAt 2985 (.Swap ⟨2, by decide⟩), opAt 2986 .POP, pushAt 2987 2 0x15ed,
   opAt 2988 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2870 = 5448 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2871 = 5449 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2872 = 5482 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2873 = 5515 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2874 = 5548 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2875 = 5581 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2876 = 5582 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2877 = 5583 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2878 = 5584 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2879 = 5585 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2880 = 5586 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2881 = 5587 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2882 = 5588 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2883 = 5589 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2884 = 5590 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2885 = 5591 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2886 = 5592 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2887 = 5593 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2888 = 5594 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2889 = 5595 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2890 = 5596 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2891 = 5597 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2892 = 5598 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2893 = 5599 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2894 = 5600 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2895 = 5601 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2896 = 5602 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2897 = 5603 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2898 = 5605 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2899 = 5606 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2900 = 5608 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2901 = 5609 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2902 = 5612 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2903 = 5613 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2904 = 5614 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2905 = 5615 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2906 = 5616 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2907 = 5617 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2908 = 5618 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2909 = 5619 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2910 = 5620 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2911 = 5621 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2912 = 5622 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2913 = 5623 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2914 = 5625 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2915 = 5626 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2916 = 5628 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 2917 = 5629 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 2918 = 5630 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 2919 = 5631 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 2920 = 5632 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 2921 = 5634 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 2922 = 5635 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 2923 = 5636 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 2924 = 5637 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 2925 = 5638 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 2926 = 5641 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 2927 = 5642 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 2928 = 5645 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 2929 = 5646 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 2930 = 5649 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 2931 = 5650 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 2932 = 5659 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 2933 = 5661 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 2934 = 5662 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 2935 = 5663 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 2936 = 5664 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 2937 = 5665 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 2938 = 5666 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 2939 = 5667 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 2940 = 5668 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 2941 = 5669 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 2942 = 5670 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 2943 = 5671 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 2944 = 5672 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 2945 = 5673 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 2946 = 5674 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 2947 = 5675 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 2948 = 5676 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 2949 = 5679 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 2950 = 5680 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 2951 = 5701 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 2952 = 5702 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 2953 = 5703 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 2954 = 5705 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 2955 = 5706 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 2956 = 5707 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 2957 = 5708 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 2958 = 5709 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 2959 = 5710 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 2960 = 5712 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 2961 = 5713 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 2962 = 5715 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 2963 = 5716 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 2964 = 5718 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 2965 = 5719 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 2966 = 5721 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 2967 = 5722 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 2968 = 5723 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 2969 = 5725 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 2970 = 5726 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 2971 = 5727 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 2972 = 5728 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 2973 = 5729 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 2974 = 5730 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 2975 = 5731 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 2976 = 5732 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 2977 = 5733 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 2978 = 5734 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 2979 = 5735 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 2980 = 5736 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 2981 = 5737 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 2982 = 5738 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 2983 = 5739 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 2984 = 5741 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 2985 = 5742 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 2986 = 5743 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 2987 = 5744 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 2988 = 5747 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

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
  [opAt 2590 .JUMPDEST,
   pushAt 2591 32 0x8080808080808080808080808080808080808080808080808080808080808080,
   pushAt 2592 32 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82,
   pushAt 2593 32 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f,
   pushAt 2594 32 0x0101010101010101010101010101010101010101010101010101010101010101,
   opAt 2595 (.Dup ⟨2, by decide⟩), opAt 2596 (.Dup ⟨2, by decide⟩),
   opAt 2597 .AND, pushAt 2598 0 0, pushAt 2599 0 0, pushAt 2600 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 2601 .JUMPDEST, opAt 2602 (.Dup ⟨0, by decide⟩),
   opAt 2603 (.Dup ⟨5, by decide⟩), opAt 2604 .MUL,
   opAt 2605 (.Dup ⟨0, by decide⟩), opAt 2606 (.Dup ⟨7, by decide⟩),
   opAt 2607 .AND, opAt 2608 (.Dup ⟨5, by decide⟩), opAt 2609 .ADD,
   opAt 2610 (.Dup ⟨1, by decide⟩), opAt 2611 (.Dup ⟨9, by decide⟩),
   opAt 2612 .XOR, opAt 2613 (.Dup ⟨10, by decide⟩), opAt 2614 .AND,
   opAt 2615 .XOR, opAt 2616 (.Dup ⟨3, by decide⟩), pushAt 2617 1 0xff,
   opAt 2618 .AND, pushAt 2619 1 0xe0, opAt 2620 .EQ, pushAt 2621 2 0x14d3,
   opAt 2622 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 2623 .JUMPDEST, opAt 2624 (.Dup ⟨3, by decide⟩),
   opAt 2625 .CALLDATALOAD, opAt 2626 .XOR, opAt 2627 (.Dup ⟨4, by decide⟩),
   opAt 2628 .OR, opAt 2629 (.Swap ⟨3, by decide⟩), opAt 2630 .POP,
   opAt 2631 .POP, opAt 2632 (.Dup ⟨0, by decide⟩), pushAt 2633 1 0xa0,
   opAt 2634 .ADD, pushAt 2635 1 0xff, opAt 2636 .AND,
   opAt 2637 (.Swap ⟨0, by decide⟩), opAt 2638 .POP,
   opAt 2639 (.Dup ⟨1, by decide⟩), pushAt 2640 1 0x20, opAt 2641 .ADD,
   opAt 2642 (.Swap ⟨1, by decide⟩), opAt 2643 .POP,
   opAt 2644 (.Dup ⟨1, by decide⟩), pushAt 2645 2 0x03e0, opAt 2646 .GT,
   pushAt 2647 2 0x145b, opAt 2648 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 2649 2 0x03e0, opAt 2650 .CALLDATALOAD,
   pushAt 2651 8 0x88add2f71c41668b, pushAt 2652 1 0xc0, opAt 2653 .SHL,
   opAt 2654 .XOR, opAt 2655 (.Dup ⟨3, by decide⟩), opAt 2656 .OR,
   opAt 2657 (.Swap ⟨2, by decide⟩), opAt 2658 .POP,
   opAt 2659 (.Swap ⟨1, by decide⟩), opAt 2660 (.Swap ⟨6, by decide⟩),
   opAt 2661 .POP, opAt 2662 .POP, opAt 2663 .POP, opAt 2664 .POP,
   opAt 2665 .POP, opAt 2666 .POP, opAt 2667 .POP, pushAt 2668 2 0x289,
   opAt 2669 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 2670 20 0x863c598588bd72a4babf36c6bb01f27bbdc0ecd4,
   pushAt 2671 0 0, opAt 2672 .MSTORE, pushAt 2673 1 0x20, pushAt 2674 0 0,
   opAt 2675 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 2676 .JUMPDEST, opAt 2677 (.Dup ⟨6, by decide⟩),
   opAt 2678 (.Dup ⟨4, by decide⟩), pushAt 2679 1 0x08, opAt 2680 .SHR,
   pushAt 2681 1 0x05, opAt 2682 .MUL, pushAt 2683 1 0x1b, opAt 2684 .SUB,
   pushAt 2685 1 0x08, opAt 2686 .MUL, opAt 2687 .SHR, pushAt 2688 1 0x0b,
   opAt 2689 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 2690 (.Dup ⟨1, by decide⟩), opAt 2691 (.Dup ⟨9, by decide⟩),
   opAt 2692 .AND, opAt 2693 (.Dup ⟨1, by decide⟩), opAt 2694 .ADD,
   opAt 2695 (.Dup ⟨2, by decide⟩), opAt 2696 (.Dup ⟨12, by decide⟩),
   opAt 2697 .AND, opAt 2698 .XOR, opAt 2699 (.Swap ⟨1, by decide⟩),
   opAt 2700 .POP, opAt 2701 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 2702 (.Dup ⟨2, by decide⟩), pushAt 2703 1 0x0b, opAt 2704 .ADD,
   opAt 2705 (.Swap ⟨2, by decide⟩), opAt 2706 .POP, pushAt 2707 2 0x1475,
   opAt 2708 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 2590 = 5072 := by rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 2591 = 5073 := by rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 2592 = 5106 := by rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 2593 = 5139 := by rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 2594 = 5172 := by rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 2595 = 5205 := by rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 2596 = 5206 := by rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 2597 = 5207 := by rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 2598 = 5208 := by rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 2599 = 5209 := by rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 2600 = 5210 := by rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 2601 = 5211 := by rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 2602 = 5212 := by rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 2603 = 5213 := by rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 2604 = 5214 := by rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 2605 = 5215 := by rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 2606 = 5216 := by rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 2607 = 5217 := by rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 2608 = 5218 := by rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 2609 = 5219 := by rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 2610 = 5220 := by rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 2611 = 5221 := by rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 2612 = 5222 := by rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 2613 = 5223 := by rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 2614 = 5224 := by rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 2615 = 5225 := by rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 2616 = 5226 := by rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 2617 = 5227 := by rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 2618 = 5229 := by rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 2619 = 5230 := by rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 2620 = 5232 := by rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 2621 = 5233 := by rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 2622 = 5236 := by rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 2623 = 5237 := by rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 2624 = 5238 := by rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 2625 = 5239 := by rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 2626 = 5240 := by rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 2627 = 5241 := by rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 2628 = 5242 := by rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 2629 = 5243 := by rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 2630 = 5244 := by rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 2631 = 5245 := by rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 2632 = 5246 := by rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 2633 = 5247 := by rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 2634 = 5249 := by rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 2635 = 5250 := by rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 2636 = 5252 := by rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 2637 = 5253 := by rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 2638 = 5254 := by rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 2639 = 5255 := by rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 2640 = 5256 := by rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 2641 = 5258 := by rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 2642 = 5259 := by rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 2643 = 5260 := by rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 2644 = 5261 := by rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 2645 = 5262 := by rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 2646 = 5265 := by rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 2647 = 5266 := by rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 2648 = 5269 := by rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 2649 = 5270 := by rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 2650 = 5273 := by rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 2651 = 5274 := by rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 2652 = 5283 := by rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 2653 = 5285 := by rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 2654 = 5286 := by rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 2655 = 5287 := by rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 2656 = 5288 := by rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 2657 = 5289 := by rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 2658 = 5290 := by rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 2659 = 5291 := by rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 2660 = 5292 := by rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 2661 = 5293 := by rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 2662 = 5294 := by rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 2663 = 5295 := by rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 2664 = 5296 := by rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 2665 = 5297 := by rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 2666 = 5298 := by rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 2667 = 5299 := by rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 2668 = 5300 := by rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 2669 = 5303 := by rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 2670 = 5304 := by rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 2671 = 5325 := by rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 2672 = 5326 := by rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 2673 = 5327 := by rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 2674 = 5329 := by rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 2675 = 5330 := by rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 2676 = 5331 := by rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 2677 = 5332 := by rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 2678 = 5333 := by rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 2679 = 5334 := by rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 2680 = 5336 := by rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 2681 = 5337 := by rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 2682 = 5339 := by rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 2683 = 5340 := by rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 2684 = 5342 := by rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 2685 = 5343 := by rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 2686 = 5345 := by rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 2687 = 5346 := by rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 2688 = 5347 := by rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 2689 = 5349 := by rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 2690 = 5350 := by rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 2691 = 5351 := by rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 2692 = 5352 := by rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 2693 = 5353 := by rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 2694 = 5354 := by rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 2695 = 5355 := by rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 2696 = 5356 := by rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 2697 = 5357 := by rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 2698 = 5358 := by rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 2699 = 5359 := by rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 2700 = 5360 := by rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 2701 = 5361 := by rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 2702 = 5362 := by rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 2703 = 5363 := by rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 2704 = 5365 := by rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 2705 = 5366 := by rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 2706 = 5367 := by rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 2707 = 5368 := by rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 2708 = 5371 := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

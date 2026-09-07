import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The correction a straddling word takes

The offsets with `o &&& 255 = 224` cross a step of `i / 251`, so their expected
word takes one further bytewise add.  The constant is shifted out of `M` rather
than stored, and the same crossing bumps the running scalar by eleven.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

theorem hdest5170 : Decode.isValidJumpDest submissionBytecode 5613 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2903 (by rfl)

/-- The correction block, with every stack slot symbolic. -/
def gasSteps_straddle_sym (input : ByteArray) (E S sv ov acc : UInt256) :
    GasSteps (stS input 5707 [E, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5613 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8]) := by
  have step2989 := soundS (opAt 2956 .JUMPDEST)
    (blockOfS _ (pcFactS input 2956 5707 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2989)
      (stepS_jumpdest input 5707 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2990 := soundS (opAt 2957 (.Dup ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 2957 5708 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2990)
      (stepS_dup input 5708 6 (by decide) [E, S, sv, ov, acc, P7, M, m7, P, m8] (M) (by rfl) (by simp) (by norm_num)))
  have step2991 := soundS (opAt 2958 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 2958 5709 [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2991)
      (stepS_dup input 5709 4 (by decide) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2992 := soundS (pushAt 2959 1 0x08)
    (blockOfS _ (pcFactS input 2959 5710 [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2992)
      (stepS_push input 5710 1 (8 : UInt256) [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2993 := soundS (opAt 2960 .SHR)
    (blockOfS _ (pcFactS input 2960 5712 [(8 : UInt256), ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2993)
      (stepS_shr input 5712 ((8 : UInt256)) (ov) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2994 := soundS (pushAt 2961 1 0x05)
    (blockOfS _ (pcFactS input 2961 5713 [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2994)
      (stepS_push input 5713 1 (5 : UInt256) [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2995 := soundS (opAt 2962 .MUL)
    (blockOfS _ (pcFactS input 2962 5715 [(5 : UInt256), (UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2995)
      (stepS_mul input 5715 ((5 : UInt256)) ((UInt256.shiftRight ov (8 : UInt256))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2996 := soundS (pushAt 2963 1 0x1b)
    (blockOfS _ (pcFactS input 2963 5716 [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2996)
      (stepS_push input 5716 1 (27 : UInt256) [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2997 := soundS (opAt 2964 .SUB)
    (blockOfS _ (pcFactS input 2964 5718 [(27 : UInt256), ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2997)
      (stepS_sub input 5718 ((27 : UInt256)) (((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2998 := soundS (pushAt 2965 1 0x08)
    (blockOfS _ (pcFactS input 2965 5719 [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2998)
      (stepS_push input 5719 1 (8 : UInt256) [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2999 := soundS (opAt 2966 .MUL)
    (blockOfS _ (pcFactS input 2966 5721 [(8 : UInt256), ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2999)
      (stepS_mul input 5721 ((8 : UInt256)) (((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3000 := soundS (opAt 2967 .SHR)
    (blockOfS _ (pcFactS input 2967 5722 [((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3000)
      (stepS_shr input 5722 (((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))) (M) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3001 := soundS (pushAt 2968 1 0x0b)
    (blockOfS _ (pcFactS input 2968 5723 [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3001)
      (stepS_push input 5723 1 (11 : UInt256) [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3002 := soundS (opAt 2969 .MUL)
    (blockOfS _ (pcFactS input 2969 5725 [(11 : UInt256), (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3002)
      (stepS_mul input 5725 ((11 : UInt256)) ((UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3003 := soundS (opAt 2970 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2970 5726 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3003)
      (stepS_dup input 5726 1 (by decide) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3004 := soundS (opAt 2971 (.Dup ⟨9, by decide⟩))
    (blockOfS _ (pcFactS input 2971 5727 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3004)
      (stepS_dup input 5727 9 (by decide) [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m7) (by rfl) (by simp) (by norm_num)))
  have step3005 := soundS (opAt 2972 .AND)
    (blockOfS _ (pcFactS input 2972 5728 [m7, E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3005)
      (stepS_and input 5728 (m7) (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3006 := soundS (opAt 2973 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2973 5729 [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3006)
      (stepS_dup input 5729 1 (by decide) [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) (by rfl) (by simp) (by norm_num)))
  have step3007 := soundS (opAt 2974 .ADD)
    (blockOfS _ (pcFactS input 2974 5730 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3007)
      (stepS_add input 5730 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) ((UInt256.land m7 E)) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3008 := soundS (opAt 2975 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 2975 5731 [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3008)
      (stepS_dup input 5731 2 (by decide) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3009 := soundS (opAt 2976 (.Dup ⟨12, by decide⟩))
    (blockOfS _ (pcFactS input 2976 5732 [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3009)
      (stepS_dup input 5732 12 (by decide) [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m8) (by rfl) (by simp) (by norm_num)))
  have step3010 := soundS (opAt 2977 .AND)
    (blockOfS _ (pcFactS input 2977 5733 [m8, E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3010)
      (stepS_and input 5733 (m8) (E) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3011 := soundS (opAt 2978 .XOR)
    (blockOfS _ (pcFactS input 2978 5734 [(UInt256.land m8 E), (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3011)
      (stepS_xor input 5734 ((UInt256.land m8 E)) ((((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3012 := soundS (opAt 2979 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2979 5735 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3012)
      (stepS_swap input 5735 1 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3013 := soundS (opAt 2980 .POP)
    (blockOfS _ (pcFactS input 2980 5736 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3013)
      (stepS_pop input 5736 (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3014 := soundS (opAt 2981 .POP)
    (blockOfS _ (pcFactS input 2981 5737 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3014)
      (stepS_pop input 5737 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3015 := soundS (opAt 2982 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 2982 5738 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3015)
      (stepS_dup input 5738 2 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (sv) (by rfl) (by simp) (by norm_num)))
  have step3016 := soundS (pushAt 2983 1 0x0b)
    (blockOfS _ (pcFactS input 2983 5739 [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3016)
      (stepS_push input 5739 1 (11 : UInt256) [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3017 := soundS (opAt 2984 .ADD)
    (blockOfS _ (pcFactS input 2984 5741 [(11 : UInt256), sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3017)
      (stepS_add input 5741 ((11 : UInt256)) (sv) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3018 := soundS (opAt 2985 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 2985 5742 [((11 : UInt256) + sv), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3018)
      (stepS_swap input 5742 2 (by decide) [((11 : UInt256) + sv), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3019 := soundS (opAt 2986 .POP)
    (blockOfS _ (pcFactS input 2986 5743 [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3019)
      (stepS_pop input 5743 (sv) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3020 := soundS (pushAt 2987 2 0x15ed)
    (blockOfS _ (pcFactS input 2987 5744 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3020)
      (stepS_push input 5744 2 (5613 : UInt256) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3021 := soundS (opAt 2988 .JUMP)
    (blockOfS _ (pcFactS input 2988 5747 [(5613 : UInt256), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3021)
      (stepS_jump input 5747 5613 ((5613 : UInt256)) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num) rfl hdest5170))
  exact step2989.trans (step2990.trans (step2991.trans (step2992.trans (step2993.trans (step2994.trans (step2995.trans (step2996.trans (step2997.trans (step2998.trans (step2999.trans (step3000.trans (step3001.trans (step3002.trans (step3003.trans (step3004.trans (step3005.trans (step3006.trans (step3007.trans (step3008.trans (step3009.trans (step3010.trans (step3011.trans (step3012.trans (step3013.trans (step3014.trans (step3015.trans (step3016.trans (step3017.trans (step3018.trans (step3019.trans (step3020.trans (step3021))))))))))))))))))))))))))))))))

/-- The running scalar never leaves a byte. -/
theorem scalarAt_lt (k : Nat) : scalarAt k < 256 := by
  cases k with
  | zero => decide
  | succ n => exact Nat.mod_lt _ (by norm_num)

/-- A straddling offset takes the correction and rejoins the scan with the
scalar bumped by eleven. -/
def gasSteps_straddle (input : ByteArray) (k : Nat) (a : UInt256)
    (h : (32 * k) % 256 = 224) :
    GasSteps (straddleState input k a)
      (compareState input k (11 + scalarAt k) a) := by
  have hgw : guardWord k =
      straddleAdd (rawWord k) (straddleCorrection (UInt256.ofNat (32 * k))) := by
    unfold guardWord
    rw [if_pos (by simpa using h)]
  have hs : UInt256.ofNat (11 + scalarAt k) =
      (11 : UInt256) + UInt256.ofNat (scalarAt k) :=
    (Challenge.EvmProof.Word.ofNat_add_ofNat
      (by have := scalarAt_lt k; omega)).symm
  have hstart : straddleState input k a =
      stS input 5707 [rawWord k, UInt256.mul M (UInt256.ofNat (scalarAt k)),
        UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a,
        P7, M, m7, P, m8] := rfl
  have hend : compareState input k (11 + scalarAt k) a =
      stS input 5613 [straddleAdd (rawWord k)
          (straddleCorrection (UInt256.ofNat (32 * k))),
        UInt256.mul M (UInt256.ofNat (scalarAt k)),
        (11 : UInt256) + UInt256.ofNat (scalarAt k),
        UInt256.ofNat (32 * k), a, P7, M, m7, P, m8] := by
    unfold compareState stS frame
    rw [hgw, hs]
  rw [hstart, hend]
  exact gasSteps_straddle_sym input (rawWord k)
    (UInt256.mul M (UInt256.ofNat (scalarAt k))) (UInt256.ofNat (scalarAt k))
    (UInt256.ofNat (32 * k)) a


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

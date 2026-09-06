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

theorem hdest5170 : Decode.isValidJumpDest submissionBytecode 5237 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2923 (by rfl)

/-- The correction block, with every stack slot symbolic. -/
def gasSteps_straddle_sym (input : ByteArray) (E S sv ov acc : UInt256) :
    GasSteps (stS input 5331 [E, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5237 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8]) := by
  have step2989 := soundS (opAt 2976 .JUMPDEST)
    (blockOfS _ (pcFactS input 2976 5331 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2989)
      (stepS_jumpdest input 5331 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2990 := soundS (opAt 2977 (.Dup ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 2977 5332 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2990)
      (stepS_dup input 5332 6 (by decide) [E, S, sv, ov, acc, P7, M, m7, P, m8] (M) (by rfl) (by simp) (by norm_num)))
  have step2991 := soundS (opAt 2978 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 2978 5333 [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2991)
      (stepS_dup input 5333 4 (by decide) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2992 := soundS (pushAt 2979 1 0x08)
    (blockOfS _ (pcFactS input 2979 5334 [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2992)
      (stepS_push input 5334 1 (8 : UInt256) [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2993 := soundS (opAt 2980 .SHR)
    (blockOfS _ (pcFactS input 2980 5336 [(8 : UInt256), ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2993)
      (stepS_shr input 5336 ((8 : UInt256)) (ov) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2994 := soundS (pushAt 2981 1 0x05)
    (blockOfS _ (pcFactS input 2981 5337 [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2994)
      (stepS_push input 5337 1 (5 : UInt256) [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2995 := soundS (opAt 2982 .MUL)
    (blockOfS _ (pcFactS input 2982 5339 [(5 : UInt256), (UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2995)
      (stepS_mul input 5339 ((5 : UInt256)) ((UInt256.shiftRight ov (8 : UInt256))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2996 := soundS (pushAt 2983 1 0x1b)
    (blockOfS _ (pcFactS input 2983 5340 [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2996)
      (stepS_push input 5340 1 (27 : UInt256) [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2997 := soundS (opAt 2984 .SUB)
    (blockOfS _ (pcFactS input 2984 5342 [(27 : UInt256), ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2997)
      (stepS_sub input 5342 ((27 : UInt256)) (((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2998 := soundS (pushAt 2985 1 0x03)
    (blockOfS _ (pcFactS input 2985 5343 [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2998)
      (stepS_push input 5343 1 (3 : UInt256) [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2999 := soundS (opAt 2986 .SHL)
    (blockOfS _ (pcFactS input 2986 5345 [(3 : UInt256), ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2999)
      (by
        simpa only [shiftLeft_three_eq_mul_eight] using
          (stepS_shl input 5345 ((3 : UInt256))
            (((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))
            [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3000 := soundS (opAt 2987 .SHR)
    (blockOfS _ (pcFactS input 2987 5346 [((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3000)
      (stepS_shr input 5346 (((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))) (M) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3001 := soundS (pushAt 2988 1 0x0b)
    (blockOfS _ (pcFactS input 2988 5347 [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3001)
      (stepS_push input 5347 1 (11 : UInt256) [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3002 := soundS (opAt 2989 .MUL)
    (blockOfS _ (pcFactS input 2989 5349 [(11 : UInt256), (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3002)
      (stepS_mul input 5349 ((11 : UInt256)) ((UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3003 := soundS (opAt 2990 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2990 5350 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3003)
      (stepS_dup input 5350 1 (by decide) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3004 := soundS (opAt 2991 (.Dup ⟨9, by decide⟩))
    (blockOfS _ (pcFactS input 2991 5351 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3004)
      (stepS_dup input 5351 9 (by decide) [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m7) (by rfl) (by simp) (by norm_num)))
  have step3005 := soundS (opAt 2992 .AND)
    (blockOfS _ (pcFactS input 2992 5352 [m7, E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3005)
      (stepS_and input 5352 (m7) (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3006 := soundS (opAt 2993 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2993 5353 [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3006)
      (stepS_dup input 5353 1 (by decide) [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) (by rfl) (by simp) (by norm_num)))
  have step3007 := soundS (opAt 2994 .ADD)
    (blockOfS _ (pcFactS input 2994 5354 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3007)
      (stepS_add input 5354 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) ((UInt256.land m7 E)) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3008 := soundS (opAt 2995 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 2995 5355 [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3008)
      (stepS_dup input 5355 2 (by decide) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3009 := soundS (opAt 2996 (.Dup ⟨12, by decide⟩))
    (blockOfS _ (pcFactS input 2996 5356 [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3009)
      (stepS_dup input 5356 12 (by decide) [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m8) (by rfl) (by simp) (by norm_num)))
  have step3010 := soundS (opAt 2997 .AND)
    (blockOfS _ (pcFactS input 2997 5357 [m8, E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3010)
      (stepS_and input 5357 (m8) (E) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3011 := soundS (opAt 2998 .XOR)
    (blockOfS _ (pcFactS input 2998 5358 [(UInt256.land m8 E), (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3011)
      (stepS_xor input 5358 ((UInt256.land m8 E)) ((((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3012 := soundS (opAt 2999 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2999 5359 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3012)
      (stepS_swap input 5359 1 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3013 := soundS (opAt 3000 .POP)
    (blockOfS _ (pcFactS input 3000 5360 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3013)
      (stepS_pop input 5360 (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3014 := soundS (opAt 3001 .POP)
    (blockOfS _ (pcFactS input 3001 5361 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3014)
      (stepS_pop input 5361 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3015 := soundS (opAt 3002 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 3002 5362 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3015)
      (stepS_dup input 5362 2 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (sv) (by rfl) (by simp) (by norm_num)))
  have step3016 := soundS (pushAt 3003 1 0x0b)
    (blockOfS _ (pcFactS input 3003 5363 [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3016)
      (stepS_push input 5363 1 (11 : UInt256) [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3017 := soundS (opAt 3004 .ADD)
    (blockOfS _ (pcFactS input 3004 5365 [(11 : UInt256), sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3017)
      (stepS_add input 5365 ((11 : UInt256)) (sv) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3018 := soundS (opAt 3005 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 3005 5366 [((11 : UInt256) + sv), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3018)
      (stepS_swap input 5366 2 (by decide) [((11 : UInt256) + sv), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3019 := soundS (opAt 3006 .POP)
    (blockOfS _ (pcFactS input 3006 5367 [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3019)
      (stepS_pop input 5367 (sv) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3020 := soundS (pushAt 3007 2 0x1475)
    (blockOfS _ (pcFactS input 3007 5368 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3020)
      (stepS_push input 5368 2 (5237 : UInt256) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3021 := soundS (opAt 3008 .JUMP)
    (blockOfS _ (pcFactS input 3008 5371 [(5237 : UInt256), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3021)
      (stepS_jump input 5371 5237 ((5237 : UInt256)) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num) rfl hdest5170))
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
      stS input 5331 [rawWord k, UInt256.mul M (UInt256.ofNat (scalarAt k)),
        UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a,
        P7, M, m7, P, m8] := rfl
  have hend : compareState input k (11 + scalarAt k) a =
      stS input 5237 [straddleAdd (rawWord k)
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

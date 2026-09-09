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

theorem hdest5170 : Decode.isValidJumpDest submissionBytecode 0x163 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 204 (by rfl)

/-- Strength reduction is valid for every 256-bit word, including wraparound. -/
private theorem straddle_shift_three (v : UInt256) :
    UInt256.shiftLeft v 3 = (8 : UInt256) * v := by
  apply Challenge.EvmProof.Word.word_ext
  change (UInt256.ofNat ((v.toNat <<< 3) % UInt256.size)).toNat =
    ((8 : Fin UInt256.size) * v.val).val
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Fin.val_mul]
  norm_num [Nat.shiftLeft_eq, UInt256.size, UInt256.toNat, Nat.mul_comm]

/-- The correction block, with every stack slot symbolic. -/
def gasSteps_straddle_sym (input : ByteArray) (E S sv ov acc : UInt256) :
    GasSteps (stS input 477 [E, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 355 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8]) := by
  have step2989 := soundS (opAt 265 .JUMPDEST)
    (blockOfS _ (pcFactS input 265 0x1dd [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2989)
      (stepS_jumpdest input 0x1dd [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2990 := soundS (opAt 266 (.Dup ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 266 0x1de [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2990)
      (stepS_dup input 0x1de 6 (by decide) [E, S, sv, ov, acc, P7, M, m7, P, m8] (M) (by rfl) (by simp) (by norm_num)))
  have step2991 := soundS (opAt 267 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 267 0x1df [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2991)
      (stepS_dup input 0x1df 4 (by decide) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2992 := soundS (pushAt 268 1 8)
    (blockOfS _ (pcFactS input 268 0x1e0 [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2992)
      (stepS_push input 0x1e0 1 (8 : UInt256) [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2993 := soundS (opAt 269 .SHR)
    (blockOfS _ (pcFactS input 269 0x1e2 [(8 : UInt256), ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2993)
      (stepS_shr input 0x1e2 ((8 : UInt256)) (ov) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2994 := soundS (pushAt 270 1 5)
    (blockOfS _ (pcFactS input 270 0x1e3 [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2994)
      (stepS_push input 0x1e3 1 (5 : UInt256) [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2995 := soundS (opAt 271 .MUL)
    (blockOfS _ (pcFactS input 271 0x1e5 [(5 : UInt256), (UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2995)
      (stepS_mul input 0x1e5 ((5 : UInt256)) ((UInt256.shiftRight ov (8 : UInt256))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2996 := soundS (pushAt 272 1 27)
    (blockOfS _ (pcFactS input 272 0x1e6 [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2996)
      (stepS_push input 0x1e6 1 (27 : UInt256) [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2997 := soundS (opAt 273 .SUB)
    (blockOfS _ (pcFactS input 273 0x1e8 [(27 : UInt256), ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2997)
      (stepS_sub input 0x1e8 ((27 : UInt256)) (((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2998 := soundS (pushAt 274 1 3)
    (blockOfS _ (pcFactS input 274 0x1e9 [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2998)
      (stepS_push input 0x1e9 1 (3 : UInt256) [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2999 := soundS (opAt 275 .SHL)
    (blockOfS _ (pcFactS input 275 0x1eb [(3 : UInt256), ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2999)
      (stepS_shl input 0x1eb ((3 : UInt256)) (((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  rw [straddle_shift_three] at step2999
  have step3000 := soundS (opAt 276 .SHR)
    (blockOfS _ (pcFactS input 276 0x1ec [((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3000)
      (stepS_shr input 0x1ec (((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))) (M) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3001 := soundS (pushAt 277 1 11)
    (blockOfS _ (pcFactS input 277 0x1ed [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3001)
      (stepS_push input 0x1ed 1 (11 : UInt256) [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3002 := soundS (opAt 278 .MUL)
    (blockOfS _ (pcFactS input 278 0x1ef [(11 : UInt256), (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3002)
      (stepS_mul input 0x1ef ((11 : UInt256)) ((UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3003 := soundS (opAt 279 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 279 0x1f0 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3003)
      (stepS_dup input 0x1f0 1 (by decide) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3004 := soundS (opAt 280 (.Dup ⟨9, by decide⟩))
    (blockOfS _ (pcFactS input 280 0x1f1 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3004)
      (stepS_dup input 0x1f1 9 (by decide) [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m7) (by rfl) (by simp) (by norm_num)))
  have step3005 := soundS (opAt 281 .AND)
    (blockOfS _ (pcFactS input 281 0x1f2 [m7, E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3005)
      (stepS_and input 0x1f2 (m7) (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3006 := soundS (opAt 282 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 282 0x1f3 [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3006)
      (stepS_dup input 0x1f3 1 (by decide) [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) (by rfl) (by simp) (by norm_num)))
  have step3007 := soundS (opAt 283 .ADD)
    (blockOfS _ (pcFactS input 283 0x1f4 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3007)
      (stepS_add input 0x1f4 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) ((UInt256.land m7 E)) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3008 := soundS (opAt 284 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 284 0x1f5 [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3008)
      (stepS_dup input 0x1f5 2 (by decide) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3009 := soundS (opAt 285 (.Dup ⟨12, by decide⟩))
    (blockOfS _ (pcFactS input 285 0x1f6 [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3009)
      (stepS_dup input 0x1f6 12 (by decide) [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m8) (by rfl) (by simp) (by norm_num)))
  have step3010 := soundS (opAt 286 .AND)
    (blockOfS _ (pcFactS input 286 0x1f7 [m8, E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3010)
      (stepS_and input 0x1f7 (m8) (E) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3011 := soundS (opAt 287 .XOR)
    (blockOfS _ (pcFactS input 287 0x1f8 [(UInt256.land m8 E), (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3011)
      (stepS_xor input 0x1f8 ((UInt256.land m8 E)) ((((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3012 := soundS (opAt 288 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 288 0x1f9 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3012)
      (stepS_swap input 0x1f9 1 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3013 := soundS (opAt 289 .POP)
    (blockOfS _ (pcFactS input 289 0x1fa [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3013)
      (stepS_pop input 0x1fa (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3014 := soundS (opAt 290 .POP)
    (blockOfS _ (pcFactS input 290 0x1fb [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3014)
      (stepS_pop input 0x1fb (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3015 := soundS (opAt 291 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 291 0x1fc [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3015)
      (stepS_swap input 0x1fc 1 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] [sv, S, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3016 := soundS (pushAt 292 1 11)
    (blockOfS _ (pcFactS input 292 0x1fd [sv, S, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3016)
      (stepS_push input 0x1fd 1 (11 : UInt256) [sv, S, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3017 := soundS (opAt 293 .ADD)
    (blockOfS _ (pcFactS input 293 0x1ff [(11 : UInt256), sv, S, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3017)
      (stepS_add input 0x1ff ((11 : UInt256)) (sv) [S, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3018 := soundS (opAt 294 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 294 0x200 [((11 : UInt256) + sv), S, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3018)
      (stepS_swap input 0x200 1 (by decide) [((11 : UInt256) + sv), S, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ov, acc, P7, M, m7, P, m8] [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3020 := soundS (pushAt 295 2 355)
    (blockOfS _ (pcFactS input 295 0x201 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3020)
      (stepS_push input 0x201 2 (355 : UInt256) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3021 := soundS (opAt 296 .JUMP)
    (blockOfS _ (pcFactS input 296 0x204 [(355 : UInt256), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3021)
      (stepS_jump input 0x204 355 ((355 : UInt256)) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num) rfl hdest5170))
  exact step2989.trans (step2990.trans (step2991.trans (step2992.trans (step2993.trans (step2994.trans (step2995.trans (step2996.trans (step2997.trans (step2998.trans (step2999.trans (step3000.trans (step3001.trans (step3002.trans (step3003.trans (step3004.trans (step3005.trans (step3006.trans (step3007.trans (step3008.trans (step3009.trans (step3010.trans (step3011.trans (step3012.trans (step3013.trans (step3014.trans (step3015.trans (step3016.trans (step3017.trans (step3018.trans (step3020.trans (step3021)))))))))))))))))))))))))))))))

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
      stS input 477 [rawWord k, UInt256.mul M (UInt256.ofNat (scalarAt k)),
        UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a,
        P7, M, m7, P, m8] := rfl
  have hend : compareState input k (11 + scalarAt k) a =
      stS input 355 [straddleAdd (rawWord k)
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

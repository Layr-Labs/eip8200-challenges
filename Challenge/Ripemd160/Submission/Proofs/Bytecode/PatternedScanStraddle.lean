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

theorem hdest5170 : Decode.isValidJumpDest submissionBytecode 0xd8 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 131 (by rfl)

/-- Strength reduction is valid for every 256-bit word, including wraparound. -/
private theorem straddle_shift_three (v : UInt256) :
    UInt256.shiftLeft v 3 = (8 : UInt256) * v := by
  apply Challenge.EvmProof.Word.word_ext
  change (UInt256.ofNat ((v.toNat <<< 3) % UInt256.size)).toNat =
    ((8 : Fin UInt256.size) * v.val).val
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Fin.val_mul]
  norm_num [Nat.shiftLeft_eq, UInt256.size, UInt256.toNat, Nat.mul_comm]

/-- Bump the scalar in place while restoring the two expected-word slots. -/
def gasSteps_scalar_bump (input : ByteArray) (E S sv ov acc : UInt256) :
    GasSteps (stS input 211 [E, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 216 [E, S, (11 : UInt256) + sv, ov, acc, P7, M, m7, P, m8]) := by
  have a := soundS (opAt 127 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 127 211 _ (by norm_num) (by rfl))
      (stepS_swap input 211 1 (by decide) [E, S, sv, ov, acc, P7, M, m7, P, m8]
        [sv, S, E, ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have b := soundS (pushAt 128 1 11)
    (blockOfS _ (pcFactS input 128 212 _ (by norm_num) (by rfl))
      (stepS_push input 212 1 11 [sv, S, E, ov, acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have c := soundS (opAt 129 .ADD)
    (blockOfS _ (pcFactS input 129 214 _ (by norm_num) (by rfl))
      (stepS_add input 214 11 sv [S, E, ov, acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have d := soundS (opAt 130 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 130 215 _ (by norm_num) (by rfl))
      (stepS_swap input 215 1 (by decide) [(11 : UInt256) + sv, S, E, ov, acc, P7, M, m7, P, m8]
        [E, S, (11 : UInt256) + sv, ov, acc, P7, M, m7, P, m8]
        (by rfl) (by simp) (by norm_num)))
  exact a.trans (b.trans (c.trans d))

/-- The correction block, with every stack slot symbolic. -/
def gasSteps_straddle_sym (input : ByteArray) (E S sv ov acc : UInt256) :
    GasSteps (stS input 180 [E, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 216 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8]) := by
  have step2989 := soundS (opAt 101 .JUMPDEST)
    (blockOfS _ (pcFactS input 101 180 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2989)
      (stepS_jumpdest input 180 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2990 := soundS (opAt 102 (.Dup ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 102 181 [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2990)
      (stepS_dup input 181 6 (by decide) [E, S, sv, ov, acc, P7, M, m7, P, m8] (M) (by rfl) (by simp) (by norm_num)))
  have step2991 := soundS (opAt 103 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 103 182 [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2991)
      (stepS_dup input 182 4 (by decide) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2992 := soundS (pushAt 104 1 8)
    (blockOfS _ (pcFactS input 104 183 [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2992)
      (stepS_push input 183 1 (8 : UInt256) [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2993 := soundS (opAt 105 .SHR)
    (blockOfS _ (pcFactS input 105 185 [(8 : UInt256), ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2993)
      (stepS_shr input 185 ((8 : UInt256)) (ov) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2994 := soundS (pushAt 106 1 5)
    (blockOfS _ (pcFactS input 106 186 [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2994)
      (stepS_push input 186 1 (5 : UInt256) [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2995 := soundS (opAt 107 .MUL)
    (blockOfS _ (pcFactS input 107 188 [(5 : UInt256), (UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2995)
      (stepS_mul input 188 ((5 : UInt256)) ((UInt256.shiftRight ov (8 : UInt256))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2996 := soundS (pushAt 108 1 27)
    (blockOfS _ (pcFactS input 108 189 [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2996)
      (stepS_push input 189 1 (27 : UInt256) [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2997 := soundS (opAt 109 .SUB)
    (blockOfS _ (pcFactS input 109 191 [(27 : UInt256), ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2997)
      (stepS_sub input 191 ((27 : UInt256)) (((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2998 := soundS (pushAt 110 1 3)
    (blockOfS _ (pcFactS input 110 192 [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2998)
      (stepS_push input 192 1 (3 : UInt256) [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2999 := soundS (opAt 111 .SHL)
    (blockOfS _ (pcFactS input 111 194 [(3 : UInt256), ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2999)
      (stepS_shl input 194 ((3 : UInt256)) (((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  rw [straddle_shift_three] at step2999
  have step3000 := soundS (opAt 112 .SHR)
    (blockOfS _ (pcFactS input 112 195 [((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3000)
      (stepS_shr input 195 (((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))) (M) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3001 := soundS (pushAt 113 1 11)
    (blockOfS _ (pcFactS input 113 196 [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3001)
      (stepS_push input 196 1 (11 : UInt256) [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3002 := soundS (opAt 114 .MUL)
    (blockOfS _ (pcFactS input 114 198 [(11 : UInt256), (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3002)
      (stepS_mul input 198 ((11 : UInt256)) ((UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3003 := soundS (opAt 115 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 115 199 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3003)
      (stepS_dup input 199 1 (by decide) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3004 := soundS (opAt 116 (.Dup ⟨9, by decide⟩))
    (blockOfS _ (pcFactS input 116 200 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3004)
      (stepS_dup input 200 9 (by decide) [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m7) (by rfl) (by simp) (by norm_num)))
  have step3005 := soundS (opAt 117 .AND)
    (blockOfS _ (pcFactS input 117 201 [m7, E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3005)
      (stepS_and input 201 (m7) (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3006 := soundS (opAt 118 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 118 202 [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3006)
      (stepS_dup input 202 1 (by decide) [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) (by rfl) (by simp) (by norm_num)))
  have step3007 := soundS (opAt 119 .ADD)
    (blockOfS _ (pcFactS input 119 203 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3007)
      (stepS_add input 203 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) ((UInt256.land m7 E)) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3008 := soundS (opAt 120 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 120 204 [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3008)
      (stepS_dup input 204 2 (by decide) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3009 := soundS (opAt 121 (.Dup ⟨12, by decide⟩))
    (blockOfS _ (pcFactS input 121 205 [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3009)
      (stepS_dup input 205 12 (by decide) [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m8) (by rfl) (by simp) (by norm_num)))
  have step3010 := soundS (opAt 122 .AND)
    (blockOfS _ (pcFactS input 122 206 [m8, E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3010)
      (stepS_and input 206 (m8) (E) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3011 := soundS (opAt 123 .XOR)
    (blockOfS _ (pcFactS input 123 207 [(UInt256.land m8 E), (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3011)
      (stepS_xor input 207 ((UInt256.land m8 E)) ((((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3012 := soundS (opAt 124 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 124 208 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3012)
      (stepS_swap input 208 1 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3013 := soundS (opAt 125 .POP)
    (blockOfS _ (pcFactS input 125 209 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3013)
      (stepS_pop input 209 (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3014 := soundS (opAt 126 .POP)
    (blockOfS _ (pcFactS input 126 210 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3014)
      (stepS_pop input 210 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  exact step2989.trans (step2990.trans (step2991.trans (step2992.trans (step2993.trans (step2994.trans (step2995.trans (step2996.trans (step2997.trans (step2998.trans (step2999.trans (step3000.trans (step3001.trans (step3002.trans (step3003.trans (step3004.trans (step3005.trans (step3006.trans (step3007.trans (step3008.trans (step3009.trans (step3010.trans (step3011.trans (step3012.trans (step3013.trans (step3014.trans (gasSteps_scalar_bump input _ _ _ _ _))))))))))))))))))))))))))

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
      stS input 180 [rawWord k, UInt256.mul M (UInt256.ofNat (scalarAt k)),
        UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a,
        P7, M, m7, P, m8] := rfl
  have hend : compareState input k (11 + scalarAt k) a =
      stS input 216 [straddleAdd (rawWord k)
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

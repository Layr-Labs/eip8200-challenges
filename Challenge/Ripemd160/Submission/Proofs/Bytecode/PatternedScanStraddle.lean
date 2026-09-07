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

theorem hdest5170 : Decode.isValidJumpDest submissionBytecode 0xc3 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 90 (by rfl)

/-- The correction block, with every stack slot symbolic. -/
def gasSteps_straddle_sym (input : ByteArray) (E S sv ov acc : UInt256) :
    GasSteps (stS input 285 [E, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 195 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8]) := by
  have step2989 := soundS (opAt 140 .JUMPDEST)
    (blockOfS _ (pcFactS input 140 0x11d [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2989)
      (stepS_jumpdest input 0x11d [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2990 := soundS (opAt 141 (.Dup ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 141 0x11e [E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2990)
      (stepS_dup input 0x11e 6 (by decide) [E, S, sv, ov, acc, P7, M, m7, P, m8] (M) (by rfl) (by simp) (by norm_num)))
  have step2991 := soundS (opAt 142 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 142 0x11f [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2991)
      (stepS_dup input 0x11f 4 (by decide) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2992 := soundS (pushAt 143 1 8)
    (blockOfS _ (pcFactS input 143 0x120 [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2992)
      (stepS_push input 0x120 1 (8 : UInt256) [ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2993 := soundS (opAt 144 .SHR)
    (blockOfS _ (pcFactS input 144 0x122 [(8 : UInt256), ov, M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2993)
      (stepS_shr input 0x122 ((8 : UInt256)) (ov) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2994 := soundS (pushAt 145 1 5)
    (blockOfS _ (pcFactS input 145 0x123 [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2994)
      (stepS_push input 0x123 1 (5 : UInt256) [(UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2995 := soundS (opAt 146 .MUL)
    (blockOfS _ (pcFactS input 146 0x125 [(5 : UInt256), (UInt256.shiftRight ov (8 : UInt256)), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2995)
      (stepS_mul input 0x125 ((5 : UInt256)) ((UInt256.shiftRight ov (8 : UInt256))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2996 := soundS (pushAt 147 1 27)
    (blockOfS _ (pcFactS input 147 0x126 [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2996)
      (stepS_push input 0x126 1 (27 : UInt256) [((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2997 := soundS (opAt 148 .SUB)
    (blockOfS _ (pcFactS input 148 0x128 [(27 : UInt256), ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2997)
      (stepS_sub input 0x128 ((27 : UInt256)) (((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2998 := soundS (pushAt 149 1 8)
    (blockOfS _ (pcFactS input 149 0x129 [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2998)
      (stepS_push input 0x129 1 (8 : UInt256) [((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2999 := soundS (opAt 150 .MUL)
    (blockOfS _ (pcFactS input 150 0x12b [(8 : UInt256), ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2999)
      (stepS_mul input 0x12b ((8 : UInt256)) (((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))) [M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3000 := soundS (opAt 151 .SHR)
    (blockOfS _ (pcFactS input 151 0x12c [((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))), M, E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3000)
      (stepS_shr input 0x12c (((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))) (M) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3001 := soundS (pushAt 152 1 11)
    (blockOfS _ (pcFactS input 152 0x12d [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3001)
      (stepS_push input 0x12d 1 (11 : UInt256) [(UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3002 := soundS (opAt 153 .MUL)
    (blockOfS _ (pcFactS input 153 0x12f [(11 : UInt256), (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3002)
      (stepS_mul input 0x12f ((11 : UInt256)) ((UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) [E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3003 := soundS (opAt 154 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 154 0x130 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3003)
      (stepS_dup input 0x130 1 (by decide) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3004 := soundS (opAt 155 (.Dup ⟨9, by decide⟩))
    (blockOfS _ (pcFactS input 155 0x131 [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3004)
      (stepS_dup input 0x131 9 (by decide) [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m7) (by rfl) (by simp) (by norm_num)))
  have step3005 := soundS (opAt 156 .AND)
    (blockOfS _ (pcFactS input 156 0x132 [m7, E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3005)
      (stepS_and input 0x132 (m7) (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3006 := soundS (opAt 157 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 157 0x133 [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3006)
      (stepS_dup input 0x133 1 (by decide) [(UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) (by rfl) (by simp) (by norm_num)))
  have step3007 := soundS (opAt 158 .ADD)
    (blockOfS _ (pcFactS input 158 0x134 [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.land m7 E), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3007)
      (stepS_add input 0x134 (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) ((UInt256.land m7 E)) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3008 := soundS (opAt 159 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 159 0x135 [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3008)
      (stepS_dup input 0x135 2 (by decide) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (E) (by rfl) (by simp) (by norm_num)))
  have step3009 := soundS (opAt 160 (.Dup ⟨12, by decide⟩))
    (blockOfS _ (pcFactS input 160 0x136 [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3009)
      (stepS_dup input 0x136 12 (by decide) [E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (m8) (by rfl) (by simp) (by norm_num)))
  have step3010 := soundS (opAt 161 .AND)
    (blockOfS _ (pcFactS input 161 0x137 [m8, E, (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3010)
      (stepS_and input 0x137 (m8) (E) [(((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3011 := soundS (opAt 162 .XOR)
    (blockOfS _ (pcFactS input 162 0x138 [(UInt256.land m8 E), (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E)), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3011)
      (stepS_xor input 0x138 ((UInt256.land m8 E)) ((((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3012 := soundS (opAt 163 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 163 0x139 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3012)
      (stepS_swap input 0x139 1 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), E, S, sv, ov, acc, P7, M, m7, P, m8] [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3013 := soundS (opAt 164 .POP)
    (blockOfS _ (pcFactS input 164 0x13a [E, ((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3013)
      (stepS_pop input 0x13a (E) [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3014 := soundS (opAt 165 .POP)
    (blockOfS _ (pcFactS input 165 0x13b [((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3014)
      (stepS_pop input 0x13b (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256)))))))) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3015 := soundS (opAt 166 (.Dup ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 166 0x13c [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3015)
      (stepS_dup input 0x13c 2 (by decide) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (sv) (by rfl) (by simp) (by norm_num)))
  have step3016 := soundS (pushAt 167 1 11)
    (blockOfS _ (pcFactS input 167 0x13d [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3016)
      (stepS_push input 0x13d 1 (11 : UInt256) [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3017 := soundS (opAt 168 .ADD)
    (blockOfS _ (pcFactS input 168 0x13f [(11 : UInt256), sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3017)
      (stepS_add input 0x13f ((11 : UInt256)) (sv) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3018 := soundS (opAt 169 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 169 0x140 [((11 : UInt256) + sv), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc3018)
      (stepS_swap input 0x140 2 (by decide) [((11 : UInt256) + sv), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, sv, ov, acc, P7, M, m7, P, m8] [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step3019 := soundS (opAt 170 .POP)
    (blockOfS _ (pcFactS input 170 0x141 [sv, (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3019)
      (stepS_pop input 0x141 (sv) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3020 := soundS (pushAt 171 1 195)
    (blockOfS _ (pcFactS input 171 0x142 [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3020)
      (stepS_push input 0x142 1 (195 : UInt256) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step3021 := soundS (opAt 172 .JUMP)
    (blockOfS _ (pcFactS input 172 0x144 [(195 : UInt256), (UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by norm_num) pc3021)
      (stepS_jump input 0x144 195 ((195 : UInt256)) [(UInt256.xor (UInt256.land m8 E) (((11 : UInt256) * (UInt256.shiftRight M ((8 : UInt256) * ((27 : UInt256) - ((5 : UInt256) * (UInt256.shiftRight ov (8 : UInt256))))))) + (UInt256.land m7 E))), S, ((11 : UInt256) + sv), ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num) rfl hdest5170))
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
      stS input 285 [rawWord k, UInt256.mul M (UInt256.ofNat (scalarAt k)),
        UInt256.ofNat (scalarAt k), UInt256.ofNat (32 * k), a,
        P7, M, m7, P, m8] := rfl
  have hend : compareState input k (11 + scalarAt k) a =
      stS input 195 [straddleAdd (rawWord k)
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

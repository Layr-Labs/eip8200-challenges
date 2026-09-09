import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# Folding one word into the accumulator

The block exclusive-ors the calldata word against the expected word, ors the
difference into the accumulator, advances the scalar by 160 modulo 256 and the
offset by 32, and jumps back while the offset is still under 992.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

theorem hdest5144 : Decode.isValidJumpDest submissionBytecode 0x142 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 178 (by rfl)

/-- The shared compare prefix: fold one word into the accumulator and advance
the scalar and offset, stopping where the loop's size-exit test begins.  Both
the patterned loop and the memo's scan use it; they differ only in how they
leave.  Factored out of `gasSteps_compare_more_sym`, whose steps these are. -/
def gasSteps_compare_fold (input : ByteArray) (W S sv ov acc : UInt256) :
    GasSteps (stS input 348 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 368 [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8]) := by
  have step2936 := soundS (opAt 200 .JUMPDEST)
    (blockOfS _ (pcFactS input 200 0x15c [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2936)
      (stepS_jumpdest input 0x15c [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2937 := soundS (opAt 201 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 201 0x15d [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2937)
      (stepS_dup input 0x15d 3 (by decide) [W, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2938 := soundS (opAt 202 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 202 0x15e [ov, W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2938)
      (stepS_calldataload input 0x15e (ov) [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2939 := soundS (opAt 203 .XOR)
    (blockOfS _ (pcFactS input 203 0x15f [(MachineState.readWord input (ov).toNat), W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2939)
      (stepS_xor input 0x15f ((MachineState.readWord input (ov).toNat)) (W) [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2940 := soundS (opAt 204 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 204 0x160 [(UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2940)
      (stepS_dup input 0x160 4 (by decide) [(UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2941 := soundS (opAt 205 .OR)
    (blockOfS _ (pcFactS input 205 0x161 [acc, (UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2941)
      (stepS_or input 0x161 (acc) ((UInt256.xor (MachineState.readWord input (ov).toNat) W)) [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2942 := soundS (opAt 206 (.Swap ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 206 0x162 [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2942)
      (stepS_swap input 0x162 3 (by decide) [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), S, sv, ov, acc, P7, M, m7, P, m8] [acc, S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2943 := soundS (opAt 207 .POP)
    (blockOfS _ (pcFactS input 207 0x163 [acc, S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2943)
      (stepS_pop input 0x163 (acc) [S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2944 := soundS (opAt 208 .POP)
    (blockOfS _ (pcFactS input 208 0x164 [S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2944)
      (stepS_pop input 0x164 (S) [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2946 := soundS (pushAt 209 1 160)
    (blockOfS _ (pcFactS input 209 0x165 [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2946)
      (stepS_push input 0x165 1 (160 : UInt256) [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2947 := soundS (opAt 210 .ADD)
    (blockOfS _ (pcFactS input 210 0x167 [(160 : UInt256), sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2947)
      (stepS_add input 0x167 ((160 : UInt256)) (sv) [ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2948 := soundS (pushAt 211 1 255)
    (blockOfS _ (pcFactS input 211 0x168 [((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2948)
      (stepS_push input 0x168 1 (255 : UInt256) [((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2949 := soundS (opAt 212 .AND)
    (blockOfS _ (pcFactS input 212 0x16a [(255 : UInt256), ((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2949)
      (stepS_and input 0x16a ((255 : UInt256)) (((160 : UInt256) + sv)) [ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2952 := soundS (opAt 213 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 213 0x16b [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2952)
      (stepS_swap input 0x16b 0 (by decide) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2953 := soundS (pushAt 214 1 32)
    (blockOfS _ (pcFactS input 214 0x16c [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2953)
      (stepS_push input 0x16c 1 (32 : UInt256) [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2954 := soundS (opAt 215 .ADD)
    (blockOfS _ (pcFactS input 215 0x16e [(32 : UInt256), ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2954)
      (stepS_add input 0x16e ((32 : UInt256)) (ov) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2955 := soundS (opAt 216 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 216 0x16f [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2955)
      (stepS_swap input 0x16f 0 (by decide) [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  exact step2936.trans (step2937.trans (step2938.trans (step2939.trans (step2940.trans (step2941.trans (step2942.trans (step2943.trans (step2944.trans (step2946.trans (step2947.trans (step2948.trans (step2949.trans (step2952.trans (step2953.trans (step2954.trans (step2955))))))))))))))))

/-- One folded word, with the scan continuing. -/
def gasSteps_compare_more_sym (input : ByteArray) (W S sv ov acc : UInt256) (hc : UInt256.isTrue (UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)))
    (hne : (32 : UInt256) + ov ≠ UInt256.ofNat input.size) :
    GasSteps (stS input 348 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 322 [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8]) := by
  have step2936 := soundS (opAt 200 .JUMPDEST)
    (blockOfS _ (pcFactS input 200 0x15c [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2936)
      (stepS_jumpdest input 0x15c [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2937 := soundS (opAt 201 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 201 0x15d [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2937)
      (stepS_dup input 0x15d 3 (by decide) [W, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2938 := soundS (opAt 202 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 202 0x15e [ov, W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2938)
      (stepS_calldataload input 0x15e (ov) [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2939 := soundS (opAt 203 .XOR)
    (blockOfS _ (pcFactS input 203 0x15f [(MachineState.readWord input (ov).toNat), W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2939)
      (stepS_xor input 0x15f ((MachineState.readWord input (ov).toNat)) (W) [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2940 := soundS (opAt 204 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 204 0x160 [(UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2940)
      (stepS_dup input 0x160 4 (by decide) [(UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2941 := soundS (opAt 205 .OR)
    (blockOfS _ (pcFactS input 205 0x161 [acc, (UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2941)
      (stepS_or input 0x161 (acc) ((UInt256.xor (MachineState.readWord input (ov).toNat) W)) [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2942 := soundS (opAt 206 (.Swap ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 206 0x162 [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2942)
      (stepS_swap input 0x162 3 (by decide) [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), S, sv, ov, acc, P7, M, m7, P, m8] [acc, S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2943 := soundS (opAt 207 .POP)
    (blockOfS _ (pcFactS input 207 0x163 [acc, S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2943)
      (stepS_pop input 0x163 (acc) [S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2944 := soundS (opAt 208 .POP)
    (blockOfS _ (pcFactS input 208 0x164 [S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2944)
      (stepS_pop input 0x164 (S) [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2946 := soundS (pushAt 209 1 160)
    (blockOfS _ (pcFactS input 209 0x165 [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2946)
      (stepS_push input 0x165 1 (160 : UInt256) [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2947 := soundS (opAt 210 .ADD)
    (blockOfS _ (pcFactS input 210 0x167 [(160 : UInt256), sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2947)
      (stepS_add input 0x167 ((160 : UInt256)) (sv) [ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2948 := soundS (pushAt 211 1 255)
    (blockOfS _ (pcFactS input 211 0x168 [((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2948)
      (stepS_push input 0x168 1 (255 : UInt256) [((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2949 := soundS (opAt 212 .AND)
    (blockOfS _ (pcFactS input 212 0x16a [(255 : UInt256), ((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2949)
      (stepS_and input 0x16a ((255 : UInt256)) (((160 : UInt256) + sv)) [ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2952 := soundS (opAt 213 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 213 0x16b [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2952)
      (stepS_swap input 0x16b 0 (by decide) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2953 := soundS (pushAt 214 1 32)
    (blockOfS _ (pcFactS input 214 0x16c [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2953)
      (stepS_push input 0x16c 1 (32 : UInt256) [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2954 := soundS (opAt 215 .ADD)
    (blockOfS _ (pcFactS input 215 0x16e [(32 : UInt256), ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2954)
      (stepS_add input 0x16e ((32 : UInt256)) (ov) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2955 := soundS (opAt 216 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 216 0x16f [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2955)
      (stepS_swap input 0x16f 0 (by decide) [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2957 := soundS (opAt 222 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 222 0x176 [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2957)
      (stepS_dup input 0x176 1 (by decide) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (((32 : UInt256) + ov)) (by rfl) (by simp) (by norm_num)))
  have step2958 := soundS (pushAt 223 2 992)
    (blockOfS _ (pcFactS input 223 0x177 [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2958)
      (stepS_push input 0x177 2 (992 : UInt256) [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2959 := soundS (opAt 224 .GT)
    (blockOfS _ (pcFactS input 224 0x17a [(992 : UInt256), ((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2959)
      (stepS_gt input 0x17a ((992 : UInt256)) (((32 : UInt256) + ov)) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2960 := soundS (pushAt 225 2 322)
    (blockOfS _ (pcFactS input 225 0x17b [(UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2960)
      (stepS_push input 0x17b 2 (322 : UInt256) [(UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2961 := soundS (opAt 226 .JUMPI)
    (blockOfS _ (pcFactS input 226 0x17e [(322 : UInt256), (UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2961)
      (stepS_jumpi_taken input 0x17e 322 ((322 : UInt256)) ((UInt256.gt (992 : UInt256) ((32 : UInt256) + ov))) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num) rfl hc hdest5144))
  exact step2936.trans (step2937.trans (step2938.trans (step2939.trans (step2940.trans (step2941.trans (step2942.trans (step2943.trans (step2944.trans (step2946.trans (step2947.trans (step2948.trans (step2949.trans (step2952.trans (step2953.trans (step2954.trans (step2955.trans ((gasSteps_size_skip input (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)) ((32 : UInt256) + ov) [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) hne).trans (step2957.trans (step2958.trans (step2959.trans (step2960.trans (step2961))))))))))))))))))))))

/-- The last folded word, falling through to the tail. -/
def gasSteps_compare_last_sym (input : ByteArray) (W S sv ov acc : UInt256) (hc : ¬ UInt256.isTrue (UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)))
    (hne : (32 : UInt256) + ov ≠ UInt256.ofNat input.size) :
    GasSteps (stS input 348 [W, S, sv, ov, acc, P7, M, m7, P, m8])
      (stS input 383 [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8]) := by
  have step2936 := soundS (opAt 200 .JUMPDEST)
    (blockOfS _ (pcFactS input 200 0x15c [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2936)
      (stepS_jumpdest input 0x15c [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2937 := soundS (opAt 201 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 201 0x15d [W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2937)
      (stepS_dup input 0x15d 3 (by decide) [W, S, sv, ov, acc, P7, M, m7, P, m8] (ov) (by rfl) (by simp) (by norm_num)))
  have step2938 := soundS (opAt 202 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 202 0x15e [ov, W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2938)
      (stepS_calldataload input 0x15e (ov) [W, S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2939 := soundS (opAt 203 .XOR)
    (blockOfS _ (pcFactS input 203 0x15f [(MachineState.readWord input (ov).toNat), W, S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2939)
      (stepS_xor input 0x15f ((MachineState.readWord input (ov).toNat)) (W) [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2940 := soundS (opAt 204 (.Dup ⟨4, by decide⟩))
    (blockOfS _ (pcFactS input 204 0x160 [(UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2940)
      (stepS_dup input 0x160 4 (by decide) [(UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2941 := soundS (opAt 205 .OR)
    (blockOfS _ (pcFactS input 205 0x161 [acc, (UInt256.xor (MachineState.readWord input (ov).toNat) W), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2941)
      (stepS_or input 0x161 (acc) ((UInt256.xor (MachineState.readWord input (ov).toNat) W)) [S, sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2942 := soundS (opAt 206 (.Swap ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 206 0x162 [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), S, sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2942)
      (stepS_swap input 0x162 3 (by decide) [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), S, sv, ov, acc, P7, M, m7, P, m8] [acc, S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2943 := soundS (opAt 207 .POP)
    (blockOfS _ (pcFactS input 207 0x163 [acc, S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2943)
      (stepS_pop input 0x163 (acc) [S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2944 := soundS (opAt 208 .POP)
    (blockOfS _ (pcFactS input 208 0x164 [S, sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2944)
      (stepS_pop input 0x164 (S) [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2946 := soundS (pushAt 209 1 160)
    (blockOfS _ (pcFactS input 209 0x165 [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2946)
      (stepS_push input 0x165 1 (160 : UInt256) [sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2947 := soundS (opAt 210 .ADD)
    (blockOfS _ (pcFactS input 210 0x167 [(160 : UInt256), sv, ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2947)
      (stepS_add input 0x167 ((160 : UInt256)) (sv) [ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2948 := soundS (pushAt 211 1 255)
    (blockOfS _ (pcFactS input 211 0x168 [((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2948)
      (stepS_push input 0x168 1 (255 : UInt256) [((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2949 := soundS (opAt 212 .AND)
    (blockOfS _ (pcFactS input 212 0x16a [(255 : UInt256), ((160 : UInt256) + sv), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2949)
      (stepS_and input 0x16a ((255 : UInt256)) (((160 : UInt256) + sv)) [ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2952 := soundS (opAt 213 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 213 0x16b [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2952)
      (stepS_swap input 0x16b 0 (by decide) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ov, (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2953 := soundS (pushAt 214 1 32)
    (blockOfS _ (pcFactS input 214 0x16c [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2953)
      (stepS_push input 0x16c 1 (32 : UInt256) [ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2954 := soundS (opAt 215 .ADD)
    (blockOfS _ (pcFactS input 215 0x16e [(32 : UInt256), ov, (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2954)
      (stepS_add input 0x16e ((32 : UInt256)) (ov) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2955 := soundS (opAt 216 (.Swap ⟨0, by decide⟩))
    (blockOfS _ (pcFactS input 216 0x16f [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2955)
      (stepS_swap input 0x16f 0 (by decide) [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2957 := soundS (opAt 222 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 222 0x176 [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2957)
      (stepS_dup input 0x176 1 (by decide) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (((32 : UInt256) + ov)) (by rfl) (by simp) (by norm_num)))
  have step2958 := soundS (pushAt 223 2 992)
    (blockOfS _ (pcFactS input 223 0x177 [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2958)
      (stepS_push input 0x177 2 (992 : UInt256) [((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2959 := soundS (opAt 224 .GT)
    (blockOfS _ (pcFactS input 224 0x17a [(992 : UInt256), ((32 : UInt256) + ov), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2959)
      (stepS_gt input 0x17a ((992 : UInt256)) (((32 : UInt256) + ov)) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2960 := soundS (pushAt 225 2 322)
    (blockOfS _ (pcFactS input 225 0x17b [(UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2960)
      (stepS_push input 0x17b 2 (322 : UInt256) [(UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2961 := soundS (opAt 226 .JUMPI)
    (blockOfS _ (pcFactS input 226 0x17e [(322 : UInt256), (UInt256.gt (992 : UInt256) ((32 : UInt256) + ov)), (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by norm_num) pc2961)
      (stepS_jumpi_fall input 0x17e ((322 : UInt256)) ((UInt256.gt (992 : UInt256) ((32 : UInt256) + ov))) [(UInt256.land (255 : UInt256) ((160 : UInt256) + sv)), ((32 : UInt256) + ov), (UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) (by norm_num) hc))
  exact step2936.trans (step2937.trans (step2938.trans (step2939.trans (step2940.trans (step2941.trans (step2942.trans (step2943.trans (step2944.trans (step2946.trans (step2947.trans (step2948.trans (step2949.trans (step2952.trans (step2953.trans (step2954.trans (step2955.trans ((gasSteps_size_skip input (UInt256.land (255 : UInt256) ((160 : UInt256) + sv)) ((32 : UInt256) + ov) [(UInt256.lor acc (UInt256.xor (MachineState.readWord input (ov).toNat) W)), P7, M, m7, P, m8] (by simp) hne).trans (step2957.trans (step2958.trans (step2959.trans (step2960.trans (step2961))))))))))))))))))))))

/-- The offset advances by a word. -/
theorem offset_step (k : Nat) (hk : k < 31) :
    (32 : UInt256) + UInt256.ofNat (32 * k) = UInt256.ofNat (32 * (k + 1)) := by
  have h : UInt256.ofNat 32 + UInt256.ofNat (32 * k) = UInt256.ofNat (32 + 32 * k) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  rw [show 32 + 32 * k = 32 * (k + 1) from by omega] at h
  exact h

/-- The scalar advances by 160 modulo 256. -/
theorem scalar_step (s k : Nat) (hs : s < 256)
    (hstep : (s + 160) % 256 = scalarAt (k + 1)) :
    UInt256.land (255 : UInt256) ((160 : UInt256) + UInt256.ofNat s)
      = UInt256.ofNat (scalarAt (k + 1)) := by
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := rfl
  have h160 : (160 : UInt256) = UInt256.ofNat 160 := rfl
  rw [h255, h160,
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega : 160 + s < 2 ^ 256),
    land_ff _ (by omega), show 160 + s = s + 160 from by omega, hstep]

/-- The scan continues exactly while the next offset is under 992. -/
theorem compare_cond (k : Nat) (hk : k < 31) :
    UInt256.isTrue (UInt256.gt (992 : UInt256)
        ((32 : UInt256) + UInt256.ofNat (32 * k))) ↔ k + 1 < 31 := by
  rw [offset_step k hk]
  unfold UInt256.isTrue UInt256.gt
  rw [show ((992 : UInt256)).toNat = 992 from by decide,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * (k + 1) < 2 ^ 256)]
  by_cases h : 32 * (k + 1) < 992
  · rw [if_pos h]
    exact ⟨fun _ => by omega, fun _ => by decide⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd (by decide : (UInt256.ofNat 0).toNat = 0) hc,
      fun hlt => by omega⟩

/-- One folded word, with the scan continuing. -/
def gasSteps_compare_more (input : ByteArray) (k s : Nat) (a : UInt256)
    (hne : UInt256.ofNat (32 * (k + 1)) ≠ UInt256.ofNat input.size)
    (hk : k + 1 < 31) (hs : s < 256) (hstep : (s + 160) % 256 = scalarAt (k + 1)) :
    GasSteps (compareState input k s a)
      (loopState input (k + 1)
        (UInt256.lor a (UInt256.xor (MachineState.readWord input (32 * k))
          (guardWord k)))) := by
  have hk31 : k < 31 := by omega
  have hoff : (UInt256.ofNat (32 * k)).toNat = 32 * k := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstart : compareState input k s a =
      stS input 348 [guardWord k, UInt256.mul M (UInt256.ofNat (scalarAt k)),
        UInt256.ofNat s, UInt256.ofNat (32 * k), a, P7, M, m7, P, m8] := rfl
  have hend : loopState input (k + 1)
        (UInt256.lor a (UInt256.xor (MachineState.readWord input (32 * k))
          (guardWord k))) =
      stS input 322 [UInt256.land (255 : UInt256)
          ((160 : UInt256) + UInt256.ofNat s),
        (32 : UInt256) + UInt256.ofNat (32 * k),
        UInt256.lor a (UInt256.xor
          (MachineState.readWord input ((UInt256.ofNat (32 * k))).toNat)
          (guardWord k)), P7, M, m7, P, m8] := by
    unfold loopState stS frame
    rw [hoff, scalar_step s k hs hstep, offset_step k hk31]
  rw [hstart, hend]
  exact gasSteps_compare_more_sym input (guardWord k)
    (UInt256.mul M (UInt256.ofNat (scalarAt k))) (UInt256.ofNat s)
    (UInt256.ofNat (32 * k)) a ((compare_cond k hk31).2 hk) (by rwa [offset_step k hk31])

/-- The thirty-first word, falling through to the padded tail. -/
def gasSteps_compare_last (input : ByteArray) (s : Nat) (a : UInt256)
    (hne : UInt256.ofNat 992 ≠ UInt256.ofNat input.size)
    (hs : s < 256) (hstep : (s + 160) % 256 = scalarAt 31) :
    GasSteps (compareState input 30 s a)
      (tailState input
        (UInt256.lor a (UInt256.xor (MachineState.readWord input (32 * 30))
          (guardWord 30)))) := by
  have hoff : (UInt256.ofNat (32 * 30)).toNat = 32 * 30 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
  have hstart : compareState input 30 s a =
      stS input 348 [guardWord 30, UInt256.mul M (UInt256.ofNat (scalarAt 30)),
        UInt256.ofNat s, UInt256.ofNat (32 * 30), a, P7, M, m7, P, m8] := rfl
  have hend : tailState input
        (UInt256.lor a (UInt256.xor (MachineState.readWord input (32 * 30))
          (guardWord 30))) =
      stS input 383 [UInt256.land (255 : UInt256)
          ((160 : UInt256) + UInt256.ofNat s),
        (32 : UInt256) + UInt256.ofNat (32 * 30),
        UInt256.lor a (UInt256.xor
          (MachineState.readWord input ((UInt256.ofNat (32 * 30))).toNat)
          (guardWord 30)), P7, M, m7, P, m8] := by
    unfold tailState stS frame
    rw [hoff, scalar_step s 30 hs hstep, offset_step 30 (by norm_num)]
  rw [hstart, hend]
  exact gasSteps_compare_last_sym input (guardWord 30)
    (UInt256.mul M (UInt256.ofNat (scalarAt 30))) (UInt256.ofNat s)
    (UInt256.ofNat (32 * 30)) a
    (fun hc => absurd ((compare_cond 30 (by norm_num)).1 hc) (by norm_num))
    (by rwa [offset_step 30 (by norm_num)])


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

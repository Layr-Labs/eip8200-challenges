import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The padded tail word and the miss test

Bytes 992 to 999 are read as a whole word, so the constant is shifted up to
meet the zero padding.  The block then drops the five constants and the two
counters, leaving the stack as the guard found it on both exits.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

theorem hdest1006 : Decode.isValidJumpDest submissionBytecode 1006 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)

/-- The accumulator is zero, so the guard answers. -/
def gasSteps_tail_hit_sym (input : ByteArray) (sv ov acc : UInt256) (hc : ¬ UInt256.isTrue (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 5203 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 5237 []) := by
  have step2962 := soundS (pushAt 2962 2 0x03e0)
    (blockOfS _ (pcFactS input 2962 5203 [sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2962)
      (stepS_push input 5203 2 (992 : UInt256) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2963 := soundS (opAt 2963 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 2963 5206 [(992 : UInt256), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2963)
      (stepS_calldataload input 5206 ((992 : UInt256)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 2964 8 0x88add2f71c41668b)
    (blockOfS _ (pcFactS input 2964 5207 [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 5207 8 (9848759918901945995 : UInt256) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 2965 1 0xc0)
    (blockOfS _ (pcFactS input 2965 5216 [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 5216 1 (192 : UInt256) [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 2966 .SHL)
    (blockOfS _ (pcFactS input 2966 5218 [(192 : UInt256), (9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 5218 ((192 : UInt256)) ((9848759918901945995 : UInt256)) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2967 := soundS (opAt 2967 .XOR)
    (blockOfS _ (pcFactS input 2967 5219 [(UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 5219 ((UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))) ((MachineState.readWord input ((992 : UInt256)).toNat)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2968 := soundS (opAt 2968 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 2968 5220 [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 5220 3 (by decide) [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 2969 .OR)
    (blockOfS _ (pcFactS input 2969 5221 [acc, (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 5221 (acc) ((UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2970 := soundS (opAt 2970 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 2970 5222 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2970)
      (stepS_swap input 5222 2 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2971 := soundS (opAt 2971 .POP)
    (blockOfS _ (pcFactS input 2971 5223 [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_pop input 5223 (acc) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2972 := soundS (opAt 2972 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2972 5224 [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2972)
      (stepS_swap input 5224 1 (by decide) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2973 := soundS (opAt 2973 (.Swap ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 2973 5225 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by norm_num) pc2973)
      (stepS_swap input 5225 6 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by rfl) (by simp) (by norm_num)))
  have step2974 := soundS (opAt 2974 .POP)
    (blockOfS _ (pcFactS input 2974 5226 [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2974)
      (stepS_pop input 5226 (m8) [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2975 := soundS (opAt 2975 .POP)
    (blockOfS _ (pcFactS input 2975 5227 [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2975)
      (stepS_pop input 5227 (ov) [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2976 := soundS (opAt 2976 .POP)
    (blockOfS _ (pcFactS input 2976 5228 [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2976)
      (stepS_pop input 5228 (sv) [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2977 := soundS (opAt 2977 .POP)
    (blockOfS _ (pcFactS input 2977 5229 [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2977)
      (stepS_pop input 5229 (P7) [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2978 := soundS (opAt 2978 .POP)
    (blockOfS _ (pcFactS input 2978 5230 [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2978)
      (stepS_pop input 5230 (M) [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2979 := soundS (opAt 2979 .POP)
    (blockOfS _ (pcFactS input 2979 5231 [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2979)
      (stepS_pop input 5231 (m7) [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2980 := soundS (opAt 2980 .POP)
    (blockOfS _ (pcFactS input 2980 5232 [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2980)
      (stepS_pop input 5232 (P) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2981 := soundS (pushAt 2981 2 0x03ee)
    (blockOfS _ (pcFactS input 2981 5233 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2981)
      (stepS_push input 5233 2 (1006 : UInt256) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by decide) (by decide) (by norm_num)))
  have step2982 := soundS (opAt 2982 .JUMPI)
    (blockOfS _ (pcFactS input 2982 5236 [(1006 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2982)
      (stepS_jumpi_fall input 5236 ((1006 : UInt256)) ((UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) [] (by simp) (by norm_num) hc))
  exact step2962.trans (step2963.trans (step2964.trans (step2965.trans (step2966.trans (step2967.trans (step2968.trans (step2969.trans (step2970.trans (step2971.trans (step2972.trans (step2973.trans (step2974.trans (step2975.trans (step2976.trans (step2977.trans (step2978.trans (step2979.trans (step2980.trans (step2981.trans (step2982))))))))))))))))))))

/-- The accumulator is nonzero, so the program runs. -/
def gasSteps_tail_miss_sym (input : ByteArray) (sv ov acc : UInt256) (hc : UInt256.isTrue (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 5203 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 1006 []) := by
  have step2962 := soundS (pushAt 2962 2 0x03e0)
    (blockOfS _ (pcFactS input 2962 5203 [sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2962)
      (stepS_push input 5203 2 (992 : UInt256) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2963 := soundS (opAt 2963 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 2963 5206 [(992 : UInt256), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2963)
      (stepS_calldataload input 5206 ((992 : UInt256)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 2964 8 0x88add2f71c41668b)
    (blockOfS _ (pcFactS input 2964 5207 [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 5207 8 (9848759918901945995 : UInt256) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 2965 1 0xc0)
    (blockOfS _ (pcFactS input 2965 5216 [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 5216 1 (192 : UInt256) [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 2966 .SHL)
    (blockOfS _ (pcFactS input 2966 5218 [(192 : UInt256), (9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 5218 ((192 : UInt256)) ((9848759918901945995 : UInt256)) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2967 := soundS (opAt 2967 .XOR)
    (blockOfS _ (pcFactS input 2967 5219 [(UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 5219 ((UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))) ((MachineState.readWord input ((992 : UInt256)).toNat)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2968 := soundS (opAt 2968 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 2968 5220 [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 5220 3 (by decide) [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 2969 .OR)
    (blockOfS _ (pcFactS input 2969 5221 [acc, (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 5221 (acc) ((UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2970 := soundS (opAt 2970 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 2970 5222 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2970)
      (stepS_swap input 5222 2 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2971 := soundS (opAt 2971 .POP)
    (blockOfS _ (pcFactS input 2971 5223 [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_pop input 5223 (acc) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2972 := soundS (opAt 2972 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 2972 5224 [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2972)
      (stepS_swap input 5224 1 (by decide) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2973 := soundS (opAt 2973 (.Swap ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 2973 5225 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by norm_num) pc2973)
      (stepS_swap input 5225 6 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by rfl) (by simp) (by norm_num)))
  have step2974 := soundS (opAt 2974 .POP)
    (blockOfS _ (pcFactS input 2974 5226 [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2974)
      (stepS_pop input 5226 (m8) [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2975 := soundS (opAt 2975 .POP)
    (blockOfS _ (pcFactS input 2975 5227 [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2975)
      (stepS_pop input 5227 (ov) [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2976 := soundS (opAt 2976 .POP)
    (blockOfS _ (pcFactS input 2976 5228 [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2976)
      (stepS_pop input 5228 (sv) [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2977 := soundS (opAt 2977 .POP)
    (blockOfS _ (pcFactS input 2977 5229 [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2977)
      (stepS_pop input 5229 (P7) [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2978 := soundS (opAt 2978 .POP)
    (blockOfS _ (pcFactS input 2978 5230 [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2978)
      (stepS_pop input 5230 (M) [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2979 := soundS (opAt 2979 .POP)
    (blockOfS _ (pcFactS input 2979 5231 [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2979)
      (stepS_pop input 5231 (m7) [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2980 := soundS (opAt 2980 .POP)
    (blockOfS _ (pcFactS input 2980 5232 [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2980)
      (stepS_pop input 5232 (P) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2981 := soundS (pushAt 2981 2 0x03ee)
    (blockOfS _ (pcFactS input 2981 5233 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2981)
      (stepS_push input 5233 2 (1006 : UInt256) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by decide) (by decide) (by norm_num)))
  have step2982 := soundS (opAt 2982 .JUMPI)
    (blockOfS _ (pcFactS input 2982 5236 [(1006 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2982)
      (stepS_jumpi_taken input 5236 1006 ((1006 : UInt256)) ((UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) [] (by simp) (by norm_num) rfl hc hdest1006))
  exact step2962.trans (step2963.trans (step2964.trans (step2965.trans (step2966.trans (step2967.trans (step2968.trans (step2969.trans (step2970.trans (step2971.trans (step2972.trans (step2973.trans (step2974.trans (step2975.trans (step2976.trans (step2977.trans (step2978.trans (step2979.trans (step2980.trans (step2981.trans (step2982))))))))))))))))))))

/-- The accumulator once the padded tail word has been folded in. -/
def scanAccFinal (input : ByteArray) : UInt256 :=
  UInt256.lor (scanAcc input 31)
    (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
      (MachineState.readWord input 992))

theorem isTrue_iff (x : UInt256) : UInt256.isTrue x ↔ x ≠ 0 := by
  unfold UInt256.isTrue
  have hz : (0 : UInt256).toNat = 0 := by decide
  exact ⟨fun h hx => h (by rw [hx, hz]),
    fun h hx => h (Challenge.EvmProof.Word.word_ext (by rw [hx, hz]))⟩

private theorem tail_read (input : ByteArray) :
    MachineState.readWord input ((992 : UInt256)).toNat =
      MachineState.readWord input 992 := by
  rw [show ((992 : UInt256)).toNat = 992 from by decide]

private theorem tail_state_eq (input : ByteArray) :
    tailState input (scanAcc input 31) =
      stS input 5203 [UInt256.ofNat (scalarAt 31), UInt256.ofNat 992,
        scanAcc input 31, P7, M, m7, P, m8] := rfl

/-- A zero accumulator means the calldata is the vector, so the guard answers. -/
def gasSteps_tail_hit (input : ByteArray) (hz : scanAccFinal input = 0) :
    GasSteps (tailState input (scanAcc input 31)) (hitState input) := by
  have hc : ¬ UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact fun h => h hz
  rw [tail_state_eq, show hitState input = stS input 5237 [] from rfl]
  exact gasSteps_tail_hit_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) hc

/-- A nonzero accumulator means the program has to run. -/
def gasSteps_tail_miss (input : ByteArray) (hnz : scanAccFinal input ≠ 0) :
    GasSteps (tailState input (scanAcc input 31)) (fallbackState input) := by
  have hc : UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact hnz
  rw [tail_state_eq, show fallbackState input = stS input 1006 [] from rfl]
  exact gasSteps_tail_miss_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) hc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

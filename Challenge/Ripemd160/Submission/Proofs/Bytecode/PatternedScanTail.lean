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

theorem hdest1006 : Decode.isValidJumpDest submissionBytecode 0x3 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2 (by rfl)

/-- The accumulator is zero, so the guard answers. -/
def gasSteps_tail_hit_sym (input : ByteArray) (sv ov acc : UInt256) (hov : ov = (992 : UInt256)) (hc : ¬ UInt256.isTrue (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 391 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 423 []) := by
  subst hov
  have step2962 := soundS (opAt 231 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 231 0x187 [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2962)
      (stepS_dup input 0x187 1 (by decide) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (992 : UInt256) (by rfl) (by simp) (by norm_num)))
  have step2963 := soundS (opAt 232 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 232 0x188 [(992 : UInt256), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2963)
      (stepS_calldataload input 0x188 ((992 : UInt256)) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 233 8 9848759918901945995)
    (blockOfS _ (pcFactS input 233 0x189 [(MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 0x189 8 (9848759918901945995 : UInt256) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 234 1 192)
    (blockOfS _ (pcFactS input 234 0x192 [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 0x192 1 (192 : UInt256) [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 235 .SHL)
    (blockOfS _ (pcFactS input 235 0x194 [(192 : UInt256), (9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 0x194 ((192 : UInt256)) ((9848759918901945995 : UInt256)) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2967 := soundS (opAt 236 .XOR)
    (blockOfS _ (pcFactS input 236 0x195 [(UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 0x195 ((UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))) ((MachineState.readWord input ((992 : UInt256)).toNat)) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2968 := soundS (opAt 237 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 237 0x196 [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 0x196 3 (by decide) [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 238 .OR)
    (blockOfS _ (pcFactS input 238 0x197 [acc, (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 0x197 (acc) ((UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have cleanupJD := soundS (opAt 239 .JUMPDEST)
    (blockOfS _ (pcFactS input 239 408 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) (by rfl))
      (stepS_jumpdest input 408 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2970 := soundS (opAt 240 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 240 0x199 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2970)
      (stepS_swap input 0x199 2 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] [acc, sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2971 := soundS (opAt 241 .POP)
    (blockOfS _ (pcFactS input 241 0x19a [acc, sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_pop input 0x19a (acc) [sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2972 := soundS (opAt 242 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 242 0x19b [sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2972)
      (stepS_swap input 0x19b 1 (by decide) [sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), (992 : UInt256), sv, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2973 := soundS (opAt 243 (.Swap ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 243 0x19c [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), (992 : UInt256), sv, P7, M, m7, P, m8] (by norm_num) pc2973)
      (stepS_swap input 0x19c 6 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), (992 : UInt256), sv, P7, M, m7, P, m8] [m8, (992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by rfl) (by simp) (by norm_num)))
  have step2974 := soundS (opAt 244 .POP)
    (blockOfS _ (pcFactS input 244 0x19d [m8, (992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2974)
      (stepS_pop input 0x19d (m8) [(992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2975 := soundS (opAt 245 .POP)
    (blockOfS _ (pcFactS input 245 0x19e [(992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2975)
      (stepS_pop input 0x19e ((992 : UInt256)) [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2976 := soundS (opAt 246 .POP)
    (blockOfS _ (pcFactS input 246 0x19f [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2976)
      (stepS_pop input 0x19f (sv) [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2977 := soundS (opAt 247 .POP)
    (blockOfS _ (pcFactS input 247 0x1a0 [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2977)
      (stepS_pop input 0x1a0 (P7) [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2978 := soundS (opAt 248 .POP)
    (blockOfS _ (pcFactS input 248 0x1a1 [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2978)
      (stepS_pop input 0x1a1 (M) [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2979 := soundS (opAt 249 .POP)
    (blockOfS _ (pcFactS input 249 0x1a2 [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2979)
      (stepS_pop input 0x1a2 (m7) [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2980 := soundS (opAt 250 .POP)
    (blockOfS _ (pcFactS input 250 0x1a3 [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2980)
      (stepS_pop input 0x1a3 (P) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2981 := soundS (pushAt 251 1 3)
    (blockOfS _ (pcFactS input 251 0x1a4 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2981)
      (stepS_push input 0x1a4 1 (3 : UInt256) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by decide) (by decide) (by norm_num)))
  have step2982 := soundS (opAt 252 .JUMPI)
    (blockOfS _ (pcFactS input 252 0x1a6 [(3 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2982)
      (stepS_jumpi_fall input 0x1a6 ((3 : UInt256)) ((UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) [] (by simp) (by norm_num) hc))
  exact step2962.trans (step2963.trans (step2964.trans (step2965.trans (step2966.trans (step2967.trans (step2968.trans (step2969.trans ((cleanupJD.trans step2970).trans (step2971.trans (step2972.trans (step2973.trans (step2974.trans (step2975.trans (step2976.trans (step2977.trans (step2978.trans (step2979.trans (step2980.trans (step2981.trans (step2982))))))))))))))))))))

/-- The accumulator is nonzero, so the program runs. -/
def gasSteps_tail_miss_sym (input : ByteArray) (sv ov acc : UInt256) (hov : ov = (992 : UInt256)) (hc : UInt256.isTrue (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 391 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 3 []) := by
  subst hov
  have step2962 := soundS (opAt 231 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 231 0x187 [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2962)
      (stepS_dup input 0x187 1 (by decide) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (992 : UInt256) (by rfl) (by simp) (by norm_num)))
  have step2963 := soundS (opAt 232 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 232 0x188 [(992 : UInt256), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2963)
      (stepS_calldataload input 0x188 ((992 : UInt256)) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 233 8 9848759918901945995)
    (blockOfS _ (pcFactS input 233 0x189 [(MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 0x189 8 (9848759918901945995 : UInt256) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 234 1 192)
    (blockOfS _ (pcFactS input 234 0x192 [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 0x192 1 (192 : UInt256) [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 235 .SHL)
    (blockOfS _ (pcFactS input 235 0x194 [(192 : UInt256), (9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 0x194 ((192 : UInt256)) ((9848759918901945995 : UInt256)) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2967 := soundS (opAt 236 .XOR)
    (blockOfS _ (pcFactS input 236 0x195 [(UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)), (MachineState.readWord input ((992 : UInt256)).toNat), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 0x195 ((UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))) ((MachineState.readWord input ((992 : UInt256)).toNat)) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2968 := soundS (opAt 237 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 237 0x196 [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 0x196 3 (by decide) [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 238 .OR)
    (blockOfS _ (pcFactS input 238 0x197 [acc, (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 0x197 (acc) ((UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))) [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have cleanupJD := soundS (opAt 239 .JUMPDEST)
    (blockOfS _ (pcFactS input 239 408 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) (by rfl))
      (stepS_jumpdest input 408 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2970 := soundS (opAt 240 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 240 0x199 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2970)
      (stepS_swap input 0x199 2 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, (992 : UInt256), acc, P7, M, m7, P, m8] [acc, sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2971 := soundS (opAt 241 .POP)
    (blockOfS _ (pcFactS input 241 0x19a [acc, sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_pop input 0x19a (acc) [sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2972 := soundS (opAt 242 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 242 0x19b [sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2972)
      (stepS_swap input 0x19b 1 (by decide) [sv, (992 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), (992 : UInt256), sv, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2973 := soundS (opAt 243 (.Swap ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 243 0x19c [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), (992 : UInt256), sv, P7, M, m7, P, m8] (by norm_num) pc2973)
      (stepS_swap input 0x19c 6 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), (992 : UInt256), sv, P7, M, m7, P, m8] [m8, (992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by rfl) (by simp) (by norm_num)))
  have step2974 := soundS (opAt 244 .POP)
    (blockOfS _ (pcFactS input 244 0x19d [m8, (992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2974)
      (stepS_pop input 0x19d (m8) [(992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2975 := soundS (opAt 245 .POP)
    (blockOfS _ (pcFactS input 245 0x19e [(992 : UInt256), sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2975)
      (stepS_pop input 0x19e ((992 : UInt256)) [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2976 := soundS (opAt 246 .POP)
    (blockOfS _ (pcFactS input 246 0x19f [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2976)
      (stepS_pop input 0x19f (sv) [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2977 := soundS (opAt 247 .POP)
    (blockOfS _ (pcFactS input 247 0x1a0 [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2977)
      (stepS_pop input 0x1a0 (P7) [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2978 := soundS (opAt 248 .POP)
    (blockOfS _ (pcFactS input 248 0x1a1 [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2978)
      (stepS_pop input 0x1a1 (M) [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2979 := soundS (opAt 249 .POP)
    (blockOfS _ (pcFactS input 249 0x1a2 [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2979)
      (stepS_pop input 0x1a2 (m7) [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2980 := soundS (opAt 250 .POP)
    (blockOfS _ (pcFactS input 250 0x1a3 [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2980)
      (stepS_pop input 0x1a3 (P) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2981 := soundS (pushAt 251 1 3)
    (blockOfS _ (pcFactS input 251 0x1a4 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2981)
      (stepS_push input 0x1a4 1 (3 : UInt256) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by decide) (by decide) (by norm_num)))
  have step2982 := soundS (opAt 252 .JUMPI)
    (blockOfS _ (pcFactS input 252 0x1a6 [(3 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2982)
      (stepS_jumpi_taken input 0x1a6 3 ((3 : UInt256)) ((UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) [] (by simp) (by norm_num) rfl hc hdest1006))
  exact step2962.trans (step2963.trans (step2964.trans (step2965.trans (step2966.trans (step2967.trans (step2968.trans (step2969.trans ((cleanupJD.trans step2970).trans (step2971.trans (step2972.trans (step2973.trans (step2974.trans (step2975.trans (step2976.trans (step2977.trans (step2978.trans (step2979.trans (step2980.trans (step2981.trans (step2982))))))))))))))))))))

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
      stS input 391 [UInt256.ofNat (scalarAt 31), UInt256.ofNat 992,
        scanAcc input 31, P7, M, m7, P, m8] := rfl

/-- A zero accumulator means the calldata is the vector, so the guard answers. -/
def gasSteps_tail_hit (input : ByteArray) (hz : scanAccFinal input = 0) :
    GasSteps (tailState input (scanAcc input 31)) (hitState input) := by
  have hc : ¬ UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact fun h => h hz
  rw [tail_state_eq, show hitState input = stS input 423 [] from rfl]
  exact gasSteps_tail_hit_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) (by rfl) hc

/-- A nonzero accumulator means the program has to run. -/
def gasSteps_tail_miss (input : ByteArray) (hnz : scanAccFinal input ≠ 0) :
    GasSteps (tailState input (scanAcc input 31)) (fallbackState input) := by
  have hc : UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact hnz
  rw [tail_state_eq, show fallbackState input = stS input 3 [] from rfl]
  exact gasSteps_tail_miss_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) (by rfl) hc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

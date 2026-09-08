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

theorem hdest1006 : Decode.isValidJumpDest submissionBytecode 0x16c = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 201 (by rfl)

/-- The accumulator is zero, so the guard answers. -/
def gasSteps_tail_hit_sym (input : ByteArray) (sv ov acc : UInt256) (hc : ¬ UInt256.isTrue (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 263 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 297 []) := by
  have step2962 := soundS (pushAt 141 2 992)
    (blockOfS _ (pcFactS input 141 0x107 [sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2962)
      (stepS_push input 0x107 2 (992 : UInt256) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2963 := soundS (opAt 142 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 142 0x10a [(992 : UInt256), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2963)
      (stepS_calldataload input 0x10a ((992 : UInt256)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 143 8 9848759918901945995)
    (blockOfS _ (pcFactS input 143 0x10b [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 0x10b 8 (9848759918901945995 : UInt256) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 144 1 192)
    (blockOfS _ (pcFactS input 144 0x114 [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 0x114 1 (192 : UInt256) [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 145 .SHL)
    (blockOfS _ (pcFactS input 145 0x116 [(192 : UInt256), (9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 0x116 ((192 : UInt256)) ((9848759918901945995 : UInt256)) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2967 := soundS (opAt 146 .XOR)
    (blockOfS _ (pcFactS input 146 0x117 [(UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 0x117 ((UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))) ((MachineState.readWord input ((992 : UInt256)).toNat)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2968 := soundS (opAt 147 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 147 0x118 [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 0x118 3 (by decide) [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 148 .OR)
    (blockOfS _ (pcFactS input 148 0x119 [acc, (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 0x119 (acc) ((UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2970 := soundS (opAt 149 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 149 0x11a [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2970)
      (stepS_swap input 0x11a 2 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2971 := soundS (opAt 150 .POP)
    (blockOfS _ (pcFactS input 150 0x11b [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_pop input 0x11b (acc) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2972 := soundS (opAt 151 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 151 0x11c [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2972)
      (stepS_swap input 0x11c 1 (by decide) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2973 := soundS (opAt 152 (.Swap ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 152 0x11d [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by norm_num) pc2973)
      (stepS_swap input 0x11d 6 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by rfl) (by simp) (by norm_num)))
  have step2974 := soundS (opAt 153 .POP)
    (blockOfS _ (pcFactS input 153 0x11e [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2974)
      (stepS_pop input 0x11e (m8) [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2975 := soundS (opAt 154 .POP)
    (blockOfS _ (pcFactS input 154 0x11f [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2975)
      (stepS_pop input 0x11f (ov) [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2976 := soundS (opAt 155 .POP)
    (blockOfS _ (pcFactS input 155 0x120 [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2976)
      (stepS_pop input 0x120 (sv) [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2977 := soundS (opAt 156 .POP)
    (blockOfS _ (pcFactS input 156 0x121 [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2977)
      (stepS_pop input 0x121 (P7) [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2978 := soundS (opAt 157 .POP)
    (blockOfS _ (pcFactS input 157 0x122 [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2978)
      (stepS_pop input 0x122 (M) [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2979 := soundS (opAt 158 .POP)
    (blockOfS _ (pcFactS input 158 0x123 [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2979)
      (stepS_pop input 0x123 (m7) [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2980 := soundS (opAt 159 .POP)
    (blockOfS _ (pcFactS input 159 0x124 [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2980)
      (stepS_pop input 0x124 (P) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2981 := soundS (pushAt 160 2 364)
    (blockOfS _ (pcFactS input 160 0x125 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2981)
      (stepS_push input 0x125 2 (364 : UInt256) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by decide) (by decide) (by norm_num)))
  have step2982 := soundS (opAt 161 .JUMPI)
    (blockOfS _ (pcFactS input 161 0x128 [(364 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2982)
      (stepS_jumpi_fall input 0x128 ((364 : UInt256)) ((UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) [] (by simp) (by norm_num) hc))
  exact step2962.trans (step2963.trans (step2964.trans (step2965.trans (step2966.trans (step2967.trans (step2968.trans (step2969.trans (step2970.trans (step2971.trans (step2972.trans (step2973.trans (step2974.trans (step2975.trans (step2976.trans (step2977.trans (step2978.trans (step2979.trans (step2980.trans (step2981.trans (step2982))))))))))))))))))))

/-- The accumulator is nonzero, so the program runs. -/
def gasSteps_tail_miss_sym (input : ByteArray) (sv ov acc : UInt256) (hc : UInt256.isTrue (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 263 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 364 []) := by
  have step2962 := soundS (pushAt 141 2 992)
    (blockOfS _ (pcFactS input 141 0x107 [sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2962)
      (stepS_push input 0x107 2 (992 : UInt256) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2963 := soundS (opAt 142 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 142 0x10a [(992 : UInt256), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2963)
      (stepS_calldataload input 0x10a ((992 : UInt256)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 143 8 9848759918901945995)
    (blockOfS _ (pcFactS input 143 0x10b [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 0x10b 8 (9848759918901945995 : UInt256) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 144 1 192)
    (blockOfS _ (pcFactS input 144 0x114 [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 0x114 1 (192 : UInt256) [(9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 145 .SHL)
    (blockOfS _ (pcFactS input 145 0x116 [(192 : UInt256), (9848759918901945995 : UInt256), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 0x116 ((192 : UInt256)) ((9848759918901945995 : UInt256)) [(MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2967 := soundS (opAt 146 .XOR)
    (blockOfS _ (pcFactS input 146 0x117 [(UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)), (MachineState.readWord input ((992 : UInt256)).toNat), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 0x117 ((UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))) ((MachineState.readWord input ((992 : UInt256)).toNat)) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2968 := soundS (opAt 147 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 147 0x118 [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 0x118 3 (by decide) [(UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (acc) (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 148 .OR)
    (blockOfS _ (pcFactS input 148 0x119 [acc, (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 0x119 (acc) ((UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))) [sv, ov, acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2970 := soundS (opAt 149 (.Swap ⟨2, by decide⟩))
    (blockOfS _ (pcFactS input 149 0x11a [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] (by norm_num) pc2970)
      (stepS_swap input 0x11a 2 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), sv, ov, acc, P7, M, m7, P, m8] [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2971 := soundS (opAt 150 .POP)
    (blockOfS _ (pcFactS input 150 0x11b [acc, sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2971)
      (stepS_pop input 0x11b (acc) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step2972 := soundS (opAt 151 (.Swap ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 151 0x11c [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] (by norm_num) pc2972)
      (stepS_swap input 0x11c 1 (by decide) [sv, ov, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), P7, M, m7, P, m8] [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by rfl) (by simp) (by norm_num)))
  have step2973 := soundS (opAt 152 (.Swap ⟨6, by decide⟩))
    (blockOfS _ (pcFactS input 152 0x11d [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] (by norm_num) pc2973)
      (stepS_swap input 0x11d 6 (by decide) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat))), ov, sv, P7, M, m7, P, m8] [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by rfl) (by simp) (by norm_num)))
  have step2974 := soundS (opAt 153 .POP)
    (blockOfS _ (pcFactS input 153 0x11e [m8, ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2974)
      (stepS_pop input 0x11e (m8) [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2975 := soundS (opAt 154 .POP)
    (blockOfS _ (pcFactS input 154 0x11f [ov, sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2975)
      (stepS_pop input 0x11f (ov) [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2976 := soundS (opAt 155 .POP)
    (blockOfS _ (pcFactS input 155 0x120 [sv, P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2976)
      (stepS_pop input 0x120 (sv) [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2977 := soundS (opAt 156 .POP)
    (blockOfS _ (pcFactS input 156 0x121 [P7, M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2977)
      (stepS_pop input 0x121 (P7) [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2978 := soundS (opAt 157 .POP)
    (blockOfS _ (pcFactS input 157 0x122 [M, m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2978)
      (stepS_pop input 0x122 (M) [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2979 := soundS (opAt 158 .POP)
    (blockOfS _ (pcFactS input 158 0x123 [m7, P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2979)
      (stepS_pop input 0x123 (m7) [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2980 := soundS (opAt 159 .POP)
    (blockOfS _ (pcFactS input 159 0x124 [P, (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2980)
      (stepS_pop input 0x124 (P) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by norm_num)))
  have step2981 := soundS (pushAt 160 2 364)
    (blockOfS _ (pcFactS input 160 0x125 [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2981)
      (stepS_push input 0x125 2 (364 : UInt256) [(UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by simp) (by decide) (by decide) (by norm_num)))
  have step2982 := soundS (opAt 161 .JUMPI)
    (blockOfS _ (pcFactS input 161 0x128 [(364 : UInt256), (UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))] (by norm_num) pc2982)
      (stepS_jumpi_taken input 0x128 364 ((364 : UInt256)) ((UInt256.lor acc (UInt256.xor (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) [] (by simp) (by norm_num) rfl hc hdest1006))
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
      stS input 263 [UInt256.ofNat (scalarAt 31), UInt256.ofNat 992,
        scanAcc input 31, P7, M, m7, P, m8] := rfl

/-- A zero accumulator means the calldata is the vector, so the guard answers. -/
def gasSteps_tail_hit (input : ByteArray) (hz : scanAccFinal input = 0) :
    GasSteps (tailState input (scanAcc input 31)) (hitState input) := by
  have hc : ¬ UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact fun h => h hz
  rw [tail_state_eq, show hitState input = stS input 297 [] from rfl]
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
  rw [tail_state_eq, show fallbackState input = stS input 364 [] from rfl]
  exact gasSteps_tail_miss_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) hc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

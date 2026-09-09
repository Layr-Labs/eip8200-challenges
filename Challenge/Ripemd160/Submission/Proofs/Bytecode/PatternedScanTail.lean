import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# The padded tail word and the miss test

Bytes 992 to 999 are read as a whole word, so the constant is shifted up to
meet the zero padding.  A successful comparison carries the scan frame into
the return block.  A miss jumps to the cleanup block appended to the program,
which restores the original empty-stack fallback state.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

theorem hdest1006 : Decode.isValidJumpDest submissionBytecode 0x3 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 2 (by rfl)

theorem hdestCleanup : Decode.isValidJumpDest submissionBytecode 5310 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4282 (by rfl)

/-- Fold the padded final word into the accumulator and stop immediately
before the conditional branch. -/
def gasSteps_tail_test_sym (input : ByteArray) (sv ov acc : UInt256)
    (hov : ov = (992 : UInt256)) :
    GasSteps (stS input 360 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 377 [UInt256.lor acc
        (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
          (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)),
        sv, (992 : UInt256), acc, P7, M, m7, P, m8]) := by
  subst hov
  have step2962 := soundS (opAt 212 (.Dup ⟨1, by decide⟩))
    (blockOfS _ (pcFactS input 212 0x168
      [sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2962)
      (stepS_dup input 0x168 1 (by decide)
        [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (992 : UInt256) (by rfl) (by simp) (by norm_num)))
  have step2963 := soundS (opAt 213 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 213 0x169
      [(992 : UInt256), sv, (992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pc2963)
      (stepS_calldataload input 0x169 (992 : UInt256)
        [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2964 := soundS (pushAt 214 8 9848759918901945995)
    (blockOfS _ (pcFactS input 214 0x16a
      [MachineState.readWord input ((992 : UInt256)).toNat, sv,
        (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2964)
      (stepS_push input 0x16a 8 (9848759918901945995 : UInt256)
        [MachineState.readWord input ((992 : UInt256)).toNat, sv,
          (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2965 := soundS (pushAt 215 1 192)
    (blockOfS _ (pcFactS input 215 0x173
      [(9848759918901945995 : UInt256),
        MachineState.readWord input ((992 : UInt256)).toNat, sv,
        (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2965)
      (stepS_push input 0x173 1 (192 : UInt256)
        [(9848759918901945995 : UInt256),
          MachineState.readWord input ((992 : UInt256)).toNat, sv,
          (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2966 := soundS (opAt 216 .SHL)
    (blockOfS _ (pcFactS input 216 0x175
      [(192 : UInt256), (9848759918901945995 : UInt256),
        MachineState.readWord input ((992 : UInt256)).toNat, sv,
        (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2966)
      (stepS_shl input 0x175 (192 : UInt256)
        (9848759918901945995 : UInt256)
        [MachineState.readWord input ((992 : UInt256)).toNat, sv,
          (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2967 := soundS (opAt 217 .XOR)
    (blockOfS _ (pcFactS input 217 0x176
      [UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256),
        MachineState.readWord input ((992 : UInt256)).toNat, sv,
        (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2967)
      (stepS_xor input 0x176
        (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat)
        [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2968 := soundS (opAt 218 (.Dup ⟨3, by decide⟩))
    (blockOfS _ (pcFactS input 218 0x177
      [UInt256.xor
          (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))
          (MachineState.readWord input ((992 : UInt256)).toNat),
        sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2968)
      (stepS_dup input 0x177 3 (by decide)
        [UInt256.xor
            (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))
            (MachineState.readWord input ((992 : UInt256)).toNat),
          sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        acc (by rfl) (by simp) (by norm_num)))
  have step2969 := soundS (opAt 219 .OR)
    (blockOfS _ (pcFactS input 219 0x178
      [acc, UInt256.xor
          (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))
          (MachineState.readWord input ((992 : UInt256)).toNat),
        sv, (992 : UInt256), acc, P7, M, m7, P, m8] (by norm_num) pc2969)
      (stepS_or input 0x178 acc
        (UInt256.xor
          (UInt256.shiftLeft (9848759918901945995 : UInt256) (192 : UInt256))
          (MachineState.readWord input ((992 : UInt256)).toNat))
        [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  exact step2962.trans (step2963.trans (step2964.trans (step2965.trans
    (step2966.trans (step2967.trans (step2968.trans step2969))))))

/-- A zero accumulator falls through to the return block while retaining the
scan frame below the digest construction. -/
def gasSteps_tail_hit_sym (input : ByteArray) (sv ov acc : UInt256)
    (hov : ov = (992 : UInt256))
    (hc : ¬ UInt256.isTrue (UInt256.lor acc
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
        (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 360 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 381 [sv, (992 : UInt256), acc, P7, M, m7, P, m8]) := by
  subst hov
  have initialSteps := gasSteps_tail_test_sym input sv (992 : UInt256) acc rfl
  have step2970 := soundS (pushAt 220 2 5310)
    (blockOfS _ (pcFactS input 220 0x179
      [UInt256.lor acc
          (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
            (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)),
        sv, (992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pc2970)
      (stepS_push input 0x179 2 (5310 : UInt256)
        [UInt256.lor acc
            (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
              (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)),
          sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2971 := soundS (opAt 221 .JUMPI)
    (blockOfS _ (pcFactS input 221 0x17c
      [(5310 : UInt256), UInt256.lor acc
          (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
            (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)),
        sv, (992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pc2971)
      (stepS_jumpi_fall input 0x17c (5310 : UInt256)
        (UInt256.lor acc
          (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
            (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))
        [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num) hc))
  exact initialSteps.trans (step2970.trans step2971)

/-- The appended cleanup block removes the retained scan frame and rejoins the
original fallback entry. -/
def gasSteps_cleanup_sym (input : ByteArray) (sv acc : UInt256) :
    GasSteps (stS input 5310 [sv, (992 : UInt256), acc, P7, M, m7, P, m8])
      (stS input 3 []) := by
  have step0 := soundS (opAt 4282 .JUMPDEST)
    (blockOfS _ (pcFactS input 4282 5310
      [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pcCleanup0)
      (stepS_jumpdest input 5310
        [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step1 := soundS (opAt 4283 .POP)
    (blockOfS _ (pcFactS input 4283 5311
      [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pcCleanup1)
      (stepS_pop input 5311 sv
        [(992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step2 := soundS (opAt 4284 .POP)
    (blockOfS _ (pcFactS input 4284 5312
      [(992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pcCleanup2)
      (stepS_pop input 5312 (992 : UInt256)
        [acc, P7, M, m7, P, m8] (by simp) (by norm_num)))
  have step3 := soundS (opAt 4285 .POP)
    (blockOfS _ (pcFactS input 4285 5313 [acc, P7, M, m7, P, m8]
      (by norm_num) pcCleanup3)
      (stepS_pop input 5313 acc [P7, M, m7, P, m8]
        (by simp) (by norm_num)))
  have step4 := soundS (opAt 4286 .POP)
    (blockOfS _ (pcFactS input 4286 5314 [P7, M, m7, P, m8]
      (by norm_num) pcCleanup4)
      (stepS_pop input 5314 P7 [M, m7, P, m8]
        (by simp) (by norm_num)))
  have step5 := soundS (opAt 4287 .POP)
    (blockOfS _ (pcFactS input 4287 5315 [M, m7, P, m8]
      (by norm_num) pcCleanup5)
      (stepS_pop input 5315 M [m7, P, m8]
        (by simp) (by norm_num)))
  have step6 := soundS (opAt 4288 .POP)
    (blockOfS _ (pcFactS input 4288 5316 [m7, P, m8]
      (by norm_num) pcCleanup6)
      (stepS_pop input 5316 m7 [P, m8]
        (by simp) (by norm_num)))
  have step7 := soundS (opAt 4289 .POP)
    (blockOfS _ (pcFactS input 4289 5317 [P, m8]
      (by norm_num) pcCleanup7)
      (stepS_pop input 5317 P [m8]
        (by simp) (by norm_num)))
  have step8 := soundS (opAt 4290 .POP)
    (blockOfS _ (pcFactS input 4290 5318 [m8]
      (by norm_num) pcCleanup8)
      (stepS_pop input 5318 m8 [] (by simp) (by norm_num)))
  have step9 := soundS (pushAt 4291 1 3)
    (blockOfS _ (pcFactS input 4291 5319 [] (by norm_num) pcCleanup9)
      (stepS_push input 5319 1 (3 : UInt256) []
        (by simp) (by decide) (by decide) (by norm_num)))
  have step10 := soundS (opAt 4292 .JUMP)
    (blockOfS _ (pcFactS input 4292 5321 [(3 : UInt256)]
      (by norm_num) pcCleanup10)
      (stepS_jump input 5321 3 (3 : UInt256) []
        (by simp) (by norm_num) rfl hdest1006))
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans
    (step5.trans (step6.trans (step7.trans (step8.trans
      (step9.trans step10)))))))))

/-- A nonzero accumulator takes the deferred cleanup branch and then runs the
ordinary fallback. -/
def gasSteps_tail_miss_sym (input : ByteArray) (sv ov acc : UInt256)
    (hov : ov = (992 : UInt256))
    (hc : UInt256.isTrue (UInt256.lor acc
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
        (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))) :
    GasSteps (stS input 360 [sv, ov, acc, P7, M, m7, P, m8])
      (stS input 3 []) := by
  subst hov
  have initialSteps := gasSteps_tail_test_sym input sv (992 : UInt256) acc rfl
  have step2970 := soundS (pushAt 220 2 5310)
    (blockOfS _ (pcFactS input 220 0x179
      [UInt256.lor acc
          (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
            (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)),
        sv, (992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pc2970)
      (stepS_push input 0x179 2 (5310 : UInt256)
        [UInt256.lor acc
            (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
              (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)),
          sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by decide) (by decide) (by norm_num)))
  have step2971 := soundS (opAt 221 .JUMPI)
    (blockOfS _ (pcFactS input 221 0x17c
      [(5310 : UInt256), UInt256.lor acc
          (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
            (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)),
        sv, (992 : UInt256), acc, P7, M, m7, P, m8]
      (by norm_num) pc2971)
      (stepS_jumpi_taken input 0x17c 5310 (5310 : UInt256)
        (UInt256.lor acc
          (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256)
            (192 : UInt256)) (MachineState.readWord input ((992 : UInt256)).toNat)))
        [sv, (992 : UInt256), acc, P7, M, m7, P, m8]
        (by simp) (by norm_num) rfl hc hdestCleanup))
  exact initialSteps.trans (step2970.trans
    (step2971.trans (gasSteps_cleanup_sym input sv acc)))

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
      stS input 360 [UInt256.ofNat (scalarAt 31), UInt256.ofNat 992,
        scanAcc input 31, P7, M, m7, P, m8] := rfl

/-- A zero accumulator means the calldata is the vector, so the guard answers. -/
def gasSteps_tail_hit (input : ByteArray) (hz : scanAccFinal input = 0) :
    GasSteps (tailState input (scanAcc input 31)) (hitState input) := by
  have hc : ¬ UInt256.isTrue (UInt256.lor (scanAcc input 31)
      (UInt256.xor (UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256))
        (MachineState.readWord input ((992 : UInt256)).toNat))) := by
    rw [tail_read, isTrue_iff]
    exact fun h => h hz
  rw [tail_state_eq,
    show hitState input = stS input 381 (hitRest input) from rfl,
    show hitRest input = [UInt256.ofNat (scalarAt 31), UInt256.ofNat 992,
      scanAcc input 31, P7, M, m7, P, m8] from rfl]
  exact gasSteps_tail_hit_sym input (UInt256.ofNat (scalarAt 31))
    (UInt256.ofNat 992) (scanAcc input 31) rfl hc

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
    (UInt256.ofNat 992) (scanAcc input 31) rfl hc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

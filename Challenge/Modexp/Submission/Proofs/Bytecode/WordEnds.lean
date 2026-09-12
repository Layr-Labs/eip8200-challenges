import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# The two ends of the unrolled exponent-bit block

The head derives `base - 1` once for the eight copies; the tail drops it and
jumps back to the byte loop.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
open Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

/-- The jump into the block. -/
def gasSteps_bitEntry_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 2940 = true) :
    GasSteps (stW s 553 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 2940 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step485 := soundW hs (pushAt 462 2 2940)
    (blockOfW _ (pcFactW s 462 553 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 553 2 (2940 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 463 .JUMP)
    (blockOfW _ (pcFactW s 463 556 ([(2940 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 556 2940 ((2940 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step485.trans step486

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 2940 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 11 := by
  unfold gasSteps_bitEntry_sym
  have c485 := blockCostW [pushAt 462 2 2940] 3
    (blockOfW _ (pcFactW s 462 553 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 553 2 (2940 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 463 .JUMP] 8
    (blockOfW _ (pcFactW s 463 556 ([(2940 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 556 2940 ((2940 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitBodyHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 2940 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 2945 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2361 := soundW hs (opAt 2272 .JUMPDEST)
    (blockOfW _ (pcFactW s 2272 2940 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 2940 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2362 := soundW hs (pushAt 2273 1 1)
    (blockOfW _ (pcFactW s 2273 2941 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 2941 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2363 := soundW hs (opAt 2274 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 2274 2943 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 2943 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2364 := soundW hs (opAt 2275 .SUB)
    (blockOfW _ (pcFactW s 2275 2944 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 2944 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2361.trans (step2362.trans (step2363.trans (step2364)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitBodyHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitBodyHead_sym
  have c2361 := blockCostW [opAt 2272 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 2272 2940 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 2940 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2362 := blockCostW [pushAt 2273 1 1] 3
    (blockOfW _ (pcFactW s 2273 2941 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 2941 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2363 := blockCostW [opAt 2274 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2274 2943 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 2943 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2364 := blockCostW [opAt 2275 .SUB] 3
    (blockOfW _ (pcFactW s 2275 2944 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 2944 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The deployed entry starts at the relocated body head. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 2940 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 2945 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) :=
  gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest

theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  simp only [gasSteps_bitHead_sym, gasSteps_bitBodyHead_sym_cost]

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 557 = true) :
    GasSteps (stW s 3102 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 557 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2501 := soundW hs (opAt 2410 .POP)
    (blockOfW _ (pcFactW s 2410 3102 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 3102 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2502 := soundW hs (pushAt 2411 2 557)
    (blockOfW _ (pcFactW s 2411 3103 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 3103 2 (557 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2503 := soundW hs (opAt 2412 .JUMP)
    (blockOfW _ (pcFactW s 2412 3106 ([(557 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 3106 557 ((557 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2501.trans (step2502.trans (step2503))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 557 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2501 := blockCostW [opAt 2410 .POP] 2
    (blockOfW _ (pcFactW s 2410 3102 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 3102 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2502 := blockCostW [pushAt 2411 2 557] 3
    (blockOfW _ (pcFactW s 2411 3103 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 3103 2 (557 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2503 := blockCostW [opAt 2412 .JUMP] 8
    (blockOfW _ (pcFactW s 2412 3106 ([(557 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 3106 557 ((557 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

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
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3330 = true) :
    GasSteps (stW s 584 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3330 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step484 := soundW hs (opAt 481 .JUMPDEST)
    (blockOfW _ (pcFactW s 481 584 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 584 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step485 := soundW hs (pushAt 482 2 3330)
    (blockOfW _ (pcFactW s 482 585 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 585 2 (3330 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 483 .JUMP)
    (blockOfW _ (pcFactW s 483 588 ([(3330 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 588 3330 ((3330 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step484.trans (step485.trans (step486))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3330 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 12 := by
  unfold gasSteps_bitEntry_sym
  have c484 := blockCostW [opAt 481 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 481 584 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 584 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c485 := blockCostW [pushAt 482 2 3330] 3
    (blockOfW _ (pcFactW s 482 585 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 585 2 (3330 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 483 .JUMP] 8
    (blockOfW _ (pcFactW s 483 588 ([(3330 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 588 3330 ((3330 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The preserved PC 3418 island transfers to the relocated block. -/
def gasSteps_bitBridge_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3130 = true) :
    GasSteps (stW s 3330 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3130 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step484 := soundW hs (opAt 2560 .JUMPDEST)
    (blockOfW _ (pcFactW s 2560 3330 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) wordBridgePC3418)
      (stepW_jumpdest s 3330 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step485 := soundW hs (pushAt 2561 2 3130)
    (blockOfW _ (pcFactW s 2561 3331 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) wordBridgePC3419)
      (stepW_push s 3331 2 (3130 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 2562 .JUMP)
    (blockOfW _ (pcFactW s 2562 3334 ([(3130 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) wordBridgePC3422)
      (stepW_jump s 3334 3130 ((3130 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step484.trans (step485.trans (step486))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitBridge_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3130 = true) :
    (gasSteps_bitBridge_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 12 := by
  unfold gasSteps_bitBridge_sym
  have c484 := blockCostW [opAt 2560 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 2560 3330 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) wordBridgePC3418)
      (stepW_jumpdest s 3330 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c485 := blockCostW [pushAt 2561 2 3130] 3
    (blockOfW _ (pcFactW s 2561 3331 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) wordBridgePC3419)
      (stepW_push s 3331 2 (3130 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 2562 .JUMP] 8
    (blockOfW _ (pcFactW s 2562 3334 ([(3130 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) wordBridgePC3422)
      (stepW_jump s 3334 3130 ((3130 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitBodyHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3130 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3135 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2361 := soundW hs (opAt 2400 .JUMPDEST)
    (blockOfW _ (pcFactW s 2400 3130 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 3130 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2362 := soundW hs (pushAt 2401 1 1)
    (blockOfW _ (pcFactW s 2401 3131 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 3131 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2363 := soundW hs (opAt 2402 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 2402 3133 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 3133 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2364 := soundW hs (opAt 2403 .SUB)
    (blockOfW _ (pcFactW s 2403 3134 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 3134 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2361.trans (step2362.trans (step2363.trans (step2364)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitBodyHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitBodyHead_sym
  have c2361 := blockCostW [opAt 2400 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 2400 3130 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 3130 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2362 := blockCostW [pushAt 2401 1 1] 3
    (blockOfW _ (pcFactW s 2401 3131 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 3131 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2363 := blockCostW [opAt 2402 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2402 3133 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 3133 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2364 := blockCostW [opAt 2403 .SUB] 3
    (blockOfW _ (pcFactW s 2403 3134 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 3134 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The deployed entry includes the island bridge and the relocated body head. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3330 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3135 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have hd : Decode.isValidJumpDest s.executionEnv.code 3130 = true := by
    rw [hs.code]
    exact Artifact.isValidJumpDest_index 2400 (by rfl)
  exact (gasSteps_bitBridge_sym s rest zero byte offset outerW acc base m hs hrest hd).trans
    (gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest)

theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 22 := by
  simp only [gasSteps_bitHead_sym, Challenge.EvmProof.GasSteps.trans_cost,
    gasSteps_bitBridge_sym_cost, gasSteps_bitBodyHead_sym_cost, Nat.reduceAdd]

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 628 = true) :
    GasSteps (stW s 3292 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 628 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2501 := soundW hs (opAt 2538 .POP)
    (blockOfW _ (pcFactW s 2538 3292 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 3292 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2502 := soundW hs (pushAt 2539 2 628)
    (blockOfW _ (pcFactW s 2539 3293 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 3293 2 (628 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2503 := soundW hs (opAt 2540 .JUMP)
    (blockOfW _ (pcFactW s 2540 3296 ([(628 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 3296 628 ((628 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2501.trans (step2502.trans (step2503))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 628 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2501 := blockCostW [opAt 2538 .POP] 2
    (blockOfW _ (pcFactW s 2538 3292 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 3292 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2502 := blockCostW [pushAt 2539 2 628] 3
    (blockOfW _ (pcFactW s 2539 3293 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 3293 2 (628 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2503 := blockCostW [opAt 2540 .JUMP] 8
    (blockOfW _ (pcFactW s 2540 3296 ([(628 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 3296 628 ((628 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

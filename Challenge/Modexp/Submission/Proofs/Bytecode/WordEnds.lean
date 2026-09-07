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
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3727 = true) :
    GasSteps (stW s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3727 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step484 := soundW hs (opAt 484 .JUMPDEST)
    (blockOfW _ (pcFactW s 484 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step485 := soundW hs (pushAt 485 2 3727)
    (blockOfW _ (pcFactW s 485 607 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 607 2 (3727 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 486 .JUMP)
    (blockOfW _ (pcFactW s 486 610 ([(3727 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 610 3727 ((3727 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step484.trans (step485.trans (step486))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3727 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 12 := by
  unfold gasSteps_bitEntry_sym
  have c484 := blockCostW [opAt 484 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 484 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c485 := blockCostW [pushAt 485 2 3727] 3
    (blockOfW _ (pcFactW s 485 607 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 607 2 (3727 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 486 .JUMP] 8
    (blockOfW _ (pcFactW s 486 610 ([(3727 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 610 3727 ((3727 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3727 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3732 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2431 := soundW hs (opAt 2431 .JUMPDEST)
    (blockOfW _ (pcFactW s 2431 3727 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2431)
      (stepW_jumpdest s 3727 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2432 := soundW hs (pushAt 2432 1 1)
    (blockOfW _ (pcFactW s 2432 3728 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2432)
      (stepW_push s 3728 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2433 := soundW hs (opAt 2433 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 2433 3730 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2433)
      (stepW_dup s 3730 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2434 := soundW hs (opAt 2434 .SUB)
    (blockOfW _ (pcFactW s 2434 3731 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2434)
      (stepW_sub s 3731 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2431.trans (step2432.trans (step2433.trans (step2434)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitHead_sym
  have c2431 := blockCostW [opAt 2431 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 2431 3727 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2431)
      (stepW_jumpdest s 3727 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2432 := blockCostW [pushAt 2432 1 1] 3
    (blockOfW _ (pcFactW s 2432 3728 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2432)
      (stepW_push s 3728 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2433 := blockCostW [opAt 2433 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2433 3730 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2433)
      (stepW_dup s 3730 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2434 := blockCostW [opAt 2434 .SUB] 3
    (blockOfW _ (pcFactW s 2434 3731 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2434)
      (stepW_sub s 3731 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    GasSteps (stW s 3891 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 655 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2571 := soundW hs (opAt 2571 .POP)
    (blockOfW _ (pcFactW s 2571 3891 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2571)
      (stepW_pop s 3891 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2572 := soundW hs (pushAt 2572 2 655)
    (blockOfW _ (pcFactW s 2572 3892 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2572)
      (stepW_push s 3892 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2573 := soundW hs (opAt 2573 .JUMP)
    (blockOfW _ (pcFactW s 2573 3895 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2573)
      (stepW_jump s 3895 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2571.trans (step2572.trans (step2573))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2571 := blockCostW [opAt 2571 (.POP)] 2
    (blockOfW _ (pcFactW s 2571 3891 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2571)
      (stepW_pop s 3891 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2572 := blockCostW [pushAt 2572 2 655] 3
    (blockOfW _ (pcFactW s 2572 3892 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2572)
      (stepW_push s 3892 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2573 := blockCostW [opAt 2573 (.JUMP)] 8
    (blockOfW _ (pcFactW s 2573 3895 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2573)
      (stepW_jump s 3895 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

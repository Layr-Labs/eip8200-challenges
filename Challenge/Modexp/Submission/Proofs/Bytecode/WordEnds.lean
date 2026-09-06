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
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3571 = true) :
    GasSteps (stW s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3571 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step484 := soundW hs (opAt 484 .JUMPDEST)
    (blockOfW _ (pcFactW s 484 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step485 := soundW hs (pushAt 485 2 3571)
    (blockOfW _ (pcFactW s 485 607 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 607 2 (3571 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 486 .JUMP)
    (blockOfW _ (pcFactW s 486 610 ([(3571 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 610 3571 ((3571 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step484.trans (step485.trans (step486))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3571 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 12 := by
  unfold gasSteps_bitEntry_sym
  have c484 := blockCostW [opAt 484 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 484 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c485 := blockCostW [pushAt 485 2 3571] 3
    (blockOfW _ (pcFactW s 485 607 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 607 2 (3571 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 486 .JUMP] 8
    (blockOfW _ (pcFactW s 486 610 ([(3571 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 610 3571 ((3571 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3571 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3576 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2338 := soundW hs (opAt 2338 .JUMPDEST)
    (blockOfW _ (pcFactW s 2338 3571 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2338)
      (stepW_jumpdest s 3571 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2339 := soundW hs (pushAt 2339 1 1)
    (blockOfW _ (pcFactW s 2339 3572 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2339)
      (stepW_push s 3572 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2340 := soundW hs (opAt 2340 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 2340 3574 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2340)
      (stepW_dup s 3574 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2341 := soundW hs (opAt 2341 .SUB)
    (blockOfW _ (pcFactW s 2341 3575 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2341)
      (stepW_sub s 3575 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2338.trans (step2339.trans (step2340.trans (step2341)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitHead_sym
  have c2338 := blockCostW [opAt 2338 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 2338 3571 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2338)
      (stepW_jumpdest s 3571 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2339 := blockCostW [pushAt 2339 1 1] 3
    (blockOfW _ (pcFactW s 2339 3572 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2339)
      (stepW_push s 3572 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2340 := blockCostW [opAt 2340 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2340 3574 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2340)
      (stepW_dup s 3574 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2341 := blockCostW [opAt 2341 .SUB] 3
    (blockOfW _ (pcFactW s 2341 3575 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2341)
      (stepW_sub s 3575 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    GasSteps (stW s 3736 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 655 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2478 := soundW hs (opAt 2478 .POP)
    (blockOfW _ (pcFactW s 2478 3736 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_pop s 3736 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2479 := soundW hs (pushAt 2479 2 655)
    (blockOfW _ (pcFactW s 2479 3737 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_push s 3737 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2480 := soundW hs (opAt 2480 .JUMP)
    (blockOfW _ (pcFactW s 2480 3740 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_jump s 3740 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2478.trans (step2479.trans (step2480))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2478 := blockCostW [opAt 2478 .POP] 2
    (blockOfW _ (pcFactW s 2478 3736 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2478)
      (stepW_pop s 3736 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2479 := blockCostW [pushAt 2479 2 655] 3
    (blockOfW _ (pcFactW s 2479 3737 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2479)
      (stepW_push s 3737 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2480 := blockCostW [opAt 2480 .JUMP] 8
    (blockOfW _ (pcFactW s 2480 3740 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2480)
      (stepW_jump s 3740 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

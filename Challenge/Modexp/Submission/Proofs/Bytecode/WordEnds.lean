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
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3724 = true) :
    GasSteps (stW s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3724 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step484 := soundW hs (opAt 484 .JUMPDEST)
    (blockOfW _ (pcFactW s 484 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step485 := soundW hs (pushAt 485 2 3724)
    (blockOfW _ (pcFactW s 485 607 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 607 2 (3724 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 486 .JUMP)
    (blockOfW _ (pcFactW s 486 610 ([(3724 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 610 3724 ((3724 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step484.trans (step485.trans (step486))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3724 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 12 := by
  unfold gasSteps_bitEntry_sym
  have c484 := blockCostW [opAt 484 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 484 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc484)
      (stepW_jumpdest s 606 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c485 := blockCostW [pushAt 485 2 3724] 3
    (blockOfW _ (pcFactW s 485 607 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 607 2 (3724 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 486 .JUMP] 8
    (blockOfW _ (pcFactW s 486 610 ([(3724 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 610 3724 ((3724 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3724 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3729 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2361 := soundW hs (opAt 2439 .JUMPDEST)
    (blockOfW _ (pcFactW s 2439 3724 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_jumpdest s 3724 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2362 := soundW hs (pushAt 2440 1 1)
    (blockOfW _ (pcFactW s 2440 3725 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_push s 3725 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2363 := soundW hs (opAt 2441 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 2441 3727 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_dup s 3727 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2364 := soundW hs (opAt 2442 .SUB)
    (blockOfW _ (pcFactW s 2442 3728 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_sub s 3728 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2361.trans (step2362.trans (step2363.trans (step2364)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitHead_sym
  have c2361 := blockCostW [opAt 2439 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 2439 3724 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2439)
      (stepW_jumpdest s 3724 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2362 := blockCostW [pushAt 2440 1 1] 3
    (blockOfW _ (pcFactW s 2440 3725 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2440)
      (stepW_push s 3725 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2363 := blockCostW [opAt 2441 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 2441 3727 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2441)
      (stepW_dup s 3727 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2364 := blockCostW [opAt 2442 .SUB] 3
    (blockOfW _ (pcFactW s 2442 3728 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2442)
      (stepW_sub s 3728 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    GasSteps (stW s 3889 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 655 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2501 := soundW hs (opAt 2579 .POP)
    (blockOfW _ (pcFactW s 2579 3889 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2579)
      (stepW_pop s 3889 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2502 := soundW hs (pushAt 2580 2 655)
    (blockOfW _ (pcFactW s 2580 3890 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2580)
      (stepW_push s 3890 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2503 := soundW hs (opAt 2581 .JUMP)
    (blockOfW _ (pcFactW s 2581 3893 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2581)
      (stepW_jump s 3893 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2501.trans (step2502.trans (step2503))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2501 := blockCostW [opAt 2579 .POP] 2
    (blockOfW _ (pcFactW s 2579 3889 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2579)
      (stepW_pop s 3889 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2502 := blockCostW [pushAt 2580 2 655] 3
    (blockOfW _ (pcFactW s 2580 3890 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2580)
      (stepW_push s 3890 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2503 := blockCostW [opAt 2581 .JUMP] 8
    (blockOfW _ (pcFactW s 2581 3893 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2581)
      (stepW_jump s 3893 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

import Challenge.Modexp.Submission.Proofs.Bytecode.WordStep
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# The two ends of the exponent-bit block

The head derives `base - 1` once for the eight bits; the tail drops it and
jumps back to the byte loop. (pc 5350 relayout: head 5569..5574, exit 5609..5543.)
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
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 5569 = true) :
    GasSteps (stW s 210 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 5569 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step485 := soundW hs (pushAt 139 2 5569)
    (blockOfW _ (pcFactW s 139 210 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 210 2 (5569 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 140 .JUMP)
    (blockOfW _ (pcFactW s 140 213 ([(5569 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 213 5569 ((5569 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step485.trans step486

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 5569 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 11 := by
  unfold gasSteps_bitEntry_sym
  have c485 := blockCostW [pushAt 139 2 5569] 3
    (blockOfW _ (pcFactW s 139 210 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 210 2 (5569 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 140 .JUMP] 8
    (blockOfW _ (pcFactW s 140 213
      ([(5569 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 213 5569 ((5569 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitBodyHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 5569 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 5574 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2361 := soundW hs (opAt 4452 .JUMPDEST)
    (blockOfW _ (pcFactW s 4452 5569 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 5569 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2362 := soundW hs (pushAt 4453 1 1)
    (blockOfW _ (pcFactW s 4453 5570 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 5570 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2363 := soundW hs (opAt 4454 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 4454 5572 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 5572 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2364 := soundW hs (opAt 4455 .SUB)
    (blockOfW _ (pcFactW s 4455 5573 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 5573 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2361.trans (step2362.trans (step2363.trans (step2364)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitBodyHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitBodyHead_sym
  have c2361 := blockCostW [opAt 4452 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 4452 5569 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 5569 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2362 := blockCostW [pushAt 4453 1 1] 3
    (blockOfW _ (pcFactW s 4453 5570 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 5570 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2363 := blockCostW [opAt 4454 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 4454 5572 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 5572 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2364 := blockCostW [opAt 4455 .SUB] 3
    (blockOfW _ (pcFactW s 4455 5573 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 5573 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The deployed entry starts at the relocated body head. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 5569 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 5574 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) :=
  gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest

theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  simp only [gasSteps_bitHead_sym, gasSteps_bitBodyHead_sym_cost]

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 5543 = true) :
    GasSteps (stW s 5609 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 5543 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2501 := soundW hs (opAt 4484 .POP)
    (blockOfW _ (pcFactW s 4484 5609 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 5609 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2502 := soundW hs (pushAt 4485 2 5543)
    (blockOfW _ (pcFactW s 4485 5610 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 5610 2 (5543 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2503 := soundW hs (opAt 4486 .JUMP)
    (blockOfW _ (pcFactW s 4486 5613 ([(5543 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 5613 5543 ((5543 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2501.trans (step2502.trans (step2503))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 5543 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2501 := blockCostW [opAt 4484 .POP] 2
    (blockOfW _ (pcFactW s 4484 5609 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 5609 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2502 := blockCostW [pushAt 4485 2 5543] 3
    (blockOfW _ (pcFactW s 4485 5610 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 5610 2 (5543 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2503 := blockCostW [opAt 4486 .JUMP] 8
    (blockOfW _ (pcFactW s 4486 5613 ([(5543 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 5613 5543 ((5543 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

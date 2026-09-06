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

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3027 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3032 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step1846 := soundW hs (opAt 1846 .JUMPDEST)
    (blockOfW _ (pcFactW s 1846 3027 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1846)
      (stepW_jumpdest s 3027 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1847 := soundW hs (pushAt 1847 1 1)
    (blockOfW _ (pcFactW s 1847 3028 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1847)
      (stepW_push s 3028 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1848 := soundW hs (opAt 1848 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 1848 3030 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1848)
      (stepW_dup s 3030 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step1849 := soundW hs (opAt 1849 .SUB)
    (blockOfW _ (pcFactW s 1849 3031 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1849)
      (stepW_sub s 3031 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step1846.trans (step1847.trans (step1848.trans (step1849)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitHead_sym
  have c1846 := blockCostW [opAt 1846 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 1846 3027 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1846)
      (stepW_jumpdest s 3027 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1847 := blockCostW [pushAt 1847 1 1] 3
    (blockOfW _ (pcFactW s 1847 3028 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1847)
      (stepW_push s 3028 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1848 := blockCostW [opAt 1848 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 1848 3030 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1848)
      (stepW_dup s 3030 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1849 := blockCostW [opAt 1849 .SUB] 3
    (blockOfW _ (pcFactW s 1849 3031 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1849)
      (stepW_sub s 3031 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    GasSteps (stW s 3192 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 655 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step1986 := soundW hs (opAt 1986 .POP)
    (blockOfW _ (pcFactW s 1986 3192 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1986)
      (stepW_pop s 3192 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step1987 := soundW hs (pushAt 1987 2 655)
    (blockOfW _ (pcFactW s 1987 3193 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1987)
      (stepW_push s 3193 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step1988 := soundW hs (opAt 1988 .JUMP)
    (blockOfW _ (pcFactW s 1988 3196 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1988)
      (stepW_jump s 3196 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step1986.trans (step1987.trans (step1988))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 655 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c1986 := blockCostW [opAt 1986 .POP] 2
    (blockOfW _ (pcFactW s 1986 3192 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1986)
      (stepW_pop s 3192 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1987 := blockCostW [pushAt 1987 2 655] 3
    (blockOfW _ (pcFactW s 1987 3193 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1987)
      (stepW_push s 3193 2 (655 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c1988 := blockCostW [opAt 1988 .JUMP] 8
    (blockOfW _ (pcFactW s 1988 3196 ([(655 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc1988)
      (stepW_jump s 3196 655 ((655 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds

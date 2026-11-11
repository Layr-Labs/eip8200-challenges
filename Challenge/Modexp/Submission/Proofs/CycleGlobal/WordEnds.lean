import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordStep
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# The two ends of the exponent-bit block

The head derives `base - 1` once for the eight bits; the tail drops it and
jumps back to the byte loop.
-/

namespace CycleSubmission.Global.WordEnds
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open CycleSubmission.Global.WordStep
open CycleSubmission.Global.UnrollPCs

/-- The jump into the block. -/
def gasSteps_bitEntry_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3962 = true) :
    GasSteps (stW s 203 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3962 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step485 := soundW hs (pushAt 133 2 3962)
    (blockOfW _ (pcFactW s 133 203 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 203 2 (3962 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 134 .JUMP)
    (blockOfW _ (pcFactW s 134 206 ([(3962 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 206 3962 ((3962 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step485.trans step486

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3962 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 11 := by
  unfold gasSteps_bitEntry_sym
  have c485 := blockCostW [pushAt 133 2 3962] 3
    (blockOfW _ (pcFactW s 133 203 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc485)
      (stepW_push s 203 2 (3962 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 134 .JUMP] 8
    (blockOfW _ (pcFactW s 134 206 ([(3962 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc486)
      (stepW_jump s 206 3962 ((3962 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The head, with every stack slot symbolic. -/
def gasSteps_bitBodyHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3962 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3967 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2361 := soundW hs (opAt 3037 .JUMPDEST)
    (blockOfW _ (pcFactW s 3037 3962 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 3962 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2362 := soundW hs (pushAt 3038 1 1)
    (blockOfW _ (pcFactW s 3038 3963 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 3963 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2363 := soundW hs (opAt 3039 (.Dup ⟨6, by decide⟩))
    (blockOfW _ (pcFactW s 3039 3965 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 3965 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2364 := soundW hs (opAt 3040 .SUB)
    (blockOfW _ (pcFactW s 3040 3966 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 3966 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  exact step2361.trans (step2362.trans (step2363.trans (step2364)))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitBodyHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitBodyHead_sym
  have c2361 := blockCostW [opAt 3037 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 3037 3962 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2414)
      (stepW_jumpdest s 3962 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2362 := blockCostW [pushAt 3038 1 1] 3
    (blockOfW _ (pcFactW s 3038 3963 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2415)
      (stepW_push s 3963 1 (1 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2363 := blockCostW [opAt 3039 (.Dup ⟨6, by decide⟩)] 3
    (blockOfW _ (pcFactW s 3039 3965 ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2416)
      (stepW_dup s 3965 6 (by decide) ([(1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2364 := blockCostW [opAt 3040 .SUB] 3
    (blockOfW _ (pcFactW s 3040 3966 ([base, (1 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2417)
      (stepW_sub s 3966 (base) ((1 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

/-- The deployed entry starts at the relocated body head. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 3962 ([zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3967 ([(base - (1 : UInt256)), zero, byte, offset, outerW, acc, base, m] ++ rest)) :=
  gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest

theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  simp only [gasSteps_bitHead_sym, gasSteps_bitBodyHead_sym_cost]

/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3936 = true) :
    GasSteps (stW s 4002 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest))
      (stW s 3936 ([zero, byte, offset, outerW, acc, base, m] ++ rest)) := by
  have step2501 := soundW hs (opAt 3069 .POP)
    (blockOfW _ (pcFactW s 3069 4002 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 4002 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num)))
  have step2502 := soundW hs (pushAt 3070 2 3936)
    (blockOfW _ (pcFactW s 3070 4003 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 4003 2 (3936 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2503 := soundW hs (opAt 3071 .JUMP)
    (blockOfW _ (pcFactW s 3071 4006 ([(3936 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 4006 3936 ((3936 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2501.trans (step2502.trans (step2503))

/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 3936 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2501 := blockCostW [opAt 3069 .POP] 2
    (blockOfW _ (pcFactW s 3069 4002 ([Bm1, zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2554)
      (stepW_pop s 4002 (Bm1) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2502 := blockCostW [pushAt 3070 2 3936] 3
    (blockOfW _ (pcFactW s 3070 4003 ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2555)
      (stepW_push s 4003 2 (3936 : UInt256) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2503 := blockCostW [opAt 3071 .JUMP] 8
    (blockOfW _ (pcFactW s 3071 4006 ([(3936 : UInt256), zero, byte, offset, outerW, acc, base, m] ++ rest) (by norm_num) pc2556)
      (stepW_jump s 4006 3936 ((3936 : UInt256)) ([zero, byte, offset, outerW, acc, base, m] ++ rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost, Nat.reduceAdd]
  omega

end CycleSubmission.Global.WordEnds

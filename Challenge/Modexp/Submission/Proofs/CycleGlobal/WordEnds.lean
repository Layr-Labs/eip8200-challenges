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
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 10486 = true) :
    GasSteps (stW s 203 ([zero,byte,offset,outerW,acc,base,m]++rest))
      (stW s 10486 ([zero,byte,offset,outerW,acc,base,m]++rest)) := by
  have step485 := soundW hs (pushAt 132 2 10486)
    (blockOfW _ (pcFactW s 132 203 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc485)
      (stepW_push s 203 2 (10486 : UInt256) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step486 := soundW hs (opAt 133 .JUMP)
    (blockOfW _ (pcFactW s 133 206 ([(10486 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc486)
      (stepW_jump s 206 10486 ((10486 : UInt256)) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step485.trans step486
/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitEntry_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 10486 = true) :
    (gasSteps_bitEntry_sym s rest zero byte offset outerW acc base m hs hrest hdest).cost = 11 := by
  unfold gasSteps_bitEntry_sym
  have c485 := blockCostW [pushAt 132 2 10486] 3
    (blockOfW _ (pcFactW s 132 203 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc485)
      (stepW_push s 203 2 (10486 : UInt256) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c486 := blockCostW [opAt 133 .JUMP] 8
    (blockOfW _ (pcFactW s 133 206 ([(10486 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc486)
      (stepW_jump s 206 10486 ((10486 : UInt256)) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW,Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,Nat.reduceAdd]
  omega
/-- The head, with every stack slot symbolic. -/
def gasSteps_bitBodyHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 10486 ([zero,byte,offset,outerW,acc,base,m]++rest))
      (stW s 10491 ([(base - (1 : UInt256)),zero,byte,offset,outerW,acc,base,m]++rest)) := by
  have step2361 := soundW hs (opAt 7938 .JUMPDEST)
    (blockOfW _ (pcFactW s 7938 10486 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2414)
      (stepW_jumpdest s 10486 ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num)))
  have step2362 := soundW hs (pushAt 7939 1 1)
    (blockOfW _ (pcFactW s 7939 10487 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2415)
      (stepW_push s 10487 1 (1 : UInt256) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2363 := soundW hs (opAt 7940 (.Dup ⟨6,by decide⟩))
    (blockOfW _ (pcFactW s 7940 10489 ([(1 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2416)
      (stepW_dup s 10489 6 (by decide) ([(1 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (base) (by rfl) (by simp; omega) (by norm_num)))
  have step2364 := soundW hs (opAt 7941 .SUB)
    (blockOfW _ (pcFactW s 7941 10490 ([base,(1 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2417)
      (stepW_sub s 10490 (base) ((1 : UInt256)) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num)))
  exact step2361.trans (step2362.trans (step2363.trans (step2364)))
/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitBodyHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  unfold gasSteps_bitBodyHead_sym
  have c2361 := blockCostW [opAt 7938 .JUMPDEST] 1
    (blockOfW _ (pcFactW s 7938 10486 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2414)
      (stepW_jumpdest s 10486 ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2362 := blockCostW [pushAt 7939 1 1] 3
    (blockOfW _ (pcFactW s 7939 10487 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2415)
      (stepW_push s 10487 1 (1 : UInt256) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2363 := blockCostW [opAt 7940 (.Dup ⟨6,by decide⟩)] 3
    (blockOfW _ (pcFactW s 7940 10489 ([(1 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2416)
      (stepW_dup s 10489 6 (by decide) ([(1 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (base) (by rfl) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2364 := blockCostW [opAt 7941 .SUB] 3
    (blockOfW _ (pcFactW s 7941 10490 ([base,(1 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2417)
      (stepW_sub s 10490 (base) ((1 : UInt256)) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW,Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,Nat.reduceAdd]
  omega
/-- The deployed entry starts at the relocated body head. -/
def gasSteps_bitHead_sym (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    GasSteps (stW s 10486 ([zero,byte,offset,outerW,acc,base,m]++rest))
      (stW s 10491 ([(base - (1 : UInt256)),zero,byte,offset,outerW,acc,base,m]++rest)) :=
  gasSteps_bitBodyHead_sym s rest zero byte offset outerW acc base m hs hrest
theorem gasSteps_bitHead_sym_cost (s : State) (rest : List UInt256)
    (zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) :
    (gasSteps_bitHead_sym s rest zero byte offset outerW acc base m hs hrest).cost = 10 := by
  simp only [gasSteps_bitHead_sym,gasSteps_bitBodyHead_sym_cost]
/-- The tail, with every stack slot symbolic. -/
def gasSteps_bitExit_sym (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 10460 = true) :
    GasSteps (stW s 10526 ([Bm1,zero,byte,offset,outerW,acc,base,m]++rest))
      (stW s 10460 ([zero,byte,offset,outerW,acc,base,m]++rest)) := by
  have step2501 := soundW hs (opAt 7970 .POP)
    (blockOfW _ (pcFactW s 7970 10526 ([Bm1,zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2554)
      (stepW_pop s 10526 (Bm1) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num)))
  have step2502 := soundW hs (pushAt 7971 2 10460)
    (blockOfW _ (pcFactW s 7971 10527 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2555)
      (stepW_push s 10527 2 (10460 : UInt256) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by decide) (by decide) (by norm_num)))
  have step2503 := soundW hs (opAt 7972 .JUMP)
    (blockOfW _ (pcFactW s 7972 10530 ([(10460 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2556)
      (stepW_jump s 10530 10460 ((10460 : UInt256)) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num) rfl hdest))
  exact step2501.trans (step2502.trans (step2503))
/-- The block is straight-line, so its cost is the sum of its opcodes. -/
theorem gasSteps_bitExit_sym_cost (s : State) (rest : List UInt256)
    (Bm1 zero byte offset outerW acc base m : UInt256)
    (hs : Frame s) (hrest : rest.length < 1000) (hdest : Decode.isValidJumpDest s.executionEnv.code 10460 = true) :
    (gasSteps_bitExit_sym s rest Bm1 zero byte offset outerW acc base m hs hrest hdest).cost = 13 := by
  unfold gasSteps_bitExit_sym
  have c2501 := blockCostW [opAt 7970 .POP] 2
    (blockOfW _ (pcFactW s 7970 10526 ([Bm1,zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2554)
      (stepW_pop s 10526 (Bm1) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2502 := blockCostW [pushAt 7971 2 10460] 3
    (blockOfW _ (pcFactW s 7971 10527 ([zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2555)
      (stepW_push s 10527 2 (10460 : UInt256) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by decide) (by decide) (by norm_num))) hs.fork (by decide) (by rfl) (by rfl)
  have c2503 := blockCostW [opAt 7972 .JUMP] 8
    (blockOfW _ (pcFactW s 7972 10530 ([(10460 : UInt256),zero,byte,offset,outerW,acc,base,m]++rest) (by norm_num) pc2556)
      (stepW_jump s 10530 10460 ((10460 : UInt256)) ([zero,byte,offset,outerW,acc,base,m]++rest) (by simp; omega) (by norm_num) rfl hdest)) hs.fork (by decide) (by rfl) (by rfl)
  simp only [soundW,Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost,Nat.reduceAdd]
  omega
end CycleSubmission.Global.WordEnds

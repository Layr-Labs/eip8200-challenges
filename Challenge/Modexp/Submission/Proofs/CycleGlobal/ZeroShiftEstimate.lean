import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftPrefix
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.Global.ZeroShiftMath

theorem run_zeroEstimate_left8 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 8)
    (hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0)
    (hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blkEstimateSuffix8.take 11)
      (zeroJoinState z s mem n bsize esize msize k) =
      some (estimateMid z s mem n bsize esize msize k) := by
  subst n
  simp (config := {maxSteps := 600000})
    [blkEstimateSuffix8, zeroJoinState, estimateMid, headPC, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, entrySlots, outer, Exp.outer,
      hcode, hrun, hkU, hxU, shr_zero, shl_256, add_ofNat_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
      List.exchange]

theorem run_zeroEstimate8 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 8)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0)
    (hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blkZero8 ++ blkEstimateSuffix8)
      (shiftLoopState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have hright : Challenge.EvmProof.Stepper.runLocatedBlock (blkEstimateSuffix8.drop 11)
      (estimateMid z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
    change Challenge.EvmProof.Stepper.runLocatedBlock (blk3026.drop 25) _ = _
    exact run_estimate_right z s mem n bsize esize msize k (by omega) (by omega) hact hcode hrun
  have htail := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (blkEstimateSuffix8.take 11) (blkEstimateSuffix8.drop 11)
    (zeroJoinState z s mem n bsize esize msize k)
    (estimateMid z s mem n bsize esize msize k)
    (macSetupState z s mem n bsize esize msize k)
    (run_zeroEstimate_left8 z s mem n bsize esize msize k hn hkU hxU hcode hrun) hrun hright
  rw [List.take_append_drop] at htail
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_zeroPrefix8 z s mem n bsize esize msize k hn hshift hbs hact hcode hrun) hrun htail

theorem run_zeroEstimate_left4 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 4)
    (hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0)
    (hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blkEstimateSuffix4.take 3)
      (zeroJoinState z s mem n bsize esize msize k) =
      some (estimate16 z s mem n bsize esize msize k) := by
  subst n
  simp (config := {maxSteps := 600000})
    [blkEstimateSuffix4, zeroJoinState, estimate16, headPC, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, entrySlots, outer, Exp.outer,
      hcode, hrun, hkU, hxU, shr_zero, shl_256, add_ofNat_zero,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
      List.exchange]

private theorem zero_estimate_h4_program :
    (blkEstimateSuffix4.drop 3).map Challenge.EvmProof.Stepper.Located.instruction =
      estimateRawPart2 ++ (estimateRawPart3 ++ (estimateRawPart4 ++ estimateRawPart5)) := by rfl
private theorem zero_estimate_h4_layout :
    WindowTwentyOneLocated.LinearPath (UInt256.ofNat 10724) (blkEstimateSuffix4.drop 3) := by
  dsimp only [blkEstimateSuffix4, List.drop, opAt, pushAt, wfOp,
    WindowTwentyOneLocated.LinearPath, WindowTwentyOneLocated.Linear]
  simp [YulEvmCompiler.Instr.size_push, YulEvmCompiler.Instr.size_op,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_zeroEstimate_right4 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 4)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blkEstimateSuffix4.drop 3)
      (estimate16 z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have hraw := WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
      (run_estimate_h4_part2 z s mem n bsize esize msize k hn hact hcode hrun)
      (WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
        (run_estimate_h4_part3 z s mem n bsize esize msize k hn hact hcode hrun)
        (WindowNibbleKernel.runInstructions_append_some _ _ _ _ _
          (run_estimate_h4_part4 z s mem n bsize esize msize k hn hact hcode hrun)
          (run_estimate_h4_part5 z s mem n bsize esize msize k hn hact hcode hrun)))
  refine WindowTwentyOneLocated.run_linear (blkEstimateSuffix4.drop 3) (UInt256.ofNat 10724)
    (estimate16 z s mem n bsize esize msize k) (macSetupState z s mem n bsize esize msize k)
    ?_ zero_estimate_h4_layout ?_ hrun ?_
  · change CycleSubmission.Artifact.bytecode.size < 2^256
    rw [CycleSubmission.Artifact.bytecodeSize]; decide
  · simp [estimate16, headPC, hn]
  · rw [zero_estimate_h4_program]
    exact hraw

theorem run_zeroEstimate4 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 4)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0)
    (hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blkZero4 ++ blkEstimateSuffix4)
      (shiftLoopState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have htail := Challenge.EvmProof.Stepper.runLocatedBlock_append
    (blkEstimateSuffix4.take 3) (blkEstimateSuffix4.drop 3)
    (zeroJoinState z s mem n bsize esize msize k)
    (estimate16 z s mem n bsize esize msize k)
    (macSetupState z s mem n bsize esize msize k)
    (run_zeroEstimate_left4 z s mem n bsize esize msize k hn hkU hxU hcode hrun) hrun
    (run_zeroEstimate_right4 z s mem n bsize esize msize k hn hact hcode hrun)
  rw [List.take_append_drop] at htail
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_zeroPrefix4 z s mem n bsize esize msize k hn hshift hbs hact hcode hrun) hrun htail

end CycleSubmission.Global.Fast.Shift

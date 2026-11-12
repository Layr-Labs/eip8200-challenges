import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftPrefix
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
private theorem rho_clamp8_program :
    blkEstimateSuffix8.map Challenge.EvmProof.Stepper.Located.instruction = estimateRawPart5 := by rfl
private theorem rho_clamp8_layout :
    WindowTwentyOneLocated.LinearPath (UInt256.ofNat 2756) blkEstimateSuffix8 := by
  dsimp only [blkEstimateSuffix8, opAt, pushAt, wfOp,
    WindowTwentyOneLocated.LinearPath, WindowTwentyOneLocated.Linear]
  simp [YulEvmCompiler.Instr.size_push, YulEvmCompiler.Instr.size_op,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
 theorem run_zeroEstimate8 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 8)
    (hpre : PreOK mem) (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0)
    (hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blkZero8 ++ blkEstimateSuffix8)
      (shiftLoopState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have hright : Challenge.EvmProof.Stepper.runLocatedBlock blkEstimateSuffix8
      (zeroJoinState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
    refine WindowTwentyOneLocated.run_linear blkEstimateSuffix8 (UInt256.ofNat 2756)
      (zeroJoinState z s mem n bsize esize msize k) (macSetupState z s mem n bsize esize msize k)
      ?_ rho_clamp8_layout ?_ hrun ?_
    · change CycleSubmission.Artifact.bytecode.size < 2^256
      rw [CycleSubmission.Artifact.bytecodeSize]; decide
    · simp [zeroJoinState, estimate40, headPC, hn]
    · rw [rho_clamp8_program]
      exact run_estimate_eight_part5 z s mem n bsize esize msize k (by omega) hact hcode hrun
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_zeroPrefix8 z s mem n bsize esize msize k hn hpre hd hshift hbs hact hcode hrun) hrun hright
#print axioms run_zeroEstimate8
private theorem rho_clamp4_program :
    blkEstimateSuffix4.map Challenge.EvmProof.Stepper.Located.instruction = estimateRawPart5 := by rfl
private theorem rho_clamp4_layout :
    WindowTwentyOneLocated.LinearPath (UInt256.ofNat 10779) blkEstimateSuffix4 := by
  dsimp only [blkEstimateSuffix4, opAt, pushAt, wfOp,
    WindowTwentyOneLocated.LinearPath, WindowTwentyOneLocated.Linear]
  simp [YulEvmCompiler.Instr.size_push, YulEvmCompiler.Instr.size_op,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
 theorem run_zeroEstimate4 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 4)
    (hpre : PreOK mem) (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0)
    (hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock (blkZero4 ++ blkEstimateSuffix4)
      (shiftLoopState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
  have hright : Challenge.EvmProof.Stepper.runLocatedBlock blkEstimateSuffix4
      (zeroJoinState z s mem n bsize esize msize k) =
      some (macSetupState z s mem n bsize esize msize k) := by
    refine WindowTwentyOneLocated.run_linear blkEstimateSuffix4 (UInt256.ofNat 10779)
      (zeroJoinState z s mem n bsize esize msize k) (macSetupState z s mem n bsize esize msize k)
      ?_ rho_clamp4_layout ?_ hrun ?_
    · change CycleSubmission.Artifact.bytecode.size < 2^256
      rw [CycleSubmission.Artifact.bytecodeSize]; decide
    · simp [zeroJoinState, estimate40, headPC, hn]
    · rw [rho_clamp4_program]
      exact run_estimate_h4_part5 z s mem n bsize esize msize k hn hact hcode hrun
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_zeroPrefix4 z s mem n bsize esize msize k hn hpre hd hshift hbs hact hcode hrun) hrun hright
#print axioms run_zeroEstimate4
end CycleSubmission.Global.Fast.Shift

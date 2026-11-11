import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimR5Head
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TailRoutes
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.TailFour
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.StackTail CycleSubmission.Global.StackPeak
open CycleSubmission CycleSubmission.Global SlimR5Head
open Monpro CiosCached StagedOperand
noncomputable def head4 (s : State) (mem : ByteArray) (bsize esize k mi : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 32)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 4 bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hmachine : ((MachineState.readWord mem 96).toNat * mi + 1) % 2^256 = 0) :
    GasSteps (append (SlimFrames.special s mem 4 bsize esize 128 k) rho)
      (append (entryState s mem bsize esize k) rho) := by
  have head := blockSteps_append CycleSubmission.CallerBlocks.fixedBlock
    (s := SlimFrames.special s mem 4 bsize esize 128 k)
    (env.transfer rfl rfl) rfl (call_run s mem bsize esize k hk hk16
      (by rw [env.code]; exact CycleSubmission.CallerBlocks.valid3181)) rho
    (by simp [SlimFrames.special, SlimFrames.outer, peakInstructions, CallerBlocks.fixedProgram,
      pops, pushes, Operation.popArity, Operation.pushArity]; omega)
  have hmiw : (MachineState.readWord mem 2720).toNat = mi := by
    rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  have hinvW : ((MachineState.readWord mem (32 * (2 + 2) - 32)).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0 := by
    rw [hmiw]; exact hmachine
  have hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1 := by
    rw [hf.minvW]
    intro h
    apply hmi1
    have h := congrArg UInt256.toNat h
    simpa only [Exp.toNat_ofNat_self hmi, Exp.toNat_ofNat_self (by decide : 1 < 2^256)] using h
  have g1 := CycleSubmission.Global.Fast.Cios2Dispatch.gasSteps_commonSetupSq s mem
    (UInt256.ofNat 3710) 2112 512 (2 + 2) (UInt256.ofNat (k - 1)) (UInt256.ofNat 0)
    (UInt256.ofNat (k-1) :: (SlimFrames.outer 4 bsize esize 128 ++ rho)) (by simp [SlimFrames.outer] <;> omega)
    env.running env.code env.forkEq env.noPrecompile hact (Or.inl rfl) (by omega)
    (by decide) (by omega) hcds hf.s32 hf.ml (by simp [SlimFrames.outer] <;> omega) (by simp [SlimFrames.outer] <;> omega)
    CycleSubmission.Global.Fast.SquareStagedEntry.jumpDest hguard
    (CiosInverseGuard.inverse_ne_zero _ _ hinvW)
  have g2 := CycleSubmission.Global.Fast.SquareStagedEntry.gasSteps_entry s
    (SquarePartialClear.memory (stageW mem 2112 (2 + 2))) (2 + 2)
    (UInt256.ofNat 3347) (UInt256.ofNat 0) (UInt256.ofNat 0)
    (UInt256.ofNat 0)
    (UInt256.ofNat 0 :: UInt256.ofNat 0 :: MachineState.readWord mem 2720 ::
      UInt256.ofNat 0 :: UInt256.ofNat 0 ::
      UInt256.ofNat (k - 1) :: UInt256.ofNat 0 :: UInt256.ofNat (k-1) :: (SlimFrames.outer 4 bsize esize 128 ++ rho))
    (by simp [SlimFrames.outer] <;> omega) env.running env.code env.forkEq env.noPrecompile hact
  have g3 := gasSteps_h1 s (SquarePartialClear.memory (stageW mem 2112 (2 + 2)))
    (CycleSubmission.Global.Fast.SquareStagedEntry.qWord (2 + 2)) (UInt256.ofNat 3347)
    (UInt256.ofNat 0) (MachineState.readWord mem 2720)
    (UInt256.ofNat 0) (UInt256.ofNat 0)
    (UInt256.ofNat 0) (UInt256.ofNat 0)
    (UInt256.ofNat 0) (UInt256.ofNat (k - 1)) (UInt256.ofNat 0)
    (UInt256.ofNat (k-1) :: (SlimFrames.outer 4 bsize esize 128 ++ rho)) (by simp [SlimFrames.outer] <;> omega)
    env.running env.code env.forkEq env.noPrecompile CycleSubmission.Global.Fast.SquareStagedEntry.qWord_four
  simpa only [append, entryState, entryMemory, frameAt, frameStack, List.append_assoc, List.cons_append] using ((head.trans g1).trans g2).trans g3

#print axioms head4
end CycleSubmission.Global.TailFour

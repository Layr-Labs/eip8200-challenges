import Challenge.Modexp.Submission.Proofs.CycleGlobal.SquareLoop
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FusedFinish
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Return
import Challenge.Modexp.Submission.Proofs.CycleCaller.Fixed
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.FourTerminal
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def result (N A B k : Nat) : Nat :=
  Model.montMul N (Limbs.radix^4) ((fun a => Model.montMul N (Limbs.radix^4) a a)^[k] A) B

theorem call_run (s : State) (mem : ByteArray) (bsize esize k : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3181 = true) :
    runInstructions CallerBlocks.fixedProgram (FixedDirectStates.special s mem 4 bsize esize 128 k) =
      some (CycleSubmission.Global.Fast.Cios2Dispatch.commonState s mem
        (UInt256.ofNat 3728) 2112 512 (UInt256.ofNat (k-1)) (UInt256.ofNat 2519)
        (UInt256.ofNat k :: Exp.outer 4 bsize esize 128)) := by
  have hdec : UInt256.ofNat k + UInt256.lnot ({ val := 0 } : UInt256) = UInt256.ofNat (k-1) := by
    interval_cases k <;> decide
  simp [CallerBlocks.fixedProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    FixedDirectStates.special, CycleSubmission.Global.Fast.Cios2Dispatch.commonState, Exp.outer, hdec, hjump,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]

noncomputable opaque run (s : State) (mem : ByteArray) (bsize esize k N A B mi : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 4 bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 4 N)
    (ha : Model.FastRepresents mem 2112 4 A)
    (hb : Model.FastRepresents mem 256 4 B)
    (hN : 0 < N) (hodd : N % 2 = 1) (hA : A < N) (hB : B < N) :
    CycleSubmission.Finish.Outcome (FixedDirectStates.special s mem 4 bsize esize 128 k)
      (Precompile.natToBytes (result N A B k) 128) := by
  have head := CallerBlocks.fixedBlock.steps
    (s := FixedDirectStates.special s mem 4 bsize esize 128 k)
    (env.transfer rfl rfl) rfl (call_run s mem bsize esize k hk hk16
      (by rw [env.code]; exact CallerBlocks.valid3181))
  have hlow : (MachineState.readWord mem 96).toNat = N % Limbs.radix := by
    have h := Model.readWord_of_fastRepresents hmod (j := 3) (by decide)
    simpa using h
  have hmiw : (MachineState.readWord mem 2720).toNat = mi := by
    rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  have hmachine : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0 := by
    rw [hlow, hmiw]; exact hinv
  have hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1 := by
    rw [hf.minvW]
    intro h
    apply hmi1
    have h := congrArg UInt256.toNat h
    simpa only [Exp.toNat_ofNat_self hmi, Exp.toNat_ofNat_self (by decide : 1 < 2^256)] using h
  have loop := CycleSubmission.Global.Fast.SquareLoop.gasSteps_squareLoop4 s mem 2 A N k
    (UInt256.ofNat 2519) (UInt256.ofNat k :: Exp.outer 4 bsize esize 128)
    (by simp [Exp.outer]) env.running env.code env.forkEq env.noPrecompile hact
    (by decide) rfl hk hk16 (by simp [Exp.outer]) (by simp [Exp.outer]) hcds
    hf.s32 hf.tl hf.ml ha hmod hA hN hodd hmachine hguard
  let out := FusedMemory.memory s 4 k mem
  have cleanup := CycleSubmission.Global.Fast.FusedFinish.gasSteps s out
    (UInt256.ofNat k) (Exp.outer 4 bsize esize 128) (by simp [Exp.outer])
    env.code env.forkEq env.running env.noPrecompile
  have finish := CycleSubmission.Global.Fast.Return.gasSteps_return s out 4 bsize esize 128
    (by decide) (by decide) (by decide) (by decide) rfl hact
    env.code env.forkEq env.running env.noPrecompile
  have rep : Model.FastRepresents out 256 4 (result N A B k) :=
    FusedMemory.represents s mem 2 A B N k (Or.inl rfl) (by decide) hk
      ha hb hmod hodd hA hB hmachine
  refine ⟨Exp.returnedState s out 4 bsize esize 128,
    ((head.trans loop).trans cleanup).trans finish, rfl, ?_, rfl⟩
  exact Exp.readPadded_eq_natToBytes rep (by decide)

end CycleSubmission.Global.FourTerminal

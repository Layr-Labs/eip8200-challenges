import Challenge.Modexp.Submission.Proofs.CycleCaller.Terminal
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.SlimCallerFixed
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.CallerBlocks CycleSubmission.CallerPrefix
theorem call_run (s : State) (mem : ByteArray) (bsize esize k : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3146 = true) :
    runInstructions fixedProgram (SlimFrames.special s mem 8 bsize esize 256 k) =
      some (call s mem k (MachineState.readWord mem 1312)
        (SlimFrames.outer mem 8 bsize esize 256).tail) := by
  have hdec : UInt256.ofNat k - UInt256.ofNat 1 = UInt256.ofNat (k-1) := by
    interval_cases k <;> decide
  simp [Exp.push0_word, fixedProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    SlimFrames.special, call, SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer, hdec, hjump,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]


theorem inverse_from_frame (mem : ByteArray) (bsize N mi : Nat)
    (hf : Exp.Frame mem 8 bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0) :
    (N * (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0 := by
  rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  simpa only [Limbs.radix, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using hinv


end CycleSubmission.Global.SlimCallerFixed

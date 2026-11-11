import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.SlimCallerFixed
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
theorem inverse_from_frame (mem : ByteArray) (bsize N mi : Nat)
    (hf : Exp.Frame mem 8 bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0) :
    (N * (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0 := by
  rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  simpa only [Limbs.radix, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using hinv


end CycleSubmission.Global.SlimCallerFixed

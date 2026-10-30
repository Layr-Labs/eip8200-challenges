import Challenge.Modexp.Submission.Proofs.CycleCaller.Terminal
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace CycleSubmission.CallerFixed
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.CallerBlocks CycleSubmission.CallerPrefix

theorem call_run (s : State) (mem : ByteArray) (bsize esize k : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3181 = true) :
    runInstructions fixedProgram (FixedDirectStates.special s mem 8 bsize esize 256 k) =
      some (call s mem k (UInt256.ofNat 2519)
        (UInt256.ofNat k :: Exp.outer 8 bsize esize 256)) := by
  have hdec : UInt256.ofNat k - UInt256.ofNat 1 = UInt256.ofNat (k-1) := by
    interval_cases k <;> decide
  simp [fixedProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    FixedDirectStates.special, call, Exp.outer, hdec, hjump,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem inverse_from_frame (mem : ByteArray) (bsize N mi : Nat)
    (hf : Exp.Frame mem 8 bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0) :
    (N * (MachineState.readWord mem 2720).toNat + 1) % 2^256 = 0 := by
  rw [hf.minvW, Exp.toNat_ofNat_self hmi]
  simpa only [Limbs.radix, Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using hinv

noncomputable opaque run (s : State) (mem : ByteArray) (bsize esize k N A B mi : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 8 bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 8 N)
    (ha : Model.FastRepresents mem 2112 8 A)
    (hb : Model.FastRepresents mem 256 8 B)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hg : (CallerPrefix.guardWord mem).toNat ≠ 0) :
    Finish.Outcome (FixedDirectStates.special s mem 8 bsize esize 256 k)
      (Precompile.natToBytes (CallerTerminal.result N A B k) 256) := by
  have head := fixedBlock.steps (s := FixedDirectStates.special s mem 8 bsize esize 256 k)
    (env.transfer rfl rfl) rfl (call_run s mem bsize esize k hk hk16
      (by rw [env.code]; exact valid3181))
  obtain ⟨done, tr, halt, bytes, calls⟩ := CallerTerminal.run s mem k (UInt256.ofNat 2519)
    (UInt256.ofNat k :: Exp.outer 8 bsize esize 256) N A B hk hk16 env
    (by simp [Exp.outer]) hact hcds hf.s32 hf.ml
    (by simp [Exp.outer]) (by simp [Exp.outer]) hmod ha hb
    (inverse_from_frame mem bsize N mi hf hmi hinv) hN hodd hB hg
  exact ⟨done, head.trans tr, halt, bytes, calls⟩

/-- When the operand guard fires, the width-8 call reaches the general route at 219. -/
noncomputable def bail (s : State) (mem : ByteArray) (bsize esize k mi : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 8 bsize mi)
    (hg : (CallerPrefix.guardWord mem).toNat = 0) :
    GasSteps (FixedDirectStates.special s mem 8 bsize esize 256 k)
      (stateAt s mem k (UInt256.ofNat 2519) (UInt256.ofNat k :: Exp.outer 8 bsize esize 256) 219) := by
  have head := fixedBlock.steps (s := FixedDirectStates.special s mem 8 bsize esize 256 k)
    (env.transfer rfl rfl) rfl (call_run s mem bsize esize k hk hk16
      (by rw [env.code]; exact valid3181))
  exact head.trans (CallerPrefix.bail s mem k (UInt256.ofNat 2519)
    (UInt256.ofNat k :: Exp.outer 8 bsize esize 256) env (by simp [Exp.outer]) hact hcds hf.s32 hf.ml
    (by simp [Exp.outer]) (by simp [Exp.outer]) hg)

end CycleSubmission.CallerFixed

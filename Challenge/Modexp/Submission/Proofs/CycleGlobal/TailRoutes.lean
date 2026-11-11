import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectR5Entry
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Terminal
import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimCallerFixed
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FixedRoute
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.TailRoutes
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission CycleSubmission.Global

noncomputable def fixed_head (s : State) (mem : ByteArray) (bsize esize k : Nat)
    
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s) :
    GasSteps (SlimFrames.special s mem 8 bsize esize 256 k)
      (CallerPrefix.call s mem k (UInt256.ofNat 256)
        ((SlimFrames.outer mem 8 bsize esize 256))) := by
  simpa [SlimFrames.special,CallerPrefix.call] using
    (DirectR5Entry.classify8 s mem (UInt256.ofNat (k-1)) (SlimFrames.outer mem 8 bsize esize 256)
      (by simp [SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,Exp.outer]) env)

noncomputable def terminal8 (s : State) (mem : ByteArray) (bsize esize k N A B mi : Nat)
    
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 8 bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 8 N)
    (ha : Model.FastRepresents mem 2112 8 A) (hb : Model.FastRepresents mem 256 8 B)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hg : (CallerPrefix.guardWord mem).toNat ≠ 0) :
    Finish.Outcome (SlimFrames.special s mem 8 bsize esize 256 k)
      (Precompile.natToBytes (CallerTerminal.result N A B k) 256) := by
  have head := fixed_head s mem bsize esize k hk hk16 env
  obtain ⟨done, tr, halt, bytes, calls⟩ := CallerTerminal.run s mem k (UInt256.ofNat 256)
    ((SlimFrames.outer mem 8 bsize esize 256)) N A B hk hk16 env
    (by simp [SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer]) hact hcds hf.s32 hf.ml rfl hmod ha hb
    (SlimCallerFixed.inverse_from_frame mem bsize N mi hf hmi hinv) hN hodd hB hg
  exact ⟨done, head.trans tr, halt, bytes, calls⟩

noncomputable def bail8 (s : State) (mem : ByteArray) (bsize esize k mi : Nat)
    
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 8 bsize mi)
    (hg : (CallerPrefix.guardWord mem).toNat = 0) :
    GasSteps (SlimFrames.special s mem 8 bsize esize 256 k)
      (CallerPrefix.stateAt s mem k (UInt256.ofNat 256)
        ((SlimFrames.outer mem 8 bsize esize 256)) 207) := by
  have head := fixed_head s mem bsize esize k hk hk16 env
  exact head.trans (CallerPrefix.bail s mem k (UInt256.ofNat 256)
    ((SlimFrames.outer mem 8 bsize esize 256)) env
    (by simp [SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, Exp.outer]) hact hcds hf.s32 hf.ml rfl hg)

#print axioms fixed_head
#print axioms terminal8
#print axioms bail8
end CycleSubmission.Global.TailRoutes

import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectR5Entry
import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectEightRaw
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.DirectEightEntry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
def guardBlock : Block CycleSubmission.Artifact.artifact .Osaka 3154 DirectEightRaw.guardProgram :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2445 7 3154 DirectEightRaw.guardProgram
  (by change 2445+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
def finishBlock : Block CycleSubmission.Artifact.artifact .Osaka 3197 DirectEightRaw.finishProgram :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2452 10 3197 DirectEightRaw.finishProgram
  (by change 2452+10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
theorem jumpDestBail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 135 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 135 = 207 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; decide
 simpa only [hp] using h
theorem jumpDestEight : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 5415 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 4177 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 4177 = 5415 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; decide
 simpa only [hp] using h

def bailState (s : State) (mem : ByteArray) (bsize esize k : Nat) : State :=
 DirectEightRaw.state s mem 207 (UInt256.ofNat (k-1)) (UInt256.ofNat 256) bsize esize
def hit (s : State) (mem : ByteArray) (bsize esize k : Nat)
 (hact : 88 ≤ s.activeWords.toNat) (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
 (hg : (DirectEightRaw.guardWord mem).toNat ≠ 0) :
 GasSteps (SlimFrames.special s mem 8 bsize esize 256 k)
 (DirectEightRaw.entered s mem (UInt256.ofNat (k-1)) (UInt256.ofNat 256) bsize esize) := by
 have gc := DirectR5Entry.classify8 s mem (UInt256.ofNat (k-1))
  (SlimFrames.outer mem 8 bsize esize 256)
  (by simp [SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer]) env
 have gg := guardBlock.steps
  (s := DirectEightRaw.state s mem 3154 (UInt256.ofNat (k-1)) (UInt256.ofNat 256) bsize esize)
  (env.transfer rfl rfl) rfl (DirectEightRaw.run_hit s mem _ _ bsize esize hact hg)
 have gf := finishBlock.steps
  (s := DirectEightRaw.state s mem 3197 (UInt256.ofNat (k-1)) (UInt256.ofNat 256) bsize esize)
  (env.transfer rfl rfl) rfl (DirectEightRaw.run_finish s mem _ _ bsize esize hact (by rw [env.code]; exact jumpDestEight))
 exact (gc.trans gg).trans gf

def miss (s : State) (mem : ByteArray) (bsize esize k : Nat)
 (hact : 88 ≤ s.activeWords.toNat) (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
 (hg : (DirectEightRaw.guardWord mem).toNat = 0) :
 GasSteps (SlimFrames.special s mem 8 bsize esize 256 k) (bailState s mem bsize esize k) := by
 have gc := DirectR5Entry.classify8 s mem (UInt256.ofNat (k-1))
  (SlimFrames.outer mem 8 bsize esize 256)
  (by simp [SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,Exp.outer]) env
 have gg := guardBlock.steps
  (s := DirectEightRaw.state s mem 3154 (UInt256.ofNat (k-1)) (UInt256.ofNat 256) bsize esize)
  (env.transfer rfl rfl) rfl (DirectEightRaw.run_miss s mem _ _ bsize esize hact hg (by rw [env.code]; exact jumpDestBail))
 exact gc.trans gg
#print axioms hit
#print axioms miss
end CycleSubmission.Global.DirectEightEntry

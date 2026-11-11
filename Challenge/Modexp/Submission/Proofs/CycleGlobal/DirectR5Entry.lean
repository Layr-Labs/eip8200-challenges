import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectR5Classifier
import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectR5Reuse
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.DirectR5Entry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
def classifyBlock : Block CycleSubmission.Artifact.artifact .Osaka 3199 DirectR5Classifier.program :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2454 6 3199 DirectR5Classifier.program
  (by change 2454+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
def dropBlock : Block CycleSubmission.Artifact.artifact .Osaka 3208 DirectR5Classifier.dropWidth :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2460 2 3208 DirectR5Classifier.dropWidth
  (by change 2460+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
def headerBlock : Block CycleSubmission.Artifact.artifact .Osaka 3210 DirectR5Reuse.program :=
 WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2462 7 3210 DirectR5Reuse.program
  (by change 2462+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
  (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)
theorem jumpDestCommon : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3146 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 2415 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 2415 = 3146 := by
  rw [CycleSubmission.PCCertificate.selectedPC 2415 (by decide)]; decide
 simpa only [hp] using h
theorem jumpDestR5 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 5197 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 4078 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 4078 = 5197 := by
  rw [CycleSubmission.PCCertificate.selectedPC 4078 (by decide)]; decide
 simpa only [hp] using h
def classify8 (s : State) (mem : ByteArray) (count : UInt256) (rest : List UInt256)
 (hcap : rest.length ≤ 1000) (env : Environment CycleSubmission.Artifact.artifact .Osaka s) :
 GasSteps {s with pc := UInt256.ofNat 3199, memory := mem, stack := [count,UInt256.ofNat 256]++rest}
 {s with pc := UInt256.ofNat 3146, memory := mem, stack := [count,UInt256.ofNat 256]++rest} :=
 classifyBlock.steps (s := {s with pc := UInt256.ofNat 3199, memory := mem, stack := [count,UInt256.ofNat 256]++rest})
  (env.transfer rfl rfl) rfl (DirectR5Classifier.run8 {s with memory := mem} count rest hcap (by rw [env.code]; exact jumpDestCommon))
def enter4 (s : State) (mem : ByteArray) (count : UInt256) (bsize esize msize : Nat)
 (hact : 88 ≤ s.activeWords.toNat) (env : Environment CycleSubmission.Artifact.artifact .Osaka s) :
 GasSteps {s with pc := UInt256.ofNat 3199, memory := mem, stack := [count,UInt256.ofNat 128]++SlimFrames.outer mem 4 bsize esize msize}
 (DirectR5Reuse.result s mem count bsize esize msize) := by
 have hc : (SlimFrames.outer mem 4 bsize esize msize).length ≤ 1000 := by
  simp [SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,Exp.outer]
 have g1 := classifyBlock.steps
  (s := {s with pc := UInt256.ofNat 3199, memory := mem, stack := [count,UInt256.ofNat 128]++SlimFrames.outer mem 4 bsize esize msize})
  (env.transfer rfl rfl) rfl (DirectR5Classifier.run4 {s with memory := mem} count _ hc)
 have g2 := dropBlock.steps
  (s := {s with pc := UInt256.ofNat 3208, memory := mem, stack := [count,UInt256.ofNat 128]++SlimFrames.outer mem 4 bsize esize msize})
  (env.transfer rfl rfl) rfl (DirectR5Classifier.runDrop {s with memory := mem} count _ hc)
 have g3 := headerBlock.steps
  (s := {s with pc := UInt256.ofNat 3210, memory := mem, stack := count::SlimFrames.outer mem 4 bsize esize msize})
  (env.transfer rfl rfl) rfl (DirectR5Reuse.run s mem count bsize esize msize hact (by rw [env.code]; exact jumpDestR5))
 exact (g1.trans g2).trans g3
#print axioms classify8
#print axioms enter4
end CycleSubmission.Global.DirectR5Entry

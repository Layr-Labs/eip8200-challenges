import Challenge.Modexp.Submission.Proofs.Cycle.PersistentCounter
import Challenge.Modexp.Submission.Proofs.Cycle.PersistentSquareLoop
import Challenge.Modexp.Submission.Proofs.Cycle.PersistentMemory
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace CycleSubmission.PersistentBinding
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding WindowTwentyOneSlice WindowNibbleKernel

theorem install_pc : Artifact.artifact.instructionPC 4223 = 5387 := by
 rw [PCCertificate.selectedPC 4223 (by decide)]; rfl
def installBlock : Block Artifact.artifact .Osaka 5387 CachedInverse.installPrefix :=
 WindowTwentyOneSlice.block Artifact.wellFormed 4223 7 5387 CachedInverse.installPrefix
  (by change 4223+7 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
  install_pc (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl) (by decide)

theorem round_pc : Artifact.artifact.instructionPC 4230 = 5395 := by
 rw [PCCertificate.selectedPC 4230 (by decide)]; rfl
def roundBlock : Block Artifact.artifact .Osaka 5395 PersistentCounter.roundProgram :=
 WindowTwentyOneSlice.block Artifact.wellFormed 4230 1572 5395 PersistentCounter.roundProgram
  (by change 4230+1572 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
  round_pc (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl) (by decide)

theorem restore_pc : Artifact.artifact.instructionPC 5802 = 7513 := by
 rw [PCCertificate.selectedPC 5802 (by decide)]; rfl
def restoreBlock : Block Artifact.artifact .Osaka 7513 CachedInverse.restoreMaskProgram :=
 WindowTwentyOneSlice.block Artifact.wellFormed 5802 8 7513 CachedInverse.restoreMaskProgram
  (by change 5802+8 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
  restore_pc (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl) (by decide)

theorem valid_kernel : Decode.isValidJumpDest Artifact.bytecode 5395 = true := by
 have h := Global.Binding.jumpDest 4230 (by rfl)
 rw [round_pc] at h
 exact h

noncomputable def round_steps (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
 (hcap : rest.length ≤ 958) (hact : 88 ≤ s.activeWords.toNat)
 (hmem : LimbMemory.Holds s.memory inv a b n) (ha : ∀ i < 8, (a i).toNat < 2^240) :
 GasSteps (CachedInverse.persistentInitial s inv count a b n rest)
 {s with pc := UInt256.ofNat (if count.toNat = 0 then 7513 else 5395),memory := R9InvConsumeComplete.historyMemory s.memory inv a b n,stack := PersistentCounter.frame inv (count-UInt256.ofNat 1) (WordHistory.squared inv a b n) b n (inv::rest)} := by
 have hj : Decode.isValidJumpDest s.executionEnv.code 5395 = true := by rw [env.code]; exact valid_kernel
 exact roundBlock.steps (env.transfer rfl rfl) rfl
  (PersistentCounter.run_round s inv count a b n rest hcap hact hmem ha hj)

def installed (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : State :=
 {s with pc := UInt256.ofNat 5395,stack := PersistentSquareLoop.frame inv a n (CachedInverse.publicCounter s::rest)}

noncomputable def install_steps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (env : Environment Artifact.artifact .Osaka s) (hm : SquareMeaning.Memory0 s.memory inv a SquareStep.zeroWords n)
 (hcache : rest[0]? = some inv) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
 GasSteps {s with pc := UInt256.ofNat 5387,stack := SquareMeaning.frame0 inv a SquareStep.zeroWords n (CachedInverse.publicCounter s::rest)}
  (installed s inv a n rest) := by
 cases rest with
 | nil => simp at hcache
 | cons value rest =>
  have hv : value = inv := by simpa using hcache
  subst value
  exact installBlock.steps (env.transfer rfl rfl) rfl
   (CachedInverse.run_installPrefix s inv (CachedInverse.publicCounter s) a SquareStep.zeroWords n rest
    (by simp at hcap; omega) hact hm.at96)

noncomputable def restore_steps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat)
 (hcache : rest[0]? = some inv) (hinv : MachineState.readWord s.memory 2720 = inv) :
 GasSteps {s with pc := UInt256.ofNat 7513,stack := PersistentSquareLoop.frame inv a n (PersistentSquareLoop.counter s::rest)}
 {s with pc := UInt256.ofNat 7526,memory := LimbMemory.store s.memory 96 (a 5),stack := SquareMeaning.frame0 inv a SquareStep.zeroWords n (PersistentSquareLoop.counter s::rest)} := by
 cases rest with
 | nil => simp at hcache
 | cons value rest =>
  have hv : value = inv := by simpa using hcache
  subst value
  exact restoreBlock.steps (env.transfer rfl rfl) rfl
   (CachedInverse.run_restoreMask s inv (PersistentSquareLoop.counter s) a SquareStep.zeroWords n rest
    (by simp at hcap; omega) hact hinv)

#print axioms round_steps
#print axioms install_steps
#print axioms restore_steps
end CycleSubmission.PersistentBinding

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

theorem install_pc : Artifact.artifact.instructionPC 4227 = 5391 := by
 rw [PCCertificate.selectedPC 4227 (by decide)]
 rfl

def installBlock : Block Artifact.artifact .Osaka 5391 CachedInverse.installPrefix :=
 WindowTwentyOneSlice.block Artifact.wellFormed 4227 3 5391 CachedInverse.installPrefix
  (by change 4227+3 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
  install_pc
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)

theorem round_pc : Artifact.artifact.instructionPC 4230 = 5394 := by
 rw [PCCertificate.selectedPC 4230 (by decide)]
 rfl

def roundBlock : Block Artifact.artifact .Osaka 5394 PersistentCounter.roundProgram :=
 WindowTwentyOneSlice.block Artifact.wellFormed 4230 1576 5394 PersistentCounter.roundProgram
  (by change 4230+1576 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
  round_pc
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)

theorem restore_pc : Artifact.artifact.instructionPC 5806 = 7723 := by
 rw [PCCertificate.selectedPC 5806 (by decide)]
 rfl

def restoreBlock : Block Artifact.artifact .Osaka 7723 CachedInverse.restoreMaskProgram :=
 WindowTwentyOneSlice.block Artifact.wellFormed 5806 6 7723 CachedInverse.restoreMaskProgram
  (by change 5806+6 ≤ Artifact.instructions.length; rw [Artifact.instructionCount]; decide)
  restore_pc
  (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
  (by decide)

theorem valid_kernel : Decode.isValidJumpDest Artifact.bytecode 5394 = true := by
 have h := Global.Binding.jumpDest 4230 (by rfl)
 rw [round_pc] at h
 exact h

noncomputable def round_steps (s : State) (inv count : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
 (hcap : rest.length ≤ 958) (hact : 88 ≤ s.activeWords.toNat)
 (hmem : SquareMeaning.Memory0 s.memory inv a b n)
 (ha : ∀ i < 8, (a i).toNat < 2^240) :
 GasSteps (CachedInverse.persistentInitial s inv count a b n rest)
 {s with pc := UInt256.ofNat (if count.toNat = 0 then 7723 else 5394), memory := R9InvConsumeComplete.historyMemory s.memory inv a b n, stack := PersistentCounter.frame inv (count-UInt256.ofNat 1) (WordHistory.squared inv a b n) b n (inv :: rest)} := by
 have hj : Decode.isValidJumpDest s.executionEnv.code 5394 = true := by
  rw [env.code]
  exact valid_kernel
 exact roundBlock.steps (env.transfer rfl rfl) rfl
  (PersistentCounter.run_round s inv count a b n rest hcap hact hmem ha hj)

#print axioms round_steps

def installed (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : State :=
 {s with pc := UInt256.ofNat 5394, stack := PersistentSquareLoop.frame inv a n (PersistentSquareLoop.counter s :: rest)}

noncomputable def install_steps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (env : Environment Artifact.artifact .Osaka s)
 (hcache : rest[0]? = some inv) (hcap : rest.length ≤ 959) :
 GasSteps {s with pc := UInt256.ofNat 5391, stack := SquareMeaning.frame0 inv a SquareStep.zeroWords n (PersistentSquareLoop.counter s :: rest)}
  (installed s inv a n rest) := by
 cases rest with
 | nil => simp at hcache
 | cons value rest =>
  have hv : value = inv := by simpa using hcache
  subst value
  exact installBlock.steps (env.transfer rfl rfl) rfl
   (CachedInverse.run_installPrefix s inv (PersistentSquareLoop.counter s) a SquareStep.zeroWords n rest (by simp at hcap; omega))

theorem restore_raw (s : State) (inv : UInt256) (a b n : Nat → UInt256)
 (rest : List UInt256) (hcap : rest.length ≤ 960) :
 runInstructions CachedInverse.restoreMaskProgram
  {s with pc := UInt256.ofNat 7723, stack := (SquareMeaning.frame0 inv a b n rest).set 10 inv} =
 some {s with pc := UInt256.ofNat 7732, stack := SquareMeaning.frame0 inv a b n rest} := by
 have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 20) : rest.length+j < 1024 := by omega
 simp [hz,CachedInverse.restoreMask_value,CachedInverse.restoreMaskProgram,SquareMeaning.frame0,List.set,runInstructions,Stepper.runInstr,
   List.exchange,Word.literal_eq_ofNat,Word.word_toNat_ofNat,Word.succ_ofNat_mod,
   Word.ofNat_add_mod,capacity,Nat.add_assoc]

noncomputable def restore_steps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
 (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length ≤ 959) :
 GasSteps {s with pc := UInt256.ofNat 7723, stack := PersistentSquareLoop.frame inv a n (PersistentSquareLoop.counter s :: rest)}
  {s with pc := UInt256.ofNat 7732, stack := SquareMeaning.frame0 inv a SquareStep.zeroWords n (PersistentSquareLoop.counter s :: rest)} := by
 exact restoreBlock.steps (env.transfer rfl rfl) rfl
  (restore_raw s inv a SquareStep.zeroWords n (PersistentSquareLoop.counter s :: rest) (by simp; omega))

#print axioms install_steps
#print axioms restore_steps

end CycleSubmission.PersistentBinding

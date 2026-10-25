import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeContract
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.NormalizeBinding
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding WindowTwentyOneSlice
open HistoricalSearch.GeneratedColumns HistoricalSearch.CRTControl
open CycleSubmission.NormalizeMeaning

def normalizerBlock : Block Artifact.artifact .Osaka 11014 normalizeProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 9062 121 11014 normalizeProgram
    (by change 9062+121 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 9062+121 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def returnBlock : Block Artifact.artifact .Osaka 11155 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 9183 1 11155 jumpProgram
    (by change 9183+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 9183+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

theorem validJump8085 : Decode.isValidJumpDest Artifact.bytecode 8085 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 6691
    (show Artifact.instructions[6691]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 6691 = 8085 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h

theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10867 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8967
    (show Artifact.instructions[8967]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8967 = 10867 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h


def returned (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256) : State :=
  {result s a n ret slot1 rest with pc := ret, stack := frame (output a n) n (n 0) slot1 rest}

noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat)
    (hret : Decode.isValidJumpDest Artifact.bytecode ret.toNat = true) :
    GasSteps {s with pc := UInt256.ofNat 11014, stack := frame a n ret slot1 rest}
      (returned s a n ret slot1 rest) := by
  have body := normalizerBlock.steps
    (s := {s with pc := UInt256.ofNat 11014, stack := frame a n ret slot1 rest})
    (env.transfer rfl rfl) rfl (run s a n ret slot1 rest h hcap hact)
  have e : Environment Artifact.artifact .Osaka (result s a n ret slot1 rest) := env.transfer rfl rfl
  have valid : Decode.isValidJumpDest (result s a n ret slot1 rest).executionEnv.code ret.toNat = true := by
    rw [e.code]; exact hret
  have cap : (result s a n ret slot1 rest).stack.length < 1024 := by
    simp only [result, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have jump := returnBlock.steps e rfl
    (jump_run (result s a n ret slot1 rest) ret (frame (output a n) n (n 0) slot1 rest) rfl cap valid)
  exact body.trans jump

noncomputable def correct (s : State) (a n : Nat → UInt256) (ret slot1 : UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat)
    (hret : Decode.isValidJumpDest Artifact.bytecode ret.toNat = true)
    (ha : ∀ i < 8, (a i).toNat < 2^240)
    (hn : ∀ i < 9, (n i).toNat < 2^240)
    (horder : HistoricalSearch.MixedMontgomery.weighted (2^240) 9 (fun i => (n i).toNat) ≤
      HistoricalSearch.MixedMontgomery.weighted (2^240) 9 (fun i => (a i).toNat)) :
    PSigma (fun _ : GasSteps {s with pc := UInt256.ofNat 11014, stack := frame a n ret slot1 rest}
      (returned s a n ret slot1 rest) =>
    (HistoricalSearch.MixedMontgomery.weighted (2^240) 9 (fun i => (output a n i).toNat) +
       HistoricalSearch.MixedMontgomery.weighted (2^240) 9 (fun i => (n i).toNat) =
       HistoricalSearch.MixedMontgomery.weighted (2^240) 9 (fun i => (a i).toNat))) :=
  ⟨gasSteps s a n ret slot1 rest env h hcap hact hret, output_value a n ha hn horder⟩

end CycleSubmission.NormalizeBinding

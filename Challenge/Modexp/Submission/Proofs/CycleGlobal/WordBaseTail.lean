import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Word
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
namespace CycleSubmission.Global.Word
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics
open EvmSemantics.EVM
attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod
set_option linter.unusedSimpArgs false in
theorem run_baseTail (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTailPath
      (baseReturnedState input i base) =
        some (baseLoopState input (i + 1) (baseStep input i base)) := by
  rcases hvalid with ⟨_,hb,he,hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have h172 : (166 : UInt256).toNat = 166 := by decide
  have h172Word : (166 : UInt256) = UInt256.ofNat 166 := by decide
  have h256Word : (256 : UInt256) = UInt256.ofNat 256 := by decide
  have h157 : (152 : UInt256).toNat = 152 := by decide
  have h157Word : (152 : UInt256) = UInt256.ofNat 152 := by decide
  have hisucc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) (by omega : i + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]; exact hisucc
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 300000 })
    [baseTailPath,opAt,pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      baseReturnedState,Accessors.calldataByteReturned,
      baseRest,baseLoopState,baseStep,byteWord,Accessors.calldataByteValue,
      nonzeroState,callerRest,Dispatch.wordEntryState,Main.headerState,
      initialState,wordPCs,List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt,
      hi256,h172,h172Word,h256Word,h157,h157Word,honeWord,
      jump541,hisucc,hincLeft]
#print axioms run_baseTail
/-- One base-byte iteration: guard, inlined byte read, tail. -/
def gasSteps_baseIteration (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.GasSteps (baseLoopState input i base)
      (baseLoopState input (i + 1) (baseStep input i base)) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      CycleSubmission.Artifact.artifact .Osaka baseGuardPath rfl rfl
        (run_baseGuard input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      CycleSubmission.Artifact.artifact .Osaka baseCallPath rfl rfl
        (run_baseCall input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      CycleSubmission.Artifact.artifact .Osaka baseTailPath rfl rfl
        (run_baseTail input i base hvalid hi) rfl deployAddress_not_precompile
def gasSteps_baseLoop (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (baseLoopState input 0 0)
      (baseLoopState input (baseSize input) (baseAfter input (baseSize input))) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (baseSize input)
    (fun i hi => gasSteps_baseIteration input i (baseAfter input i) hvalid hi)
end CycleSubmission.Global.Word

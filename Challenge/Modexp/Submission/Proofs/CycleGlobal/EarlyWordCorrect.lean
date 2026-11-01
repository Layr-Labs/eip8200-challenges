import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ArtifactEarlyWordPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MainGas
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FermatGas
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.PrimeCertificates
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUMain
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUBlocks

noncomputable section
set_option warningAsError true

/-!
# Total initial dispatch through the early one-word wrapper

The initial header reader starts directly at byte zero. Matching headers fall
through to the Fermat/window proof at pc 25. Every other header restores the
legacy entry at pc 1251 with an empty stack and unchanged memory and environment.
-/

namespace CycleSubmission.Global.EarlyWordCorrect
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics EvmSemantics.EVM
open WindowTwentyOneBinding WindowTwentyOnePositive

abbrev Handled (input : ByteArray) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps
      (initialState CycleSubmission.Artifact.bytecode input 0) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input)

private def environment (input : ByteArray) :
    Environment CycleSubmission.Artifact.artifact .Osaka
      (initialState CycleSubmission.Artifact.bytecode input 0) where
  sizeBound := by
    change CycleSubmission.Artifact.bytecode.size < 2 ^ 256
    rw [CycleSubmission.Artifact.bytecodeSize]
    norm_num
  code := rfl
  forkEq := rfl
  running := rfl
  noPrecompile := deployAddress_not_precompile

/-- Every valid header whose exponent or modulus size is not 32 reaches the unchanged
legacy entry exactly. -/
def legacy (input : ByteArray) (hvalid : ValidInput input)
    (hmiss : ¬ (exponentSize input = 32 ∧ modulusSize input = 32)) :
    Challenge.EvmProof.GasSteps (initialState CycleSubmission.Artifact.bytecode input 0)
      (Main.trampolineState input 578) := by
  have tail := EarlyWordGas.steps_size_miss CycleSubmission.Global.Paths.earlyWordPaths
    (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) input rfl
    hvalid.2.2.1 hvalid.2.2.2 hmiss
  change Challenge.EvmProof.GasSteps (Main.trampolineState input 0)
    (Main.trampolineState input 578) at tail
  exact (Main.gasSteps_entryHop input).trans tail

/-- The three words the loads at 16 read for any header; garbage unless the base size is 32. -/
def loaded (input : ByteArray) : List UInt256 :=
  [MachineState.readWord input 160, MachineState.readWord input 128, MachineState.readWord input 96]

/-- Every matching header has a complete initial-state correctness trace: a 32-byte
base through the merged test at 25, a shorter base through the general-width entry. -/
def hit (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    Handled input := by
  have hsize : exponentSize input = 32 ∧ modulusSize input = 32 := ⟨hmatch.2.1, hmatch.2.2⟩
  have s1 := EarlyWordGas.steps_size_hit CycleSubmission.Global.Paths.earlyWordPaths
    (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) input rfl hsize
  by_cases hb : baseSize input = 32
  · have s2 := FermatGas.fastSteps CycleSubmission.Global.Paths.fermatPaths
      (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) input hb
    obtain ⟨final, ⟨tail⟩, done, result⟩ := FermatGas.wideHandled
      CycleSubmission.Global.Paths.fermatPaths CycleSubmission.Global.Paths.twentyOnePaths
      (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) rfl input hmatch hb
      (by exact PrimeCertificates.bn254P_prime) (by exact PrimeCertificates.secpP_prime)
    exact ⟨final, ⟨(Main.gasSteps_entryHop input).trans ((s1.trans s2).trans tail)⟩,
      done, result⟩
  · have s2 := FermatGas.missSteps CycleSubmission.Global.Paths.fermatPaths
      (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) input hb
    have s3 := FermatGas.genSteps CycleSubmission.Global.Paths.fermatPaths
      (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) input hmatch.1
      (loaded input) (by simp [loaded])
    obtain ⟨final, ⟨tail⟩, done, result⟩ := FermatGas.handled
      CycleSubmission.Global.Paths.fermatPaths CycleSubmission.Global.Paths.twentyOnePaths
      (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) rfl input
      (UInt256.ofNat (32 - baseSize input) :: loaded input) (by simp [loaded]) hmatch
      (by exact PrimeCertificates.bn254P_prime) (by exact PrimeCertificates.secpP_prime)
    exact ⟨final, ⟨(Main.gasSteps_entryHop input).trans ((s1.trans (s2.trans s3)).trans tail)⟩,
      done, result⟩

/-- Where a base size above 32 (exponent and modulus sizes 32) leaves the general-width
entry: the wide fallback at 219 with the base size, 32 and the three loaded words on the stack. -/
def genBigState (input : ByteArray) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with
    pc := UInt256.ofNat 219
    stack := [UInt256.ofNat (baseSize input), UInt256.ofNat 32] ++ loaded input }

def genBig (input : ByteArray) (hsize : exponentSize input = 32 ∧ modulusSize input = 32)
    (hb : 32 < baseSize input) :
    Challenge.EvmProof.GasSteps (initialState CycleSubmission.Artifact.bytecode input 0) (genBigState input) := by
  have s1 := EarlyWordGas.steps_size_hit CycleSubmission.Global.Paths.earlyWordPaths
    (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) input rfl hsize
  have s2 := FermatGas.missSteps CycleSubmission.Global.Paths.fermatPaths
    (initialState CycleSubmission.Artifact.bytecode input 0) (environment input) input (by omega)
  have hjump : Decode.isValidJumpDest
      (initialState CycleSubmission.Artifact.bytecode input 0).executionEnv.code 219 = true :=
    CycleSubmission.Global.Paths.fermatPaths.bigJump
  have hc := FermatNext.run_gen_check (initialState CycleSubmission.Artifact.bytecode input 0)
    (loaded input) (by simp [loaded]) hjump
  have hword : MachineState.readWord
      (initialState CycleSubmission.Artifact.bytecode input 0).executionEnv.calldata 0 =
      UInt256.ofNat (baseSize input) := rfl
  have hbig : baseSize input < 2 ^ 256 := EarlyWordProgram.header_lt input 0
  have hgt : ¬ (UInt256.gt (UInt256.ofNat (baseSize input)) (UInt256.ofNat 32)).toNat = 0 := by
    unfold UInt256.gt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbig, Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
    simp [hb]
  rw [hword, if_neg hgt] at hc
  have s3 := CycleSubmission.Global.Paths.fermatPaths.genCheck.steps
    ((environment input).transfer (t := WindowTwentyOneEntry.framed
      (initialState CycleSubmission.Artifact.bytecode input 0) (UInt256.ofNat 101) (loaded input)) rfl rfl) rfl hc
  change Challenge.EvmProof.GasSteps (Main.trampolineState input 0) _ at s1
  exact (Main.gasSteps_entryHop input).trans ((s1.trans s2).trans s3)

/-- A base size above 32 with exponent and modulus sizes 32 is handled by the
certified wide fallback from 238. -/
def big (input : ByteArray) (hvalid : ValidInput input)
    (hsize : exponentSize input = 32 ∧ modulusSize input = 32) (hb : 32 < baseSize input) :
    Handled input := by
  have steps := genBig input hsize hb
  have env : WindowTwentyOneBinding.Environment CycleSubmission.Artifact.artifact .Osaka
      (genBigState input) :=
    { sizeBound := by
        change CycleSubmission.Artifact.bytecode.size < 2 ^ 256
        rw [CycleSubmission.Artifact.bytecodeSize]
        norm_num
      code := rfl
      forkEq := rfl
      running := rfl
      noPrecompile := deployAddress_not_precompile }
  obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
    BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
      BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks _ env rfl
      (by simp [genBigState, loaded])
      (by simp [genBigState, initialState]; decide)
      rfl hvalid (by show 0 < modulusSize input; omega)
  exact ⟨final, ⟨steps.trans tail⟩, hdone, hres⟩

end CycleSubmission.Global.EarlyWordCorrect


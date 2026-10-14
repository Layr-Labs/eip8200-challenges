import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactEarlyWordPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas
import Challenge.Modexp.Submission.Proofs.Bytecode.MainGas
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactWindowPaths
import Challenge.Modexp.Submission.Proofs.PrimeCertificates
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMain
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUBlocks

set_option warningAsError true

/-!
# Total initial dispatch through the early one-word wrapper

The initial header reader starts directly at byte zero. Matching headers fall
through to the Fermat/window proof at pc 25. Every other header restores the
legacy entry at pc 1251 with an empty stack and unchanged memory and environment.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordCorrect

open EvmSemantics EvmSemantics.EVM
open WindowTwentyOneBinding WindowTwentyOnePositive

abbrev Handled (input : ByteArray) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps
      (initialState submissionBytecode input 0) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input)

private def environment (input : ByteArray) :
    Environment Artifact.submissionArtifact .Osaka
      (initialState submissionBytecode input 0) where
  sizeBound := by
    change submissionBytecode.size < 2 ^ 256
    rw [submissionBytecode_size]
    norm_num
  code := rfl
  forkEq := rfl
  running := rfl
  noPrecompile := deployAddress_not_precompile

/-- Every header whose exponent or modulus size is not 32 reaches the unchanged
legacy entry exactly. -/
def legacy (input : ByteArray)
    (hmiss : ¬ (exponentSize input = 32 ∧ modulusSize input = 32)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 578) := by
  have tail := EarlyWordGas.steps_size_miss Artifact.earlyWordPaths
    (initialState submissionBytecode input 0) (environment input) input rfl hmiss
  change Challenge.EvmProof.GasSteps (Main.trampolineState input 0)
    (Main.trampolineState input 578) at tail
  exact (Main.gasSteps_entryHop input).trans tail

/-- Every matching header has a complete initial-state correctness trace: a 32-byte
base through the fast entry at 24, a shorter base through the general-width entry. -/
def hit (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    Handled input := by
  have hsize : exponentSize input = 32 ∧ modulusSize input = 32 := ⟨hmatch.2.1, hmatch.2.2⟩
  have s1 := EarlyWordGas.steps_size_hit Artifact.earlyWordPaths
    (initialState submissionBytecode input 0) (environment input) input rfl hsize
  by_cases hb : baseSize input = 32
  · have s2 := EarlyWordGas.steps_width_hit Artifact.earlyWordPaths
      (initialState submissionBytecode input 0) (environment input) input rfl hb
    have s3 := FermatGas.fastSteps Artifact.fermatPaths
      (initialState submissionBytecode input 0) (environment input) input hb
    obtain ⟨final, ⟨tail⟩, done, result⟩ := FermatGas.handled
      Artifact.fermatPaths Artifact.twentyOnePaths
      (initialState submissionBytecode input 0) (environment input) rfl input [] (by simp) hmatch
      (by exact PrimeCertificates.bn254P_prime) (by exact PrimeCertificates.secpP_prime)
    exact ⟨final, ⟨(Main.gasSteps_entryHop input).trans ((s1.trans s2).trans (s3.trans tail))⟩,
      done, result⟩
  · have s2 := EarlyWordGas.steps_width_miss Artifact.earlyWordPaths
      (initialState submissionBytecode input 0) (environment input) input rfl hb
    have s3 := FermatGas.genSteps Artifact.fermatPaths
      (initialState submissionBytecode input 0) (environment input) input hmatch.1 [] (by simp)
    obtain ⟨final, ⟨tail⟩, done, result⟩ := FermatGas.handled
      Artifact.fermatPaths Artifact.twentyOnePaths
      (initialState submissionBytecode input 0) (environment input) rfl input
      [UInt256.ofNat (32 - baseSize input)] (by simp) hmatch
      (by exact PrimeCertificates.bn254P_prime) (by exact PrimeCertificates.secpP_prime)
    exact ⟨final, ⟨(Main.gasSteps_entryHop input).trans ((s1.trans s2).trans (s3.trans tail))⟩,
      done, result⟩

/-- Where a base size above 32 (exponent and modulus sizes 32) leaves the general-width
entry: the wide fallback at 238 with the base size and 32 on the stack. -/
def genBigState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 218
    stack := [UInt256.ofNat (baseSize input), UInt256.ofNat 32] }

def genBig (input : ByteArray) (hsize : exponentSize input = 32 ∧ modulusSize input = 32)
    (hb : 32 < baseSize input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0) (genBigState input) := by
  have s1 := EarlyWordGas.steps_size_hit Artifact.earlyWordPaths
    (initialState submissionBytecode input 0) (environment input) input rfl hsize
  have s2 := EarlyWordGas.steps_width_miss Artifact.earlyWordPaths
    (initialState submissionBytecode input 0) (environment input) input rfl (by omega)
  have hjump : Decode.isValidJumpDest
      (initialState submissionBytecode input 0).executionEnv.code 218 = true :=
    Artifact.fermatPaths.bigJump
  have hc := FermatNext.run_gen_check (initialState submissionBytecode input 0) [] (by simp) hjump
  have hword : MachineState.readWord
      (initialState submissionBytecode input 0).executionEnv.calldata 0 =
      UInt256.ofNat (baseSize input) := rfl
  have hbig : baseSize input < 2 ^ 256 := EarlyWordProgram.header_lt input 0
  have hgt : ¬ (UInt256.gt (UInt256.ofNat (baseSize input)) (UInt256.ofNat 32)).toNat = 0 := by
    unfold UInt256.gt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbig, Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
    simp [hb]
  rw [hword, if_neg hgt] at hc
  have s3 := Artifact.fermatPaths.genCheck.steps
    ((environment input).transfer (t := WindowTwentyOneEntry.framed
      (initialState submissionBytecode input 0) (UInt256.ofNat 103) []) rfl rfl) rfl hc
  change Challenge.EvmProof.GasSteps (Main.trampolineState input 0) _ at s1
  exact (Main.gasSteps_entryHop input).trans ((s1.trans s2).trans s3)

/-- A base size above 32 with exponent and modulus sizes 32 is handled by the
certified wide fallback from 238. -/
def big (input : ByteArray) (hvalid : ValidInput input)
    (hsize : exponentSize input = 32 ∧ modulusSize input = 32) (hb : 32 < baseSize input) :
    Handled input := by
  have steps := genBig input hsize hb
  have env : WindowTwentyOneBinding.Environment Artifact.submissionArtifact .Osaka
      (genBigState input) :=
    { sizeBound := by
        change submissionBytecode.size < 2 ^ 256
        rw [submissionBytecode_size]
        norm_num
      code := rfl
      forkEq := rfl
      running := rfl
      noPrecompile := deployAddress_not_precompile }
  obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
    BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
      BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks _ env rfl
      (by simp [genBigState])
      (by simp [genBigState, initialState]; decide)
      rfl hvalid (by show 0 < modulusSize input; omega)
  exact ⟨final, ⟨steps.trans tail⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordCorrect

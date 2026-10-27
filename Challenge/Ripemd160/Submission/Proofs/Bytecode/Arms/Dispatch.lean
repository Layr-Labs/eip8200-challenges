import Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Long
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Patterned128Entry
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

/-!
# Size dispatch into the compact arms

The short size table selects a three-byte trampoline (or the one-byte arm
directly); 256 and 376 bytes are matched by equality.  Every allowed size other
than 1000 reaches its arm and returns RIPEMD-160.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Dispatch
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate J2Moves ReverseLiteralRaw
open Arms.Scan

def trampTemplate (target : Nat) : List Instr := [.op .JUMPDEST] ++ jumpTemplate target

theorem run_tramp (input : ByteArray) (pc target : Nat) (ht : target < 2^256)
    (hv : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code target = true) :
    runInstrSeq (trampTemplate target) (atState (base input) pc []) =
      some (atState (base input) target []) := by
  have h1 := run_jd (base input) (UInt256.ofNat pc) [] (by simp) rfl
  have h2 := run_jump (base input) (pcAfter (UInt256.ofNat pc) [.op .JUMPDEST]) target [] (by simp) rfl
    (by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht]; exact hv)
  exact DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2

def tramp0Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 8051) :=
  StackSiteBuilder.ofSlice (trampTemplate 8051) 6264 (by rfl)
    (by change 6264 + (trampTemplate 8051).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 8051) (by decide)) (by decide)
theorem tramp0_pc : tramp0Site.startPC = UInt256.ofNat 8169 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6264) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp0 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8169 = true :=
  valid_at 6264 8169 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp0 (input : ByteArray) :
    GasSteps (atState (base input) 8169 []) (atState (base input) 8051 []) :=
  RecognitionLift.gasSteps_of_raw tramp0Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp0_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8169 8051 (by decide)
      (valid_at 6186 8051 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short0 (input : ByteArray) (h : input.size = 0) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8169 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 0 8169 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8169 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp0)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp31Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 8761) :=
  StackSiteBuilder.ofSlice (trampTemplate 8761) 6241 (by rfl)
    (by change 6241 + (trampTemplate 8761).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 8761) (by decide)) (by decide)
theorem tramp31_pc : tramp31Site.startPC = UInt256.ofNat 8136 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6241) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp31 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8136 = true :=
  valid_at 6241 8136 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp31 (input : ByteArray) :
    GasSteps (atState (base input) 8136 []) (atState (base input) 8761 []) :=
  RecognitionLift.gasSteps_of_raw tramp31Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp31_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8136 8761 (by decide)
      (valid_at 6407 8761 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short31 (input : ByteArray) (h : input.size = 31) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8136 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 31 8136 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8136 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp31)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp32Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 8828) :=
  StackSiteBuilder.ofSlice (trampTemplate 8828) 6261 (by rfl)
    (by change 6261 + (trampTemplate 8828).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 8828) (by decide)) (by decide)
theorem tramp32_pc : tramp32Site.startPC = UInt256.ofNat 8164 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6261) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp32 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8164 = true :=
  valid_at 6261 8164 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp32 (input : ByteArray) :
    GasSteps (atState (base input) 8164 []) (atState (base input) 8828 []) :=
  RecognitionLift.gasSteps_of_raw tramp32Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp32_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8164 8828 (by decide)
      (valid_at 6420 8828 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short32 (input : ByteArray) (h : input.size = 32) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8164 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 32 8164 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8164 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp32)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp55Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 8857) :=
  StackSiteBuilder.ofSlice (trampTemplate 8857) 6211 (by rfl)
    (by change 6211 + (trampTemplate 8857).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 8857) (by decide)) (by decide)
theorem tramp55_pc : tramp55Site.startPC = UInt256.ofNat 8100 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6211) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp55 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8100 = true :=
  valid_at 6211 8100 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp55 (input : ByteArray) :
    GasSteps (atState (base input) 8100 []) (atState (base input) 8857 []) :=
  RecognitionLift.gasSteps_of_raw tramp55Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp55_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8100 8857 (by decide)
      (valid_at 6427 8857 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short55 (input : ByteArray) (h : input.size = 55) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8100 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 55 8100 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8100 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp55)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp56Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 8921) :=
  StackSiteBuilder.ofSlice (trampTemplate 8921) 6249 (by rfl)
    (by change 6249 + (trampTemplate 8921).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 8921) (by decide)) (by decide)
theorem tramp56_pc : tramp56Site.startPC = UInt256.ofNat 8146 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6249) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp56 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8146 = true :=
  valid_at 6249 8146 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp56 (input : ByteArray) :
    GasSteps (atState (base input) 8146 []) (atState (base input) 8921 []) :=
  RecognitionLift.gasSteps_of_raw tramp56Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp56_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8146 8921 (by decide)
      (valid_at 6437 8921 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short56 (input : ByteArray) (h : input.size = 56) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8146 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 56 8146 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8146 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp56)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp63Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 8985) :=
  StackSiteBuilder.ofSlice (trampTemplate 8985) 6234 (by rfl)
    (by change 6234 + (trampTemplate 8985).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 8985) (by decide)) (by decide)
theorem tramp63_pc : tramp63Site.startPC = UInt256.ofNat 8127 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6234) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp63 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8127 = true :=
  valid_at 6234 8127 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp63 (input : ByteArray) :
    GasSteps (atState (base input) 8127 []) (atState (base input) 8985 []) :=
  RecognitionLift.gasSteps_of_raw tramp63Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp63_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8127 8985 (by decide)
      (valid_at 6447 8985 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short63 (input : ByteArray) (h : input.size = 63) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8127 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 63 8127 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8127 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp63)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp64Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 9049) :=
  StackSiteBuilder.ofSlice (trampTemplate 9049) 6258 (by rfl)
    (by change 6258 + (trampTemplate 9049).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 9049) (by decide)) (by decide)
theorem tramp64_pc : tramp64Site.startPC = UInt256.ofNat 8159 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6258) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp64 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8159 = true :=
  valid_at 6258 8159 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp64 (input : ByteArray) :
    GasSteps (atState (base input) 8159 []) (atState (base input) 9049 []) :=
  RecognitionLift.gasSteps_of_raw tramp64Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp64_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8159 9049 (by decide)
      (valid_at 6457 9049 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short64 (input : ByteArray) (h : input.size = 64) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8159 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 64 8159 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8159 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp64)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp65Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 9078) :=
  StackSiteBuilder.ofSlice (trampTemplate 9078) 6268 (by rfl)
    (by change 6268 + (trampTemplate 9078).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 9078) (by decide)) (by decide)
theorem tramp65_pc : tramp65Site.startPC = UInt256.ofNat 8175 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6268) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp65 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8175 = true :=
  valid_at 6268 8175 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp65 (input : ByteArray) :
    GasSteps (atState (base input) 8175 []) (atState (base input) 9078 []) :=
  RecognitionLift.gasSteps_of_raw tramp65Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp65_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8175 9078 (by decide)
      (valid_at 6464 9078 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short65 (input : ByteArray) (h : input.size = 65) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8175 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 65 8175 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8175 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp65)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp119Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 9143) :=
  StackSiteBuilder.ofSlice (trampTemplate 9143) 6219 (by rfl)
    (by change 6219 + (trampTemplate 9143).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 9143) (by decide)) (by decide)
theorem tramp119_pc : tramp119Site.startPC = UInt256.ofNat 8110 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6219) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp119 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8110 = true :=
  valid_at 6219 8110 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp119 (input : ByteArray) :
    GasSteps (atState (base input) 8110 []) (atState (base input) 9143 []) :=
  RecognitionLift.gasSteps_of_raw tramp119Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp119_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8110 9143 (by decide)
      (valid_at 6474 9143 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short119 (input : ByteArray) (h : input.size = 119) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8110 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 119 8110 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8110 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp119)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp120Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 9208) :=
  StackSiteBuilder.ofSlice (trampTemplate 9208) 6252 (by rfl)
    (by change 6252 + (trampTemplate 9208).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 9208) (by decide)) (by decide)
theorem tramp120_pc : tramp120Site.startPC = UInt256.ofNat 8151 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6252) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp120 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8151 = true :=
  valid_at 6252 8151 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp120 (input : ByteArray) :
    GasSteps (atState (base input) 8151 []) (atState (base input) 9208 []) :=
  RecognitionLift.gasSteps_of_raw tramp120Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp120_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8151 9208 (by decide)
      (valid_at 6484 9208 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short120 (input : ByteArray) (h : input.size = 120) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8151 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 120 8151 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8151 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp120)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

def tramp128Site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (trampTemplate 9273) :=
  StackSiteBuilder.ofSlice (trampTemplate 9273) 6208 (by rfl)
    (by change 6208 + (trampTemplate 9273).length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := trampTemplate 9273) (by decide)) (by decide)
theorem tramp128_pc : tramp128Site.startPC = UInt256.ofNat 8095 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6208) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem valid_tramp128 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8095 = true :=
  valid_at 6208 8095 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)
def gasSteps_tramp128 (input : ByteArray) :
    GasSteps (atState (base input) 8095 []) (atState (base input) 9273 []) :=
  RecognitionLift.gasSteps_of_raw tramp128Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using tramp128_pc.symm) (RecognitionLift.advancesAll_sound _ (by decide))
    (run_tramp input 8095 9273 (by decide)
      (valid_at 6494 9273 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)))
def gasSteps_short128 (input : ByteArray) (h : input.size = 128) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8095 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 128 8095 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8095 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_tramp128)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

theorem valid_arm1 : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8180 = true :=
  valid_at 6271 8180 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_short1 (input : ByteArray) (h : input.size = 1) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (atState (base input) 8180 []) := by
  have hs := HoistedInherited.Patterned128Entry.shortSource_eq input 1 8180 h (by decide)
  have hn : (HoistedInherited.Patterned128Entry.shortSource input).toNat = 8180 := by rw [hs]; rfl
  have g := HoistedInherited.Patterned128Entry.gasSteps_short input (by omega)
    (by rw [hn]; exact valid_arm1)
  exact GasSteps.cast g rfl (by rw [hn]; rfl)

/-- The empty input reaches the shared empty-digest arm through its trampoline. -/
def gasSteps_to_empty (input : ByteArray) (hz : input.size = 0) :
    GasSteps (HoistedInherited.DirectGuard.guardEntry input) (HoistedInherited.AbcArm.emptyEntry input) :=
  (gasSteps_short0 input hz).trans (gasSteps_tramp0 input)

/-- Every allowed size other than 1000 returns the reference digest. -/
theorem from_entry (input : ByteArray) (hfit : CalldataFits input)
    (hn : RecognitionAccumulator.Allowed input.size) (h1000 : input.size ≠ 1000)
    (hguard : GasSteps (initialState HoistedInherited.submissionBytecode input 0)
      (HoistedInherited.DirectGuard.guardEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState HoistedInherited.submissionBytecode input gas) (.returned (spec input)) := by
  have hn' := hn
  unfold RecognitionAccumulator.Allowed at hn'
  rcases hn' with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have g := hguard.trans ((gasSteps_short1 input h).trans (Each.gasSteps_arm1 input))
    exact Finish.arm_correct input hfit 1 (h ▸ hn) h 8244 g
      (Finish.finish_gasSteps input 1 8244 Finish.finishSite0 Finish.finishSite0_pc)
  · have g := hguard.trans (((gasSteps_short31 input h).trans (gasSteps_tramp31 input)).trans (Each.gasSteps_arm31 input))
    exact Finish.arm_correct input hfit 31 (h ▸ hn) h 8825 g
      (Finish.finish_gasSteps input 31 8825 Finish.finishSite1 Finish.finishSite1_pc)
  · have g := hguard.trans (((gasSteps_short32 input h).trans (gasSteps_tramp32 input)).trans (Each.gasSteps_arm32 input))
    exact Finish.arm_correct input hfit 32 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 32 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short55 input h).trans (gasSteps_tramp55 input)).trans (Each.gasSteps_arm55 input))
    exact Finish.arm_correct input hfit 55 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 55 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short56 input h).trans (gasSteps_tramp56 input)).trans (Each.gasSteps_arm56 input))
    exact Finish.arm_correct input hfit 56 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 56 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short63 input h).trans (gasSteps_tramp63 input)).trans (Each.gasSteps_arm63 input))
    exact Finish.arm_correct input hfit 63 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 63 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short64 input h).trans (gasSteps_tramp64 input)).trans (Each.gasSteps_arm64 input))
    exact Finish.arm_correct input hfit 64 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 64 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short65 input h).trans (gasSteps_tramp65 input)).trans (Each.gasSteps_arm65 input))
    exact Finish.arm_correct input hfit 65 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 65 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short119 input h).trans (gasSteps_tramp119 input)).trans (Each.gasSteps_arm119 input))
    exact Finish.arm_correct input hfit 119 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 119 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short120 input h).trans (gasSteps_tramp120 input)).trans (Each.gasSteps_arm120 input))
    exact Finish.arm_correct input hfit 120 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 120 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans (((gasSteps_short128 input h).trans (gasSteps_tramp128 input)).trans (Each.gasSteps_arm128 input))
    exact Finish.arm_correct input hfit 128 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 128 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · have g := hguard.trans ((GasSteps.cast (HoistedInherited.Patterned128Entry.gasSteps_256 input hfit h
        (valid_at 6501 9302 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))) rfl rfl).trans (Each.gasSteps_arm256 input))
    exact Finish.arm_correct input hfit 256 (h ▸ hn) h 8758 g
      (Finish.finish_gasSteps input 256 8758 Finish.finishSite2 Finish.finishSite2_pc)
  · exact Long.correct376 input hfit h (hguard.trans (GasSteps.cast
      (HoistedInherited.Patterned128Entry.gasSteps_376 input hfit h
        (valid_at 6508 9331 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))) rfl rfl))
  · exact absurd h h1000

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Dispatch

import Challenge.Ripemd160.Submission.Local20261028.RecArmsScan
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Generated per-arm and per-chain-entry site certificates. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Each
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralRawV4 DirectLiteralModel J2Moves ReverseLiteralRaw
open Arms.Scan


def chain1Template : List Instr := chainTemplate 1
theorem chain1_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6293).take chain1Template.length = chain1Template := by rfl
def chain1Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain1Template :=
  StackSiteBuilder.ofSlice chain1Template 6293 chain1_slice
    (by change 6293 + chain1Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain1Template) (by decide)) (by decide)
theorem chain1_pc : chain1Site.startPC = UInt256.ofNat 8715 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6293) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain1_form : ∀ i ∈ chain1Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain1 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 8715 = true :=
  valid_at 6293 8715 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain1 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 8715 [a])
      {prepared input n with pc := if (rev input a 1).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 8715) a [] (by simp) rfl rfl 1 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 8715) (chainTemplate 1) = UInt256.ofNat 8758 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain1Template (atState (prepared input n) 8715 [a]) =
      some {prepared input n with pc := if (rev input a 1).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain1Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain1_pc.symm) chain1_form h'


def chain2Template : List Instr := chainTemplate 2
theorem chain2_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6287).take chain2Template.length = chain2Template := by rfl
def chain2Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain2Template :=
  StackSiteBuilder.ofSlice chain2Template 6287 chain2_slice
    (by change 6287 + chain2Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain2Template) (by decide)) (by decide)
theorem chain2_pc : chain2Site.startPC = UInt256.ofNat 8677 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6287) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain2_form : ∀ i ∈ chain2Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain2 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 8677 = true :=
  valid_at 6287 8677 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain2 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 8677 [a])
      {prepared input n with pc := if (rev input a 2).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 8677) a [] (by simp) rfl rfl 2 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 8677) (chainTemplate 2) = UInt256.ofNat 8758 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain2Template (atState (prepared input n) 8677 [a]) =
      some {prepared input n with pc := if (rev input a 2).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain2Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain2_pc.symm) chain2_form h'


def chain3Template : List Instr := chainTemplate 3
theorem chain3_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6281).take chain3Template.length = chain3Template := by rfl
def chain3Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain3Template :=
  StackSiteBuilder.ofSlice chain3Template 6281 chain3_slice
    (by change 6281 + chain3Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain3Template) (by decide)) (by decide)
theorem chain3_pc : chain3Site.startPC = UInt256.ofNat 8638 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6281) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain3_form : ∀ i ∈ chain3Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain3 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 8638 = true :=
  valid_at 6281 8638 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain3 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 8638 [a])
      {prepared input n with pc := if (rev input a 3).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 8638) a [] (by simp) rfl rfl 3 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 8638) (chainTemplate 3) = UInt256.ofNat 8758 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain3Template (atState (prepared input n) 8638 [a]) =
      some {prepared input n with pc := if (rev input a 3).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain3Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain3_pc.symm) chain3_form h'


def chain4Template : List Instr := chainTemplate 4
theorem chain4_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6275).take chain4Template.length = chain4Template := by rfl
def chain4Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain4Template :=
  StackSiteBuilder.ofSlice chain4Template 6275 chain4_slice
    (by change 6275 + chain4Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain4Template) (by decide)) (by decide)
theorem chain4_pc : chain4Site.startPC = UInt256.ofNat 8599 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6275) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain4_form : ∀ i ∈ chain4Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain4 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 8599 = true :=
  valid_at 6275 8599 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain4 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 8599 [a])
      {prepared input n with pc := if (rev input a 4).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 8599) a [] (by simp) rfl rfl 4 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 8599) (chainTemplate 4) = UInt256.ofNat 8758 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain4Template (atState (prepared input n) 8599 [a]) =
      some {prepared input n with pc := if (rev input a 4).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain4Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain4_pc.symm) chain4_form h'


def chain8Template : List Instr := chainTemplate 8
theorem chain8_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6254).take chain8Template.length = chain8Template := by rfl
def chain8Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain8Template :=
  StackSiteBuilder.ofSlice chain8Template 6254 chain8_slice
    (by change 6254 + chain8Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain8Template) (by decide)) (by decide)
theorem chain8_pc : chain8Site.startPC = UInt256.ofNat 8446 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6254) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain8_form : ∀ i ∈ chain8Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain8 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 8446 = true :=
  valid_at 6254 8446 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain8 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 8446 [a])
      {prepared input n with pc := if (rev input a 8).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 8446) a [] (by simp) rfl rfl 8 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 8446) (chainTemplate 8) = UInt256.ofNat 8758 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain8Template (atState (prepared input n) 8446 [a]) =
      some {prepared input n with pc := if (rev input a 8).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain8Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain8_pc.symm) chain8_form h'


def arm1Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 1) ++ prefixTemplate 1 ++ Scan.resultTemplate
theorem arm1_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6169).take arm1Template.length = arm1Template := by rfl
def arm1Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm1Template :=
  StackSiteBuilder.ofSlice arm1Template 6169 arm1_slice
    (by change 6169 + arm1Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm1Template) (by decide)) (by decide)
theorem arm1_pc : arm1Site.startPC = UInt256.ofNat 8180 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6169) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm1_form : ∀ i ∈ arm1Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm1 (input : ByteArray) :
    GasSteps (atState (base input) 8180 [])
      {prepared input 1 with pc := if (ZeroTailModel.result input 1).toNat = 0 then UInt256.ofNat 8244 else UInt256.ofNat 8078, stack := []} := by
  have h1 := Scan.run_store input (UInt256.ofNat 8180) 1
  have h2 := Scan.run_prefix (prepared input 1) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8180))
    1 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := Scan.run_result (prepared input 1)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8180)) (prefixTemplate 1))
    (ZeroTailModel.tailDiff input 1) [] (by simp) rfl (by rw [prepared_code]; exact valid_fail)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have hend : pcAfter (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8180))
      (prefixTemplate 1)) Scan.resultTemplate = UInt256.ofNat 8244 := by decide
  rw [hend] at hall
  have hres : ZeroTailModel.result input 1 = ZeroTailModel.tailDiff input 1 := by
    simp [ZeroTailModel.result, last, rev]
  have h' : runInstrSeq arm1Template (atState (base input) 8180 []) =
      some {prepared input 1 with pc := if (ZeroTailModel.result input 1).toNat = 0 then UInt256.ofNat 8244 else UInt256.ofNat 8078, stack := []} := by
    rw [hres]
    simpa only [arm1Template, atState, List.append_assoc] using hall
  exact RecognitionLift.gasSteps_of_raw arm1Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm1_pc.symm) arm1_form h'


def arm31Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 31) ++ prefixTemplate 31 ++ Scan.resultTemplate
theorem arm31_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6305).take arm31Template.length = arm31Template := by rfl
def arm31Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm31Template :=
  StackSiteBuilder.ofSlice arm31Template 6305 arm31_slice
    (by change 6305 + arm31Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm31Template) (by decide)) (by decide)
theorem arm31_pc : arm31Site.startPC = UInt256.ofNat 8761 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6305) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm31_form : ∀ i ∈ arm31Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm31 (input : ByteArray) :
    GasSteps (atState (base input) 8761 [])
      {prepared input 31 with pc := if (ZeroTailModel.result input 31).toNat = 0 then UInt256.ofNat 8825 else UInt256.ofNat 8078, stack := []} := by
  have h1 := Scan.run_store input (UInt256.ofNat 8761) 31
  have h2 := Scan.run_prefix (prepared input 31) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8761))
    31 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := Scan.run_result (prepared input 31)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8761)) (prefixTemplate 31))
    (ZeroTailModel.tailDiff input 31) [] (by simp) rfl (by rw [prepared_code]; exact valid_fail)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have hend : pcAfter (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8761))
      (prefixTemplate 31)) Scan.resultTemplate = UInt256.ofNat 8825 := by decide
  rw [hend] at hall
  have hres : ZeroTailModel.result input 31 = ZeroTailModel.tailDiff input 31 := by
    simp [ZeroTailModel.result, last, rev]
  have h' : runInstrSeq arm31Template (atState (base input) 8761 []) =
      some {prepared input 31 with pc := if (ZeroTailModel.result input 31).toNat = 0 then UInt256.ofNat 8825 else UInt256.ofNat 8078, stack := []} := by
    rw [hres]
    simpa only [arm31Template, atState, List.append_assoc] using hall
  exact RecognitionLift.gasSteps_of_raw arm31Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm31_pc.symm) arm31_form h'


def arm32Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 32) ++ startTemplate 32 ++ jumpTemplate 8715
theorem arm32_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6318).take arm32Template.length = arm32Template := by rfl
def arm32Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm32Template :=
  StackSiteBuilder.ofSlice arm32Template 6318 arm32_slice
    (by change 6318 + arm32Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm32Template) (by decide)) (by decide)
theorem arm32_pc : arm32Site.startPC = UInt256.ofNat 8828 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6318) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm32_form : ∀ i ∈ arm32Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm32_entry (input : ByteArray) :
    GasSteps (atState (base input) 8828 []) (atState (prepared input 32) 8715 [startValue input 32]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 8828) 32
  have h2 := Scan.run_start (prepared input 32) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8828))
    32 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 32)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8828)) (startTemplate 32))
    8715 [startValue input 32] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8715).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm32Template (atState (base input) 8828 []) =
      some (atState (prepared input 32) 8715 [startValue input 32]) := by
    simpa only [arm32Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm32Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm32_pc.symm) arm32_form h'

theorem value32 (input : ByteArray) :
    rev input (startValue input 32) 1 = ZeroTailModel.result input 32 :=
  Scan.value_full input 32 (by decide) (by decide)

def gasSteps_arm32 (input : ByteArray) :
    GasSteps (atState (base input) 8828 [])
      {prepared input 32 with pc := if (ZeroTailModel.result input 32).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm32_entry input).trans (gasSteps_chain1 input 32 (startValue input 32))
  rw [value32] at g
  exact g


def arm55Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 55) ++ startTemplate 55 ++ jumpTemplate 8715
theorem arm55_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6325).take arm55Template.length = arm55Template := by rfl
def arm55Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm55Template :=
  StackSiteBuilder.ofSlice arm55Template 6325 arm55_slice
    (by change 6325 + arm55Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm55Template) (by decide)) (by decide)
theorem arm55_pc : arm55Site.startPC = UInt256.ofNat 8857 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6325) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm55_form : ∀ i ∈ arm55Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm55_entry (input : ByteArray) :
    GasSteps (atState (base input) 8857 []) (atState (prepared input 55) 8715 [startValue input 55]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 8857) 55
  have h2 := Scan.run_start (prepared input 55) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8857))
    55 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 55)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8857)) (startTemplate 55))
    8715 [startValue input 55] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8715).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm55Template (atState (base input) 8857 []) =
      some (atState (prepared input 55) 8715 [startValue input 55]) := by
    simpa only [arm55Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm55Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm55_pc.symm) arm55_form h'

theorem value55 (input : ByteArray) :
    rev input (startValue input 55) 1 = ZeroTailModel.result input 55 :=
  Scan.value_partial input 55 (by decide)

def gasSteps_arm55 (input : ByteArray) :
    GasSteps (atState (base input) 8857 [])
      {prepared input 55 with pc := if (ZeroTailModel.result input 55).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm55_entry input).trans (gasSteps_chain1 input 55 (startValue input 55))
  rw [value55] at g
  exact g


def arm56Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 56) ++ startTemplate 56 ++ jumpTemplate 8715
theorem arm56_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6335).take arm56Template.length = arm56Template := by rfl
def arm56Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm56Template :=
  StackSiteBuilder.ofSlice arm56Template 6335 arm56_slice
    (by change 6335 + arm56Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm56Template) (by decide)) (by decide)
theorem arm56_pc : arm56Site.startPC = UInt256.ofNat 8921 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6335) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm56_form : ∀ i ∈ arm56Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm56_entry (input : ByteArray) :
    GasSteps (atState (base input) 8921 []) (atState (prepared input 56) 8715 [startValue input 56]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 8921) 56
  have h2 := Scan.run_start (prepared input 56) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8921))
    56 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 56)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8921)) (startTemplate 56))
    8715 [startValue input 56] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8715).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm56Template (atState (base input) 8921 []) =
      some (atState (prepared input 56) 8715 [startValue input 56]) := by
    simpa only [arm56Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm56Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm56_pc.symm) arm56_form h'

theorem value56 (input : ByteArray) :
    rev input (startValue input 56) 1 = ZeroTailModel.result input 56 :=
  Scan.value_partial input 56 (by decide)

def gasSteps_arm56 (input : ByteArray) :
    GasSteps (atState (base input) 8921 [])
      {prepared input 56 with pc := if (ZeroTailModel.result input 56).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm56_entry input).trans (gasSteps_chain1 input 56 (startValue input 56))
  rw [value56] at g
  exact g


def arm63Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 63) ++ startTemplate 63 ++ jumpTemplate 8715
theorem arm63_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6345).take arm63Template.length = arm63Template := by rfl
def arm63Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm63Template :=
  StackSiteBuilder.ofSlice arm63Template 6345 arm63_slice
    (by change 6345 + arm63Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm63Template) (by decide)) (by decide)
theorem arm63_pc : arm63Site.startPC = UInt256.ofNat 8985 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6345) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm63_form : ∀ i ∈ arm63Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm63_entry (input : ByteArray) :
    GasSteps (atState (base input) 8985 []) (atState (prepared input 63) 8715 [startValue input 63]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 8985) 63
  have h2 := Scan.run_start (prepared input 63) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8985))
    63 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 63)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 8985)) (startTemplate 63))
    8715 [startValue input 63] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8715).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm63Template (atState (base input) 8985 []) =
      some (atState (prepared input 63) 8715 [startValue input 63]) := by
    simpa only [arm63Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm63Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm63_pc.symm) arm63_form h'

theorem value63 (input : ByteArray) :
    rev input (startValue input 63) 1 = ZeroTailModel.result input 63 :=
  Scan.value_partial input 63 (by decide)

def gasSteps_arm63 (input : ByteArray) :
    GasSteps (atState (base input) 8985 [])
      {prepared input 63 with pc := if (ZeroTailModel.result input 63).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm63_entry input).trans (gasSteps_chain1 input 63 (startValue input 63))
  rw [value63] at g
  exact g


def arm64Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 64) ++ startTemplate 64 ++ jumpTemplate 8677
theorem arm64_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6355).take arm64Template.length = arm64Template := by rfl
def arm64Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm64Template :=
  StackSiteBuilder.ofSlice arm64Template 6355 arm64_slice
    (by change 6355 + arm64Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm64Template) (by decide)) (by decide)
theorem arm64_pc : arm64Site.startPC = UInt256.ofNat 9049 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6355) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm64_form : ∀ i ∈ arm64Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm64_entry (input : ByteArray) :
    GasSteps (atState (base input) 9049 []) (atState (prepared input 64) 8677 [startValue input 64]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 9049) 64
  have h2 := Scan.run_start (prepared input 64) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9049))
    64 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 64)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9049)) (startTemplate 64))
    8677 [startValue input 64] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8677).toNat = true
      exact valid_chain2)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm64Template (atState (base input) 9049 []) =
      some (atState (prepared input 64) 8677 [startValue input 64]) := by
    simpa only [arm64Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm64Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm64_pc.symm) arm64_form h'

theorem value64 (input : ByteArray) :
    rev input (startValue input 64) 2 = ZeroTailModel.result input 64 :=
  Scan.value_full input 64 (by decide) (by decide)

def gasSteps_arm64 (input : ByteArray) :
    GasSteps (atState (base input) 9049 [])
      {prepared input 64 with pc := if (ZeroTailModel.result input 64).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm64_entry input).trans (gasSteps_chain2 input 64 (startValue input 64))
  rw [value64] at g
  exact g


def arm65Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 65) ++ startTemplate 65 ++ jumpTemplate 8677
theorem arm65_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6362).take arm65Template.length = arm65Template := by rfl
def arm65Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm65Template :=
  StackSiteBuilder.ofSlice arm65Template 6362 arm65_slice
    (by change 6362 + arm65Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm65Template) (by decide)) (by decide)
theorem arm65_pc : arm65Site.startPC = UInt256.ofNat 9078 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6362) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm65_form : ∀ i ∈ arm65Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm65_entry (input : ByteArray) :
    GasSteps (atState (base input) 9078 []) (atState (prepared input 65) 8677 [startValue input 65]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 9078) 65
  have h2 := Scan.run_start (prepared input 65) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9078))
    65 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 65)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9078)) (startTemplate 65))
    8677 [startValue input 65] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8677).toNat = true
      exact valid_chain2)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm65Template (atState (base input) 9078 []) =
      some (atState (prepared input 65) 8677 [startValue input 65]) := by
    simpa only [arm65Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm65Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm65_pc.symm) arm65_form h'

theorem value65 (input : ByteArray) :
    rev input (startValue input 65) 2 = ZeroTailModel.result input 65 :=
  Scan.value_partial input 65 (by decide)

def gasSteps_arm65 (input : ByteArray) :
    GasSteps (atState (base input) 9078 [])
      {prepared input 65 with pc := if (ZeroTailModel.result input 65).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm65_entry input).trans (gasSteps_chain2 input 65 (startValue input 65))
  rw [value65] at g
  exact g


def arm119Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 119) ++ startTemplate 119 ++ jumpTemplate 8638
theorem arm119_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6372).take arm119Template.length = arm119Template := by rfl
def arm119Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm119Template :=
  StackSiteBuilder.ofSlice arm119Template 6372 arm119_slice
    (by change 6372 + arm119Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm119Template) (by decide)) (by decide)
theorem arm119_pc : arm119Site.startPC = UInt256.ofNat 9143 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6372) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm119_form : ∀ i ∈ arm119Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm119_entry (input : ByteArray) :
    GasSteps (atState (base input) 9143 []) (atState (prepared input 119) 8638 [startValue input 119]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 9143) 119
  have h2 := Scan.run_start (prepared input 119) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9143))
    119 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 119)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9143)) (startTemplate 119))
    8638 [startValue input 119] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8638).toNat = true
      exact valid_chain3)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm119Template (atState (base input) 9143 []) =
      some (atState (prepared input 119) 8638 [startValue input 119]) := by
    simpa only [arm119Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm119Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm119_pc.symm) arm119_form h'

theorem value119 (input : ByteArray) :
    rev input (startValue input 119) 3 = ZeroTailModel.result input 119 :=
  Scan.value_partial input 119 (by decide)

def gasSteps_arm119 (input : ByteArray) :
    GasSteps (atState (base input) 9143 [])
      {prepared input 119 with pc := if (ZeroTailModel.result input 119).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm119_entry input).trans (gasSteps_chain3 input 119 (startValue input 119))
  rw [value119] at g
  exact g


def arm120Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 120) ++ startTemplate 120 ++ jumpTemplate 8638
theorem arm120_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6382).take arm120Template.length = arm120Template := by rfl
def arm120Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm120Template :=
  StackSiteBuilder.ofSlice arm120Template 6382 arm120_slice
    (by change 6382 + arm120Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm120Template) (by decide)) (by decide)
theorem arm120_pc : arm120Site.startPC = UInt256.ofNat 9208 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6382) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm120_form : ∀ i ∈ arm120Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm120_entry (input : ByteArray) :
    GasSteps (atState (base input) 9208 []) (atState (prepared input 120) 8638 [startValue input 120]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 9208) 120
  have h2 := Scan.run_start (prepared input 120) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9208))
    120 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 120)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9208)) (startTemplate 120))
    8638 [startValue input 120] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8638).toNat = true
      exact valid_chain3)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm120Template (atState (base input) 9208 []) =
      some (atState (prepared input 120) 8638 [startValue input 120]) := by
    simpa only [arm120Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm120Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm120_pc.symm) arm120_form h'

theorem value120 (input : ByteArray) :
    rev input (startValue input 120) 3 = ZeroTailModel.result input 120 :=
  Scan.value_partial input 120 (by decide)

def gasSteps_arm120 (input : ByteArray) :
    GasSteps (atState (base input) 9208 [])
      {prepared input 120 with pc := if (ZeroTailModel.result input 120).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm120_entry input).trans (gasSteps_chain3 input 120 (startValue input 120))
  rw [value120] at g
  exact g


def arm128Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 128) ++ startTemplate 128 ++ jumpTemplate 8599
theorem arm128_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6392).take arm128Template.length = arm128Template := by rfl
def arm128Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm128Template :=
  StackSiteBuilder.ofSlice arm128Template 6392 arm128_slice
    (by change 6392 + arm128Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm128Template) (by decide)) (by decide)
theorem arm128_pc : arm128Site.startPC = UInt256.ofNat 9273 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6392) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm128_form : ∀ i ∈ arm128Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm128_entry (input : ByteArray) :
    GasSteps (atState (base input) 9273 []) (atState (prepared input 128) 8599 [startValue input 128]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 9273) 128
  have h2 := Scan.run_start (prepared input 128) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9273))
    128 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 128)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9273)) (startTemplate 128))
    8599 [startValue input 128] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8599).toNat = true
      exact valid_chain4)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm128Template (atState (base input) 9273 []) =
      some (atState (prepared input 128) 8599 [startValue input 128]) := by
    simpa only [arm128Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm128Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm128_pc.symm) arm128_form h'

theorem value128 (input : ByteArray) :
    rev input (startValue input 128) 4 = ZeroTailModel.result input 128 :=
  Scan.value_full input 128 (by decide) (by decide)

def gasSteps_arm128 (input : ByteArray) :
    GasSteps (atState (base input) 9273 [])
      {prepared input 128 with pc := if (ZeroTailModel.result input 128).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm128_entry input).trans (gasSteps_chain4 input 128 (startValue input 128))
  rw [value128] at g
  exact g


def arm256Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 256) ++ startTemplate 256 ++ jumpTemplate 8446
theorem arm256_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 6399).take arm256Template.length = arm256Template := by rfl
def arm256Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm256Template :=
  StackSiteBuilder.ofSlice arm256Template 6399 arm256_slice
    (by change 6399 + arm256Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm256Template) (by decide)) (by decide)
theorem arm256_pc : arm256Site.startPC = UInt256.ofNat 9302 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6399) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm256_form : ∀ i ∈ arm256Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm256_entry (input : ByteArray) :
    GasSteps (atState (base input) 9302 []) (atState (prepared input 256) 8446 [startValue input 256]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 9302) 256
  have h2 := Scan.run_start (prepared input 256) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9302))
    256 (by decide) [] (by simp) rfl rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 256)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 9302)) (startTemplate 256))
    8446 [startValue input 256] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 8446).toNat = true
      exact valid_chain8)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm256Template (atState (base input) 9302 []) =
      some (atState (prepared input 256) 8446 [startValue input 256]) := by
    simpa only [arm256Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm256Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm256_pc.symm) arm256_form h'

theorem value256 (input : ByteArray) :
    rev input (startValue input 256) 8 = ZeroTailModel.result input 256 :=
  Scan.value_full input 256 (by decide) (by decide)

def gasSteps_arm256 (input : ByteArray) :
    GasSteps (atState (base input) 9302 [])
      {prepared input 256 with pc := if (ZeroTailModel.result input 256).toNat = 0 then UInt256.ofNat 8758 else UInt256.ofNat 8078, stack := []} := by
  have g := (gasSteps_arm256_entry input).trans (gasSteps_chain8 input 256 (startValue input 256))
  rw [value256] at g
  exact g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Each


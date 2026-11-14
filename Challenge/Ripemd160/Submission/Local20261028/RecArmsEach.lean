import Challenge.Ripemd160.Submission.Local20261028.RecArmsScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcSizeGuard
import Challenge.EvmProof.Bytes
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
    (Control.Artifact.submissionArtifact.instructions.drop 3521).take chain1Template.length = chain1Template := by rfl
def chain1Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain1Template :=
  StackSiteBuilder.ofSlice chain1Template 3521 chain1_slice
    (by change 3521 + chain1Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain1Template) (by decide)) (by decide)
theorem chain1_pc : chain1Site.startPC = UInt256.ofNat 5200 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3521) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain1_form : ∀ i ∈ chain1Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain1 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 5200 = true :=
  valid_at 3521 5200 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain1 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 5200 [a])
      {prepared input n with pc := if (rev input a 1).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 5200) a [] (by simp) rfl rfl 1 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 5200) (chainTemplate 1) = UInt256.ofNat 5243 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain1Template (atState (prepared input n) 5200 [a]) =
      some {prepared input n with pc := if (rev input a 1).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain1Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain1_pc.symm) chain1_form h'


def chain2Template : List Instr := chainTemplate 2
theorem chain2_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3515).take chain2Template.length = chain2Template := by rfl
def chain2Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain2Template :=
  StackSiteBuilder.ofSlice chain2Template 3515 chain2_slice
    (by change 3515 + chain2Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain2Template) (by decide)) (by decide)
theorem chain2_pc : chain2Site.startPC = UInt256.ofNat 5162 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3515) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain2_form : ∀ i ∈ chain2Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain2 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 5162 = true :=
  valid_at 3515 5162 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain2 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 5162 [a])
      {prepared input n with pc := if (rev input a 2).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 5162) a [] (by simp) rfl rfl 2 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 5162) (chainTemplate 2) = UInt256.ofNat 5243 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain2Template (atState (prepared input n) 5162 [a]) =
      some {prepared input n with pc := if (rev input a 2).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain2Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain2_pc.symm) chain2_form h'


def chain3Template : List Instr := chainTemplate 3
theorem chain3_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3509).take chain3Template.length = chain3Template := by rfl
def chain3Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain3Template :=
  StackSiteBuilder.ofSlice chain3Template 3509 chain3_slice
    (by change 3509 + chain3Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain3Template) (by decide)) (by decide)
theorem chain3_pc : chain3Site.startPC = UInt256.ofNat 5123 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3509) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain3_form : ∀ i ∈ chain3Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain3 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 5123 = true :=
  valid_at 3509 5123 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain3 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 5123 [a])
      {prepared input n with pc := if (rev input a 3).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 5123) a [] (by simp) rfl rfl 3 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 5123) (chainTemplate 3) = UInt256.ofNat 5243 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain3Template (atState (prepared input n) 5123 [a]) =
      some {prepared input n with pc := if (rev input a 3).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain3Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain3_pc.symm) chain3_form h'


def chain4Template : List Instr := chainTemplate 4
theorem chain4_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3503).take chain4Template.length = chain4Template := by rfl
def chain4Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain4Template :=
  StackSiteBuilder.ofSlice chain4Template 3503 chain4_slice
    (by change 3503 + chain4Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain4Template) (by decide)) (by decide)
theorem chain4_pc : chain4Site.startPC = UInt256.ofNat 5084 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3503) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain4_form : ∀ i ∈ chain4Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain4 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 5084 = true :=
  valid_at 3503 5084 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain4 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 5084 [a])
      {prepared input n with pc := if (rev input a 4).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 5084) a [] (by simp) rfl rfl 4 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 5084) (chainTemplate 4) = UInt256.ofNat 5243 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain4Template (atState (prepared input n) 5084 [a]) =
      some {prepared input n with pc := if (rev input a 4).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain4Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain4_pc.symm) chain4_form h'


def chain8Template : List Instr := chainTemplate 8
theorem chain8_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3482).take chain8Template.length = chain8Template := by rfl
def chain8Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chain8Template :=
  StackSiteBuilder.ofSlice chain8Template 3482 chain8_slice
    (by change 3482 + chain8Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := chain8Template) (by decide)) (by decide)
theorem chain8_pc : chain8Site.startPC = UInt256.ofNat 4931 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3482) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem chain8_form : ∀ i ∈ chain8Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


theorem valid_chain8 : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code 4931 = true :=
  valid_at 3482 4931 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

def gasSteps_chain8 (input : ByteArray) (n : Nat) (a : UInt256) :
    GasSteps (atState (prepared input n) 4931 [a])
      {prepared input n with pc := if (rev input a 8).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have h := Scan.run_chain (prepared input n) (UInt256.ofNat 4931) a [] (by simp) rfl rfl 8 (by decide) valid_fail
  have hend : pcAfter (UInt256.ofNat 4931) (chainTemplate 8) = UInt256.ofNat 5243 := by decide
  rw [hend] at h
  have h' : runInstrSeq chain8Template (atState (prepared input n) 4931 [a]) =
      some {prepared input n with pc := if (rev input a 8).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := h
  exact RecognitionLift.gasSteps_of_raw chain8Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using chain8_pc.symm) chain8_form h'


def byte1Template : List Instr :=
  [.push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .CALLDATALOAD,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .BYTE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 7), .op .XOR]

def byte1Value (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 7) (UInt256.byteAt ⟨0⟩ (MachineState.readWord input 0))

theorem run_byte1 (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq byte1Template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc byte1Template, stack := byte1Value s.executionEnv.calldata :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  simp (discharger := omega) [byte1Template, byte1Value, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, show rho.length < 1024 by omega, hcap, hzero, UInt256.succ, Instr.size,
    Nat.add_assoc, Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

private theorem tail_after_one (input : ByteArray) (hsize : input.size = 1) (w : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded input 1 w = 0 := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hb := AbcSizeGuard.byte_getD input (1 + w)
    unfold AbcSizeGuard.byte at hb
    rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, ih, hb,
      Memory.getElem?_getD_eq_zero_of_size_le input (1 + w) (by omega)]
    rfl

private theorem readWord_one (input : ByteArray) (hsize : input.size = 1) :
    MachineState.readWord input 0 =
      UInt256.ofNat ((YulSemantics.EVM.byteFrom input.toList 0).toNat * 2 ^ 248) := by
  apply Word.word_ext
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 0 1 31
  have hone := Challenge.EvmProof.Bytes.bytesToNatPadded_succ input 0 0
  simp only [Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width, Nat.zero_mul,
    Nat.zero_add] at hone
  rw [hone, Nat.zero_add, tail_after_one input hsize 31] at hsplit
  have hb : (YulSemantics.EVM.byteFrom input.toList 0).toNat < 256 :=
    (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt
  have hlt : (YulSemantics.EVM.byteFrom input.toList 0).toNat * 2 ^ 248 < 2 ^ 256 :=
    calc (YulSemantics.EVM.byteFrom input.toList 0).toNat * 2 ^ 248
        < 256 * 2 ^ 248 := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      _ = 2 ^ 256 := by norm_num
  rw [Challenge.EvmProof.Bytes.readWord_toNat, Word.word_toNat_ofNat,
    show (32 : Nat) = 1 + 31 by rfl, hsplit, Nat.add_zero,
    show (256 : Nat) ^ 31 = 2 ^ 248 by norm_num]
  exact (Nat.mod_eq_of_lt hlt).symm

private theorem byte1_key : ∀ b, b < 256 →
    ((UInt256.xor (UInt256.ofNat 7) (UInt256.ofNat b)).toNat = 0 ↔
      (UInt256.xor (ZeroTailModel.expectedLast 1) (UInt256.ofNat (b * 2 ^ 248))).toNat = 0) := by
  decide +kernel

theorem byte1_zero_iff (input : ByteArray) (hsize : input.size = 1) :
    (byte1Value input).toNat = 0 ↔ (ZeroTailModel.tailDiff input 1).toNat = 0 := by
  have hb : (YulSemantics.EVM.byteFrom input.toList 0).toNat < 256 :=
    (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt
  rw [byte1Value, Challenge.EvmProof.Bytes.byteAt_zero_readWord, ZeroTailModel.tailDiff,
    show 32 * DirectLiteralModel.last 1 = 0 by decide, readWord_one input hsize]
  exact byte1_key _ hb

def arm1Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 1) ++ byte1Template ++ Scan.resultTemplate
theorem arm1_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3391).take arm1Template.length = arm1Template := by rfl
def arm1Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm1Template :=
  StackSiteBuilder.ofSlice arm1Template 3391 arm1_slice
    (by change 3391 + arm1Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm1Template) (by decide)) (by decide)
theorem arm1_pc : arm1Site.startPC = UInt256.ofNat 4717 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3391) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm1_form : ∀ i ∈ arm1Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm1 (input : ByteArray) (hsize : input.size = 1) :
    GasSteps (atState (base input) 4717 [])
      {prepared input 1 with pc := if (ZeroTailModel.result input 1).toNat = 0 then UInt256.ofNat 4753 else UInt256.ofNat 4651, stack := []} := by
  have h1 := Scan.run_store input (UInt256.ofNat 4717) 1
  have h2 := run_byte1 (prepared input 1) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 4717))
    [] (by simp) rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := Scan.run_result (prepared input 1)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 4717)) byte1Template)
    (byte1Value input) [] (by simp) rfl (by rw [prepared_code]; exact valid_fail)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have hend : pcAfter (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 4717))
      byte1Template) Scan.resultTemplate = UInt256.ofNat 4753 := by decide
  rw [hend] at hall
  have hres : ZeroTailModel.result input 1 = ZeroTailModel.tailDiff input 1 := by
    simp [ZeroTailModel.result, last, rev]
  have hif : (if (byte1Value input).toNat = 0 then UInt256.ofNat 4753 else UInt256.ofNat 4651) =
      (if (ZeroTailModel.result input 1).toNat = 0 then UInt256.ofNat 4753
        else UInt256.ofNat 4651) := by
    rw [hres]
    exact if_congr (byte1_zero_iff input hsize) rfl rfl
  have h' : runInstrSeq arm1Template (atState (base input) 4717 []) =
      some {prepared input 1 with pc := if (ZeroTailModel.result input 1).toNat = 0 then UInt256.ofNat 4753 else UInt256.ofNat 4651, stack := []} := by
    rw [← hif]
    simpa only [arm1Template, atState, List.append_assoc] using hall
  exact RecognitionLift.gasSteps_of_raw arm1Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm1_pc.symm) arm1_form h'


def arm31Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 31) ++ prefixTemplate 31 ++ Scan.resultTemplate
theorem arm31_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3532).take arm31Template.length = arm31Template := by rfl
def arm31Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm31Template :=
  StackSiteBuilder.ofSlice arm31Template 3532 arm31_slice
    (by change 3532 + arm31Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm31Template) (by decide)) (by decide)
theorem arm31_pc : arm31Site.startPC = UInt256.ofNat 5246 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3532) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm31_form : ∀ i ∈ arm31Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm31 (input : ByteArray) :
    GasSteps (atState (base input) 5246 [])
      {prepared input 31 with pc := if (ZeroTailModel.result input 31).toNat = 0 then UInt256.ofNat 5310 else UInt256.ofNat 4651, stack := []} := by
  have h1 := Scan.run_store input (UInt256.ofNat 5246) 31
  have h2 := Scan.run_prefix (prepared input 31) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5246))
    31 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := Scan.run_result (prepared input 31)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5246)) (prefixTemplate 31))
    (ZeroTailModel.tailDiff input 31) [] (by simp) rfl (by rw [prepared_code]; exact valid_fail)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have hend : pcAfter (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5246))
      (prefixTemplate 31)) Scan.resultTemplate = UInt256.ofNat 5310 := by decide
  rw [hend] at hall
  have hres : ZeroTailModel.result input 31 = ZeroTailModel.tailDiff input 31 := by
    simp [ZeroTailModel.result, last, rev]
  have h' : runInstrSeq arm31Template (atState (base input) 5246 []) =
      some {prepared input 31 with pc := if (ZeroTailModel.result input 31).toNat = 0 then UInt256.ofNat 5310 else UInt256.ofNat 4651, stack := []} := by
    rw [hres]
    simpa only [arm31Template, atState, List.append_assoc] using hall
  exact RecognitionLift.gasSteps_of_raw arm31Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm31_pc.symm) arm31_form h'


def arm32Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 32) ++ startTemplate 32 ++ jumpTemplate 5200
theorem arm32_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3545).take arm32Template.length = arm32Template := by rfl
def arm32Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm32Template :=
  StackSiteBuilder.ofSlice arm32Template 3545 arm32_slice
    (by change 3545 + arm32Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm32Template) (by decide)) (by decide)
theorem arm32_pc : arm32Site.startPC = UInt256.ofNat 5313 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3545) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm32_form : ∀ i ∈ arm32Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm32_entry (input : ByteArray) :
    GasSteps (atState (base input) 5313 []) (atState (prepared input 32) 5200 [startValue input 32]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5313) 32
  have h2 := Scan.run_start (prepared input 32) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5313))
    32 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 32)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5313)) (startTemplate 32))
    5200 [startValue input 32] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5200).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm32Template (atState (base input) 5313 []) =
      some (atState (prepared input 32) 5200 [startValue input 32]) := by
    simpa only [arm32Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm32Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm32_pc.symm) arm32_form h'

theorem value32 (input : ByteArray) :
    rev input (startValue input 32) 1 = ZeroTailModel.result input 32 :=
  Scan.value_full input 32 (by decide) (by decide)

def gasSteps_arm32 (input : ByteArray) :
    GasSteps (atState (base input) 5313 [])
      {prepared input 32 with pc := if (ZeroTailModel.result input 32).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm32_entry input).trans (gasSteps_chain1 input 32 (startValue input 32))
  rw [value32] at g
  exact g


def arm55Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 55) ++ startTemplate 55 ++ jumpTemplate 5200
theorem arm55_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3552).take arm55Template.length = arm55Template := by rfl
def arm55Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm55Template :=
  StackSiteBuilder.ofSlice arm55Template 3552 arm55_slice
    (by change 3552 + arm55Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm55Template) (by decide)) (by decide)
theorem arm55_pc : arm55Site.startPC = UInt256.ofNat 5342 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3552) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm55_form : ∀ i ∈ arm55Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm55_entry (input : ByteArray) :
    GasSteps (atState (base input) 5342 []) (atState (prepared input 55) 5200 [startValue input 55]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5342) 55
  have h2 := Scan.run_start (prepared input 55) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5342))
    55 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 55)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5342)) (startTemplate 55))
    5200 [startValue input 55] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5200).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm55Template (atState (base input) 5342 []) =
      some (atState (prepared input 55) 5200 [startValue input 55]) := by
    simpa only [arm55Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm55Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm55_pc.symm) arm55_form h'

theorem value55 (input : ByteArray) :
    rev input (startValue input 55) 1 = ZeroTailModel.result input 55 :=
  Scan.value_partial input 55 (by decide)

def gasSteps_arm55 (input : ByteArray) :
    GasSteps (atState (base input) 5342 [])
      {prepared input 55 with pc := if (ZeroTailModel.result input 55).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm55_entry input).trans (gasSteps_chain1 input 55 (startValue input 55))
  rw [value55] at g
  exact g


def arm56Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 56) ++ startTemplate 56 ++ jumpTemplate 5200
theorem arm56_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3564).take arm56Template.length = arm56Template := by rfl
def arm56Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm56Template :=
  StackSiteBuilder.ofSlice arm56Template 3564 arm56_slice
    (by change 3564 + arm56Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm56Template) (by decide)) (by decide)
theorem arm56_pc : arm56Site.startPC = UInt256.ofNat 5400 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3564) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm56_form : ∀ i ∈ arm56Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm56_entry (input : ByteArray) (hsize : input.size = 56) :
    GasSteps (atState (base input) 5400 []) (atState (prepared input 56) 5200 [startValue input 56]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5400) 56
  have h2 := Scan.run_start (prepared input 56) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5400))
    56 (by decide) [] (by simp) rfl rfl (fun _ => hsize)
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 56)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5400)) (startTemplate 56))
    5200 [startValue input 56] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5200).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm56Template (atState (base input) 5400 []) =
      some (atState (prepared input 56) 5200 [startValue input 56]) := by
    simpa only [arm56Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm56Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm56_pc.symm) arm56_form h'

theorem value56 (input : ByteArray) :
    rev input (startValue input 56) 1 = ZeroTailModel.result input 56 :=
  Scan.value_partial input 56 (by decide)

def gasSteps_arm56 (input : ByteArray) (hsize : input.size = 56) :
    GasSteps (atState (base input) 5400 [])
      {prepared input 56 with pc := if (ZeroTailModel.result input 56).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm56_entry input hsize).trans (gasSteps_chain1 input 56 (startValue input 56))
  rw [value56] at g
  exact g


def arm63Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 63) ++ startTemplate 63 ++ jumpTemplate 5200
theorem arm63_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3576).take arm63Template.length = arm63Template := by rfl
def arm63Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm63Template :=
  StackSiteBuilder.ofSlice arm63Template 3576 arm63_slice
    (by change 3576 + arm63Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm63Template) (by decide)) (by decide)
theorem arm63_pc : arm63Site.startPC = UInt256.ofNat 5459 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3576) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm63_form : ∀ i ∈ arm63Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm63_entry (input : ByteArray) :
    GasSteps (atState (base input) 5459 []) (atState (prepared input 63) 5200 [startValue input 63]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5459) 63
  have h2 := Scan.run_start (prepared input 63) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5459))
    63 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 63)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5459)) (startTemplate 63))
    5200 [startValue input 63] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5200).toNat = true
      exact valid_chain1)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm63Template (atState (base input) 5459 []) =
      some (atState (prepared input 63) 5200 [startValue input 63]) := by
    simpa only [arm63Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm63Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm63_pc.symm) arm63_form h'

theorem value63 (input : ByteArray) :
    rev input (startValue input 63) 1 = ZeroTailModel.result input 63 :=
  Scan.value_partial input 63 (by decide)

def gasSteps_arm63 (input : ByteArray) :
    GasSteps (atState (base input) 5459 [])
      {prepared input 63 with pc := if (ZeroTailModel.result input 63).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm63_entry input).trans (gasSteps_chain1 input 63 (startValue input 63))
  rw [value63] at g
  exact g


def arm64Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 64) ++ startTemplate 64 ++ jumpTemplate 5162
theorem arm64_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3586).take arm64Template.length = arm64Template := by rfl
def arm64Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm64Template :=
  StackSiteBuilder.ofSlice arm64Template 3586 arm64_slice
    (by change 3586 + arm64Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm64Template) (by decide)) (by decide)
theorem arm64_pc : arm64Site.startPC = UInt256.ofNat 5523 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3586) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm64_form : ∀ i ∈ arm64Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm64_entry (input : ByteArray) :
    GasSteps (atState (base input) 5523 []) (atState (prepared input 64) 5162 [startValue input 64]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5523) 64
  have h2 := Scan.run_start (prepared input 64) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5523))
    64 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 64)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5523)) (startTemplate 64))
    5162 [startValue input 64] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5162).toNat = true
      exact valid_chain2)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm64Template (atState (base input) 5523 []) =
      some (atState (prepared input 64) 5162 [startValue input 64]) := by
    simpa only [arm64Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm64Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm64_pc.symm) arm64_form h'

theorem value64 (input : ByteArray) :
    rev input (startValue input 64) 2 = ZeroTailModel.result input 64 :=
  Scan.value_full input 64 (by decide) (by decide)

def gasSteps_arm64 (input : ByteArray) :
    GasSteps (atState (base input) 5523 [])
      {prepared input 64 with pc := if (ZeroTailModel.result input 64).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm64_entry input).trans (gasSteps_chain2 input 64 (startValue input 64))
  rw [value64] at g
  exact g


def byte65Template : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 64), .op .CALLDATALOAD,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0), .op .BYTE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 71), .op .XOR]

def byte65Value (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 71) (UInt256.byteAt ⟨0⟩ (MachineState.readWord input 64))

theorem run_byte65 (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq byte65Template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc byte65Template, stack := byte65Value s.executionEnv.calldata :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have h64 : ({val := 64} : UInt256).toNat = 64 := rfl
  have h64' : (UInt256.ofNat 64).toNat = 64 := rfl
  simp (discharger := omega) [byte65Template, byte65Value, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, show rho.length < 1024 by omega, hcap, hzero, h64, h64', UInt256.succ, Instr.size,
    Nat.add_assoc, Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

private theorem tail_past_size (input : ByteArray) (m : Nat) (hsize : input.size ≤ m) (w : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded input m w = 0 := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hb := AbcSizeGuard.byte_getD input (m + w)
    unfold AbcSizeGuard.byte at hb
    rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ, ih, hb,
      Memory.getElem?_getD_eq_zero_of_size_le input (m + w) (by omega)]
    rfl

private theorem readWord_64 (input : ByteArray) (hsize : input.size = 65) :
    MachineState.readWord input 64 =
      UInt256.ofNat ((YulSemantics.EVM.byteFrom input.toList 64).toNat * 2 ^ 248) := by
  apply Word.word_ext
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 64 1 31
  have hone := Challenge.EvmProof.Bytes.bytesToNatPadded_succ input 64 0
  simp only [Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width, Nat.zero_mul,
    Nat.zero_add, Nat.add_zero] at hone
  rw [hone, tail_past_size input (64 + 1) (by omega) 31] at hsplit
  have hb : (YulSemantics.EVM.byteFrom input.toList 64).toNat < 256 :=
    (YulSemantics.EVM.byteFrom input.toList 64).toNat_lt
  have hlt : (YulSemantics.EVM.byteFrom input.toList 64).toNat * 2 ^ 248 < 2 ^ 256 :=
    calc (YulSemantics.EVM.byteFrom input.toList 64).toNat * 2 ^ 248
        < 256 * 2 ^ 248 := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      _ = 2 ^ 256 := by norm_num
  rw [Challenge.EvmProof.Bytes.readWord_toNat, Word.word_toNat_ofNat,
    show (32 : Nat) = 1 + 31 by rfl, hsplit, Nat.add_zero,
    show (256 : Nat) ^ 31 = 2 ^ 248 by norm_num]
  exact (Nat.mod_eq_of_lt hlt).symm

private theorem byte65_key : ∀ b, b < 256 →
    ((UInt256.xor (UInt256.ofNat 71) (UInt256.ofNat b)).toNat = 0 ↔
      (UInt256.xor (ZeroTailModel.expectedLast 65) (UInt256.ofNat (b * 2 ^ 248))).toNat = 0) := by
  decide +kernel

theorem byte65_zero_iff (input : ByteArray) (hsize : input.size = 65) :
    (byte65Value input).toNat = 0 ↔ (ZeroTailModel.tailDiff input 65).toNat = 0 := by
  have hb : (YulSemantics.EVM.byteFrom input.toList 64).toNat < 256 :=
    (YulSemantics.EVM.byteFrom input.toList 64).toNat_lt
  rw [byte65Value, Challenge.EvmProof.Bytes.byteAt_zero_readWord, ZeroTailModel.tailDiff,
    show 32 * DirectLiteralModel.last 65 = 64 by decide, readWord_64 input hsize]
  exact byte65_key _ hb

private theorem word_toNat_eq_zero_iff (x : UInt256) : x.toNat = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply Word.word_ext
    rw [h]
    rfl
  · rintro rfl
    rfl

def arm65Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 65) ++ byte65Template ++ jumpTemplate 5162
theorem arm65_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3593).take arm65Template.length = arm65Template := by rfl
def arm65Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm65Template :=
  StackSiteBuilder.ofSlice arm65Template 3593 arm65_slice
    (by change 3593 + arm65Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm65Template) (by decide)) (by decide)
theorem arm65_pc : arm65Site.startPC = UInt256.ofNat 5552 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3593) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm65_form : ∀ i ∈ arm65Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm65_entry (input : ByteArray) :
    GasSteps (atState (base input) 5552 []) (atState (prepared input 65) 5162 [byte65Value input]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5552) 65
  have h2 := run_byte65 (prepared input 65) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5552))
    [] (by simp) rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 65)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5552)) byte65Template)
    5162 [byte65Value input] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5162).toNat = true
      exact valid_chain2)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm65Template (atState (base input) 5552 []) =
      some (atState (prepared input 65) 5162 [byte65Value input]) := by
    simpa only [arm65Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm65Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm65_pc.symm) arm65_form h'

theorem value65 (input : ByteArray) :
    rev input (startValue input 65) 2 = ZeroTailModel.result input 65 :=
  Scan.value_partial input 65 (by decide)

theorem byte65_rev_iff (input : ByteArray) (hsize : input.size = 65) :
    (rev input (byte65Value input) 2).toNat = 0 ↔ (ZeroTailModel.result input 65).toNat = 0 := by
  have hk := byte65_zero_iff input hsize
  rw [word_toNat_eq_zero_iff, word_toNat_eq_zero_iff] at hk
  have hs : startValue input 65 = ZeroTailModel.tailDiff input 65 := by
    simp [startValue]
  rw [← value65 input, hs, word_toNat_eq_zero_iff, word_toNat_eq_zero_iff,
    ZeroTailModel.rev_zero_iff, ZeroTailModel.rev_zero_iff, hk]

def gasSteps_arm65 (input : ByteArray) (hsize : input.size = 65) :
    GasSteps (atState (base input) 5552 [])
      {prepared input 65 with pc := if (ZeroTailModel.result input 65).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm65_entry input).trans (gasSteps_chain2 input 65 (byte65Value input))
  have hif : (if (rev input (byte65Value input) 2).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651) =
      (if (ZeroTailModel.result input 65).toNat = 0 then UInt256.ofNat 5243
        else UInt256.ofNat 4651) :=
    if_congr (byte65_rev_iff input hsize) rfl rfl
  rw [hif] at g
  exact g


def arm119Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 119) ++ startTemplate 119 ++ jumpTemplate 5123
theorem arm119_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3605).take arm119Template.length = arm119Template := by rfl
def arm119Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm119Template :=
  StackSiteBuilder.ofSlice arm119Template 3605 arm119_slice
    (by change 3605 + arm119Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm119Template) (by decide)) (by decide)
theorem arm119_pc : arm119Site.startPC = UInt256.ofNat 5589 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3605) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm119_form : ∀ i ∈ arm119Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm119_entry (input : ByteArray) :
    GasSteps (atState (base input) 5589 []) (atState (prepared input 119) 5123 [startValue input 119]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5589) 119
  have h2 := Scan.run_start (prepared input 119) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5589))
    119 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 119)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5589)) (startTemplate 119))
    5123 [startValue input 119] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5123).toNat = true
      exact valid_chain3)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm119Template (atState (base input) 5589 []) =
      some (atState (prepared input 119) 5123 [startValue input 119]) := by
    simpa only [arm119Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm119Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm119_pc.symm) arm119_form h'

theorem value119 (input : ByteArray) :
    rev input (startValue input 119) 3 = ZeroTailModel.result input 119 :=
  Scan.value_partial input 119 (by decide)

def gasSteps_arm119 (input : ByteArray) :
    GasSteps (atState (base input) 5589 [])
      {prepared input 119 with pc := if (ZeroTailModel.result input 119).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm119_entry input).trans (gasSteps_chain3 input 119 (startValue input 119))
  rw [value119] at g
  exact g


def arm120Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 120) ++ startTemplate 120 ++ jumpTemplate 5123
theorem arm120_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3617).take arm120Template.length = arm120Template := by rfl
def arm120Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm120Template :=
  StackSiteBuilder.ofSlice arm120Template 3617 arm120_slice
    (by change 3617 + arm120Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm120Template) (by decide)) (by decide)
theorem arm120_pc : arm120Site.startPC = UInt256.ofNat 5648 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3617) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm120_form : ∀ i ∈ arm120Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm120_entry (input : ByteArray) :
    GasSteps (atState (base input) 5648 []) (atState (prepared input 120) 5123 [startValue input 120]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5648) 120
  have h2 := Scan.run_start (prepared input 120) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5648))
    120 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 120)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5648)) (startTemplate 120))
    5123 [startValue input 120] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5123).toNat = true
      exact valid_chain3)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm120Template (atState (base input) 5648 []) =
      some (atState (prepared input 120) 5123 [startValue input 120]) := by
    simpa only [arm120Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm120Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm120_pc.symm) arm120_form h'

theorem value120 (input : ByteArray) :
    rev input (startValue input 120) 3 = ZeroTailModel.result input 120 :=
  Scan.value_partial input 120 (by decide)

def gasSteps_arm120 (input : ByteArray) :
    GasSteps (atState (base input) 5648 [])
      {prepared input 120 with pc := if (ZeroTailModel.result input 120).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm120_entry input).trans (gasSteps_chain3 input 120 (startValue input 120))
  rw [value120] at g
  exact g


def arm128Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 128) ++ startTemplate 128 ++ jumpTemplate 5084
theorem arm128_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3627).take arm128Template.length = arm128Template := by rfl
def arm128Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm128Template :=
  StackSiteBuilder.ofSlice arm128Template 3627 arm128_slice
    (by change 3627 + arm128Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm128Template) (by decide)) (by decide)
theorem arm128_pc : arm128Site.startPC = UInt256.ofNat 5713 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3627) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm128_form : ∀ i ∈ arm128Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm128_entry (input : ByteArray) :
    GasSteps (atState (base input) 5713 []) (atState (prepared input 128) 5084 [startValue input 128]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5713) 128
  have h2 := Scan.run_start (prepared input 128) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5713))
    128 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 128)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5713)) (startTemplate 128))
    5084 [startValue input 128] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 5084).toNat = true
      exact valid_chain4)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm128Template (atState (base input) 5713 []) =
      some (atState (prepared input 128) 5084 [startValue input 128]) := by
    simpa only [arm128Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm128Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm128_pc.symm) arm128_form h'

theorem value128 (input : ByteArray) :
    rev input (startValue input 128) 4 = ZeroTailModel.result input 128 :=
  Scan.value_full input 128 (by decide) (by decide)

def gasSteps_arm128 (input : ByteArray) :
    GasSteps (atState (base input) 5713 [])
      {prepared input 128 with pc := if (ZeroTailModel.result input 128).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm128_entry input).trans (gasSteps_chain4 input 128 (startValue input 128))
  rw [value128] at g
  exact g


def arm256Template : List Instr := DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord 256) ++ startTemplate 256 ++ jumpTemplate 4931
theorem arm256_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3634).take arm256Template.length = arm256Template := by rfl
def arm256Site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka arm256Template :=
  StackSiteBuilder.ofSlice arm256Template 3634 arm256_slice
    (by change 3634 + arm256Template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := arm256Template) (by decide)) (by decide)
theorem arm256_pc : arm256Site.startPC = UInt256.ofNat 5742 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3634) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem arm256_form : ∀ i ∈ arm256Template.dropLast, RecognitionLift.Advances i :=
  RecognitionLift.advancesAll_sound _ (by decide)


def gasSteps_arm256_entry (input : ByteArray) :
    GasSteps (atState (base input) 5742 []) (atState (prepared input 256) 4931 [startValue input 256]) := by
  have h1 := Scan.run_store input (UInt256.ofNat 5742) 256
  have h2 := Scan.run_start (prepared input 256) (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5742))
    256 (by decide) [] (by simp) rfl rfl (fun h => absurd h (by decide))
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2
  have h3 := run_jump (prepared input 256)
    (pcAfter (UInt256.add (UInt256.ofNat 24) (UInt256.ofNat 5742)) (startTemplate 256))
    4931 [startValue input 256] (by simp) rfl (by
      change Decode.isValidJumpDest Control.Artifact.submissionArtifact.code (UInt256.ofNat 4931).toNat = true
      exact valid_chain8)
  have hall := DenseScheduleTrace.runInstrSeq_append_running h12 rfl h3
  have h' : runInstrSeq arm256Template (atState (base input) 5742 []) =
      some (atState (prepared input 256) 4931 [startValue input 256]) := by
    simpa only [arm256Template, atState, List.append_assoc, prepared_calldata] using hall
  exact RecognitionLift.gasSteps_of_raw arm256Site _ _ rfl rfl rfl deployAddress_not_precompile
    (by simpa [atState] using arm256_pc.symm) arm256_form h'

theorem value256 (input : ByteArray) :
    rev input (startValue input 256) 8 = ZeroTailModel.result input 256 :=
  Scan.value_full input 256 (by decide) (by decide)

def gasSteps_arm256 (input : ByteArray) :
    GasSteps (atState (base input) 5742 [])
      {prepared input 256 with pc := if (ZeroTailModel.result input 256).toNat = 0 then UInt256.ofNat 5243 else UInt256.ofNat 4651, stack := []} := by
  have g := (gasSteps_arm256_entry input).trans (gasSteps_chain8 input 256 (startValue input 256))
  rw [value256] at g
  exact g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Each


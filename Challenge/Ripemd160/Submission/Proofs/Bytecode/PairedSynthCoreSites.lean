import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate PairedHelperBooleanTrace

/-- Actual instruction windows for the frozen 5359-byte generic paired compressor. -/

theorem group0_slice :
    (Artifact.submissionArtifact.instructions.drop 468).take PairedHelperBooleanTrace.group0Template.length = PairedHelperBooleanTrace.group0Template := by
  rfl

theorem group0_instructionPC :
    Artifact.submissionArtifact.instructionPC 468 = 960 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.group0Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.group0Template 468 group0_slice
    (by
      change 468 + PairedHelperBooleanTrace.group0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.group0Template) (by decide))
    (by decide)

theorem group0Site_startPC : group0Site.startPC = UInt256.ofNat 960 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 468) = UInt256.ofNat 960
  rw [group0_instructionPC]


theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 469).take PairedSynthCoreTrace.inline0Template.length = PairedSynthCoreTrace.inline0Template := by
  rfl

theorem inline0_instructionPC :
    Artifact.submissionArtifact.instructionPC 469 = 981 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline0Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline0Template 469 inline0_slice
    (by
      change 469 + PairedSynthCoreTrace.inline0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline0Template) (by decide))
    (by decide)

theorem inline0Site_startPC : inline0Site.startPC = UInt256.ofNat 981 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 469) = UInt256.ofNat 981
  rw [inline0_instructionPC]


theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 515).take PairedSynthCoreTrace.inline1Template.length = PairedSynthCoreTrace.inline1Template := by
  rfl

theorem inline1_instructionPC :
    Artifact.submissionArtifact.instructionPC 515 = 1033 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline1Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline1Template 515 inline1_slice
    (by
      change 515 + PairedSynthCoreTrace.inline1Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline1Template) (by decide))
    (by decide)

theorem inline1Site_startPC : inline1Site.startPC = UInt256.ofNat 1033 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 515) = UInt256.ofNat 1033
  rw [inline1_instructionPC]


theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 561).take PairedSynthCoreTrace.inline2Template.length = PairedSynthCoreTrace.inline2Template := by
  rfl

theorem inline2_instructionPC :
    Artifact.submissionArtifact.instructionPC 561 = 1085 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline2Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline2Template 561 inline2_slice
    (by
      change 561 + PairedSynthCoreTrace.inline2Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline2Template) (by decide))
    (by decide)

theorem inline2Site_startPC : inline2Site.startPC = UInt256.ofNat 1085 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 561) = UInt256.ofNat 1085
  rw [inline2_instructionPC]


theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 607).take PairedSynthCoreTrace.inline3Template.length = PairedSynthCoreTrace.inline3Template := by
  rfl

theorem inline3_instructionPC :
    Artifact.submissionArtifact.instructionPC 607 = 1138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline3Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline3Template 607 inline3_slice
    (by
      change 607 + PairedSynthCoreTrace.inline3Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline3Template) (by decide))
    (by decide)

theorem inline3Site_startPC : inline3Site.startPC = UInt256.ofNat 1138 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 607) = UInt256.ofNat 1138
  rw [inline3_instructionPC]


theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 653).take PairedSynthCoreTrace.inline4Template.length = PairedSynthCoreTrace.inline4Template := by
  rfl

theorem inline4_instructionPC :
    Artifact.submissionArtifact.instructionPC 653 = 1190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline4Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline4Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline4Template 653 inline4_slice
    (by
      change 653 + PairedSynthCoreTrace.inline4Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline4Template) (by decide))
    (by decide)

theorem inline4Site_startPC : inline4Site.startPC = UInt256.ofNat 1190 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 653) = UInt256.ofNat 1190
  rw [inline4_instructionPC]


theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 700).take PairedSynthCoreTrace.inline5Template.length = PairedSynthCoreTrace.inline5Template := by
  rfl

theorem inline5_instructionPC :
    Artifact.submissionArtifact.instructionPC 700 = 1244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline5Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline5Template 700 inline5_slice
    (by
      change 700 + PairedSynthCoreTrace.inline5Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline5Template) (by decide))
    (by decide)

theorem inline5Site_startPC : inline5Site.startPC = UInt256.ofNat 1244 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 700) = UInt256.ofNat 1244
  rw [inline5_instructionPC]


theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 747).take PairedSynthCoreTrace.inline6Template.length = PairedSynthCoreTrace.inline6Template := by
  rfl

theorem inline6_instructionPC :
    Artifact.submissionArtifact.instructionPC 747 = 1298 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline6Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline6Template 747 inline6_slice
    (by
      change 747 + PairedSynthCoreTrace.inline6Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline6Template) (by decide))
    (by decide)

theorem inline6Site_startPC : inline6Site.startPC = UInt256.ofNat 1298 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 747) = UInt256.ofNat 1298
  rw [inline6_instructionPC]


theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 794).take PairedSynthCoreTrace.inline7Template.length = PairedSynthCoreTrace.inline7Template := by
  rfl

theorem inline7_instructionPC :
    Artifact.submissionArtifact.instructionPC 794 = 1352 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline7Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline7Template 794 inline7_slice
    (by
      change 794 + PairedSynthCoreTrace.inline7Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline7Template) (by decide))
    (by decide)

theorem inline7Site_startPC : inline7Site.startPC = UInt256.ofNat 1352 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 794) = UInt256.ofNat 1352
  rw [inline7_instructionPC]


theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 840).take PairedSynthCoreTrace.inline8Template.length = PairedSynthCoreTrace.inline8Template := by
  rfl

theorem inline8_instructionPC :
    Artifact.submissionArtifact.instructionPC 840 = 1405 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline8Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline8Template 840 inline8_slice
    (by
      change 840 + PairedSynthCoreTrace.inline8Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline8Template) (by decide))
    (by decide)

theorem inline8Site_startPC : inline8Site.startPC = UInt256.ofNat 1405 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 840) = UInt256.ofNat 1405
  rw [inline8_instructionPC]


theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 886).take PairedSynthCoreTrace.inline9Template.length = PairedSynthCoreTrace.inline9Template := by
  rfl

theorem inline9_instructionPC :
    Artifact.submissionArtifact.instructionPC 886 = 1458 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline9Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline9Template 886 inline9_slice
    (by
      change 886 + PairedSynthCoreTrace.inline9Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline9Template) (by decide))
    (by decide)

theorem inline9Site_startPC : inline9Site.startPC = UInt256.ofNat 1458 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 886) = UInt256.ofNat 1458
  rw [inline9_instructionPC]


theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 932).take PairedSynthCoreTrace.inline10Template.length = PairedSynthCoreTrace.inline10Template := by
  rfl

theorem inline10_instructionPC :
    Artifact.submissionArtifact.instructionPC 932 = 1511 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline10Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline10Template 932 inline10_slice
    (by
      change 932 + PairedSynthCoreTrace.inline10Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline10Template) (by decide))
    (by decide)

theorem inline10Site_startPC : inline10Site.startPC = UInt256.ofNat 1511 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 932) = UInt256.ofNat 1511
  rw [inline10_instructionPC]


theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 978).take PairedSynthCoreTrace.inline11Template.length = PairedSynthCoreTrace.inline11Template := by
  rfl

theorem inline11_instructionPC :
    Artifact.submissionArtifact.instructionPC 978 = 1564 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline11Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline11Template 978 inline11_slice
    (by
      change 978 + PairedSynthCoreTrace.inline11Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline11Template) (by decide))
    (by decide)

theorem inline11Site_startPC : inline11Site.startPC = UInt256.ofNat 1564 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 978) = UInt256.ofNat 1564
  rw [inline11_instructionPC]


theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1024).take PairedSynthCoreTrace.inline12Template.length = PairedSynthCoreTrace.inline12Template := by
  rfl

theorem inline12_instructionPC :
    Artifact.submissionArtifact.instructionPC 1024 = 1617 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline12Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline12Template 1024 inline12_slice
    (by
      change 1024 + PairedSynthCoreTrace.inline12Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline12Template) (by decide))
    (by decide)

theorem inline12Site_startPC : inline12Site.startPC = UInt256.ofNat 1617 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1024) = UInt256.ofNat 1617
  rw [inline12_instructionPC]


theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1071).take PairedSynthCoreTrace.inline13Template.length = PairedSynthCoreTrace.inline13Template := by
  rfl

theorem inline13_instructionPC :
    Artifact.submissionArtifact.instructionPC 1071 = 1670 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline13Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline13Template 1071 inline13_slice
    (by
      change 1071 + PairedSynthCoreTrace.inline13Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline13Template) (by decide))
    (by decide)

theorem inline13Site_startPC : inline13Site.startPC = UInt256.ofNat 1670 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1071) = UInt256.ofNat 1670
  rw [inline13_instructionPC]


theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1118).take PairedSynthCoreTrace.inline14Template.length = PairedSynthCoreTrace.inline14Template := by
  rfl

theorem inline14_instructionPC :
    Artifact.submissionArtifact.instructionPC 1118 = 1724 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline14Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline14Template 1118 inline14_slice
    (by
      change 1118 + PairedSynthCoreTrace.inline14Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline14Template) (by decide))
    (by decide)

theorem inline14Site_startPC : inline14Site.startPC = UInt256.ofNat 1724 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1118) = UInt256.ofNat 1724
  rw [inline14_instructionPC]


theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1165).take PairedSynthCoreTrace.inline15Template.length = PairedSynthCoreTrace.inline15Template := by
  rfl

theorem inline15_instructionPC :
    Artifact.submissionArtifact.instructionPC 1165 = 1778 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline15Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline15Template 1165 inline15_slice
    (by
      change 1165 + PairedSynthCoreTrace.inline15Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline15Template) (by decide))
    (by decide)

theorem inline15Site_startPC : inline15Site.startPC = UInt256.ofNat 1778 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1165) = UInt256.ofNat 1778
  rw [inline15_instructionPC]


theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1211).take PairedHelperBooleanTrace.group16Template.length = PairedHelperBooleanTrace.group16Template := by
  rfl

theorem group16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1211 = 1831 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.group16Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.group16Template 1211 group16_slice
    (by
      change 1211 + PairedHelperBooleanTrace.group16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.group16Template) (by decide))
    (by decide)

theorem group16Site_startPC : group16Site.startPC = UInt256.ofNat 1831 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1211) = UInt256.ofNat 1831
  rw [group16_instructionPC]


theorem call16_slice :
    (Artifact.submissionArtifact.instructions.drop 1214).take PairedSynthCoreTrace.call16Template.length = PairedSynthCoreTrace.call16Template := by
  rfl

theorem call16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1214 = 1854 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.call16Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.call16Template 1214 call16_slice
    (by
      change 1214 + PairedSynthCoreTrace.call16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.call16Template) (by decide))
    (by decide)

theorem call16Site_startPC : call16Site.startPC = UInt256.ofNat 1854 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1214) = UInt256.ofNat 1854
  rw [call16_instructionPC]


theorem return18_slice :
    (Artifact.submissionArtifact.instructions.drop 1238).take PairedHelperBooleanTrace.return18Template.length = PairedHelperBooleanTrace.return18Template := by
  rfl

theorem return18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1238 = 1894 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.return18Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.return18Template 1238 return18_slice
    (by
      change 1238 + PairedHelperBooleanTrace.return18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.return18Template) (by decide))
    (by decide)

theorem return18Site_startPC : return18Site.startPC = UInt256.ofNat 1894 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1238) = UInt256.ofNat 1894
  rw [return18_instructionPC]


theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1239).take PairedSynthCoreTrace.inline18Template.length = PairedSynthCoreTrace.inline18Template := by
  rfl

theorem inline18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1239 = 1895 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline18Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline18Template 1239 inline18_slice
    (by
      change 1239 + PairedSynthCoreTrace.inline18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline18Template) (by decide))
    (by decide)

theorem inline18Site_startPC : inline18Site.startPC = UInt256.ofNat 1895 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1239) = UInt256.ofNat 1895
  rw [inline18_instructionPC]


theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1287).take PairedSynthCoreTrace.inline19Template.length = PairedSynthCoreTrace.inline19Template := by
  rfl

theorem inline19_instructionPC :
    Artifact.submissionArtifact.instructionPC 1287 = 1950 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline19Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline19Template 1287 inline19_slice
    (by
      change 1287 + PairedSynthCoreTrace.inline19Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline19Template) (by decide))
    (by decide)

theorem inline19Site_startPC : inline19Site.startPC = UInt256.ofNat 1950 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1287) = UInt256.ofNat 1950
  rw [inline19_instructionPC]


theorem inline20_slice :
    (Artifact.submissionArtifact.instructions.drop 1335).take PairedSynthCoreTrace.inline20Template.length = PairedSynthCoreTrace.inline20Template := by
  rfl

theorem inline20_instructionPC :
    Artifact.submissionArtifact.instructionPC 1335 = 2004 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline20Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline20Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline20Template 1335 inline20_slice
    (by
      change 1335 + PairedSynthCoreTrace.inline20Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline20Template) (by decide))
    (by decide)

theorem inline20Site_startPC : inline20Site.startPC = UInt256.ofNat 2004 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1335) = UInt256.ofNat 2004
  rw [inline20_instructionPC]


theorem inline21_slice :
    (Artifact.submissionArtifact.instructions.drop 1384).take PairedSynthCoreTrace.inline21Template.length = PairedSynthCoreTrace.inline21Template := by
  rfl

theorem inline21_instructionPC :
    Artifact.submissionArtifact.instructionPC 1384 = 2059 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline21Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline21Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline21Template 1384 inline21_slice
    (by
      change 1384 + PairedSynthCoreTrace.inline21Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline21Template) (by decide))
    (by decide)

theorem inline21Site_startPC : inline21Site.startPC = UInt256.ofNat 2059 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1384) = UInt256.ofNat 2059
  rw [inline21_instructionPC]


theorem inline22_slice :
    (Artifact.submissionArtifact.instructions.drop 1432).take PairedSynthCoreTrace.inline22Template.length = PairedSynthCoreTrace.inline22Template := by
  rfl

theorem inline22_instructionPC :
    Artifact.submissionArtifact.instructionPC 1432 = 2114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline22Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline22Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline22Template 1432 inline22_slice
    (by
      change 1432 + PairedSynthCoreTrace.inline22Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline22Template) (by decide))
    (by decide)

theorem inline22Site_startPC : inline22Site.startPC = UInt256.ofNat 2114 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1432) = UInt256.ofNat 2114
  rw [inline22_instructionPC]


theorem inline23_slice :
    (Artifact.submissionArtifact.instructions.drop 1480).take PairedSynthCoreTrace.inline23Template.length = PairedSynthCoreTrace.inline23Template := by
  rfl

theorem inline23_instructionPC :
    Artifact.submissionArtifact.instructionPC 1480 = 2169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline23Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline23Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline23Template 1480 inline23_slice
    (by
      change 1480 + PairedSynthCoreTrace.inline23Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline23Template) (by decide))
    (by decide)

theorem inline23Site_startPC : inline23Site.startPC = UInt256.ofNat 2169 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1480) = UInt256.ofNat 2169
  rw [inline23_instructionPC]


theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1528).take PairedSynthCoreTrace.inline24Template.length = PairedSynthCoreTrace.inline24Template := by
  rfl

theorem inline24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1528 = 2224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline24Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline24Template 1528 inline24_slice
    (by
      change 1528 + PairedSynthCoreTrace.inline24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline24Template) (by decide))
    (by decide)

theorem inline24Site_startPC : inline24Site.startPC = UInt256.ofNat 2224 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1528) = UInt256.ofNat 2224
  rw [inline24_instructionPC]


theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1568).take PairedSynthCoreTrace.inline25Template.length = PairedSynthCoreTrace.inline25Template := by
  rfl

theorem inline25_instructionPC :
    Artifact.submissionArtifact.instructionPC 1568 = 2270 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline25Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline25Template 1568 inline25_slice
    (by
      change 1568 + PairedSynthCoreTrace.inline25Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline25Template) (by decide))
    (by decide)

theorem inline25Site_startPC : inline25Site.startPC = UInt256.ofNat 2270 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1568) = UInt256.ofNat 2270
  rw [inline25_instructionPC]


theorem inline26_slice :
    (Artifact.submissionArtifact.instructions.drop 1616).take PairedSynthCoreTrace.inline26Template.length = PairedSynthCoreTrace.inline26Template := by
  rfl

theorem inline26_instructionPC :
    Artifact.submissionArtifact.instructionPC 1616 = 2324 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline26Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline26Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline26Template 1616 inline26_slice
    (by
      change 1616 + PairedSynthCoreTrace.inline26Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline26Template) (by decide))
    (by decide)

theorem inline26Site_startPC : inline26Site.startPC = UInt256.ofNat 2324 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1616) = UInt256.ofNat 2324
  rw [inline26_instructionPC]


theorem inline27_slice :
    (Artifact.submissionArtifact.instructions.drop 1664).take PairedSynthCoreTrace.inline27Template.length = PairedSynthCoreTrace.inline27Template := by
  rfl

theorem inline27_instructionPC :
    Artifact.submissionArtifact.instructionPC 1664 = 2379 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline27Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline27Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline27Template 1664 inline27_slice
    (by
      change 1664 + PairedSynthCoreTrace.inline27Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline27Template) (by decide))
    (by decide)

theorem inline27Site_startPC : inline27Site.startPC = UInt256.ofNat 2379 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1664) = UInt256.ofNat 2379
  rw [inline27_instructionPC]


theorem call28_slice :
    (Artifact.submissionArtifact.instructions.drop 1712).take PairedSynthCoreTrace.call28Template.length = PairedSynthCoreTrace.call28Template := by
  rfl

theorem call28_instructionPC :
    Artifact.submissionArtifact.instructionPC 1712 = 2434 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call28Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.call28Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.call28Template 1712 call28_slice
    (by
      change 1712 + PairedSynthCoreTrace.call28Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.call28Template) (by decide))
    (by decide)

theorem call28Site_startPC : call28Site.startPC = UInt256.ofNat 2434 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1712) = UInt256.ofNat 2434
  rw [call28_instructionPC]


theorem return30_slice :
    (Artifact.submissionArtifact.instructions.drop 1733).take PairedHelperBooleanTrace.return30Template.length = PairedHelperBooleanTrace.return30Template := by
  rfl

theorem return30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1733 = 2471 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.return30Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.return30Template 1733 return30_slice
    (by
      change 1733 + PairedHelperBooleanTrace.return30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.return30Template) (by decide))
    (by decide)

theorem return30Site_startPC : return30Site.startPC = UInt256.ofNat 2471 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1733) = UInt256.ofNat 2471
  rw [return30_instructionPC]


theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1734).take PairedSynthCoreTrace.inline30Template.length = PairedSynthCoreTrace.inline30Template := by
  rfl

theorem inline30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1734 = 2472 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline30Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline30Template 1734 inline30_slice
    (by
      change 1734 + PairedSynthCoreTrace.inline30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline30Template) (by decide))
    (by decide)

theorem inline30Site_startPC : inline30Site.startPC = UInt256.ofNat 2472 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1734) = UInt256.ofNat 2472
  rw [inline30_instructionPC]


theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1773).take PairedSynthCoreTrace.inline31Template.length = PairedSynthCoreTrace.inline31Template := by
  rfl

theorem inline31_instructionPC :
    Artifact.submissionArtifact.instructionPC 1773 = 2516 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline31Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline31Template 1773 inline31_slice
    (by
      change 1773 + PairedSynthCoreTrace.inline31Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline31Template) (by decide))
    (by decide)

theorem inline31Site_startPC : inline31Site.startPC = UInt256.ofNat 2516 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1773) = UInt256.ofNat 2516
  rw [inline31_instructionPC]


theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1821).take PairedSynthCoreTrace.group32Template.length = PairedSynthCoreTrace.group32Template := by
  rfl

theorem group32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1821 = 2571 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.group32Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.group32Template 1821 group32_slice
    (by
      change 1821 + PairedSynthCoreTrace.group32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.group32Template) (by decide))
    (by decide)

theorem group32Site_startPC : group32Site.startPC = UInt256.ofNat 2571 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1821) = UInt256.ofNat 2571
  rw [group32_instructionPC]


theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1824).take PairedSynthCoreTrace.inline32Template.length = PairedSynthCoreTrace.inline32Template := by
  rfl

theorem inline32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1824 = 2595 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline32Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline32Template 1824 inline32_slice
    (by
      change 1824 + PairedSynthCoreTrace.inline32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline32Template) (by decide))
    (by decide)

theorem inline32Site_startPC : inline32Site.startPC = UInt256.ofNat 2595 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1824) = UInt256.ofNat 2595
  rw [inline32_instructionPC]


theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 1865).take PairedSynthCoreTrace.inline33Template.length = PairedSynthCoreTrace.inline33Template := by
  rfl

theorem inline33_instructionPC :
    Artifact.submissionArtifact.instructionPC 1865 = 2643 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline33Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline33Template 1865 inline33_slice
    (by
      change 1865 + PairedSynthCoreTrace.inline33Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline33Template) (by decide))
    (by decide)

theorem inline33Site_startPC : inline33Site.startPC = UInt256.ofNat 2643 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1865) = UInt256.ofNat 2643
  rw [inline33_instructionPC]


theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 1906).take PairedSynthCoreTrace.inline34Template.length = PairedSynthCoreTrace.inline34Template := by
  rfl

theorem inline34_instructionPC :
    Artifact.submissionArtifact.instructionPC 1906 = 2691 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline34Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline34Template 1906 inline34_slice
    (by
      change 1906 + PairedSynthCoreTrace.inline34Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline34Template) (by decide))
    (by decide)

theorem inline34Site_startPC : inline34Site.startPC = UInt256.ofNat 2691 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1906) = UInt256.ofNat 2691
  rw [inline34_instructionPC]


theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 1948).take PairedSynthCoreTrace.inline35Template.length = PairedSynthCoreTrace.inline35Template := by
  rfl

theorem inline35_instructionPC :
    Artifact.submissionArtifact.instructionPC 1948 = 2739 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline35Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline35Template 1948 inline35_slice
    (by
      change 1948 + PairedSynthCoreTrace.inline35Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline35Template) (by decide))
    (by decide)

theorem inline35Site_startPC : inline35Site.startPC = UInt256.ofNat 2739 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1948) = UInt256.ofNat 2739
  rw [inline35_instructionPC]


theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 1990).take PairedSynthCoreTrace.inline36Template.length = PairedSynthCoreTrace.inline36Template := by
  rfl

theorem inline36_instructionPC :
    Artifact.submissionArtifact.instructionPC 1990 = 2788 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline36Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline36Template 1990 inline36_slice
    (by
      change 1990 + PairedSynthCoreTrace.inline36Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline36Template) (by decide))
    (by decide)

theorem inline36Site_startPC : inline36Site.startPC = UInt256.ofNat 2788 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1990) = UInt256.ofNat 2788
  rw [inline36_instructionPC]


theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 2031).take PairedSynthCoreTrace.inline37Template.length = PairedSynthCoreTrace.inline37Template := by
  rfl

theorem inline37_instructionPC :
    Artifact.submissionArtifact.instructionPC 2031 = 2836 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline37Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline37Template 2031 inline37_slice
    (by
      change 2031 + PairedSynthCoreTrace.inline37Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline37Template) (by decide))
    (by decide)

theorem inline37Site_startPC : inline37Site.startPC = UInt256.ofNat 2836 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2031) = UInt256.ofNat 2836
  rw [inline37_instructionPC]


theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 2072).take PairedSynthCoreTrace.inline38Template.length = PairedSynthCoreTrace.inline38Template := by
  rfl

theorem inline38_instructionPC :
    Artifact.submissionArtifact.instructionPC 2072 = 2884 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline38Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline38Template 2072 inline38_slice
    (by
      change 2072 + PairedSynthCoreTrace.inline38Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline38Template) (by decide))
    (by decide)

theorem inline38Site_startPC : inline38Site.startPC = UInt256.ofNat 2884 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2072) = UInt256.ofNat 2884
  rw [inline38_instructionPC]


theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 2113).take PairedSynthCoreTrace.inline39Template.length = PairedSynthCoreTrace.inline39Template := by
  rfl

theorem inline39_instructionPC :
    Artifact.submissionArtifact.instructionPC 2113 = 2932 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline39Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline39Template 2113 inline39_slice
    (by
      change 2113 + PairedSynthCoreTrace.inline39Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline39Template) (by decide))
    (by decide)

theorem inline39Site_startPC : inline39Site.startPC = UInt256.ofNat 2932 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2113) = UInt256.ofNat 2932
  rw [inline39_instructionPC]


theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 2154).take PairedSynthCoreTrace.inline40Template.length = PairedSynthCoreTrace.inline40Template := by
  rfl

theorem inline40_instructionPC :
    Artifact.submissionArtifact.instructionPC 2154 = 2979 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline40Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline40Template 2154 inline40_slice
    (by
      change 2154 + PairedSynthCoreTrace.inline40Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline40Template) (by decide))
    (by decide)

theorem inline40Site_startPC : inline40Site.startPC = UInt256.ofNat 2979 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2154) = UInt256.ofNat 2979
  rw [inline40_instructionPC]


theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2195).take PairedSynthCoreTrace.inline41Template.length = PairedSynthCoreTrace.inline41Template := by
  rfl

theorem inline41_instructionPC :
    Artifact.submissionArtifact.instructionPC 2195 = 3027 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline41Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline41Template 2195 inline41_slice
    (by
      change 2195 + PairedSynthCoreTrace.inline41Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline41Template) (by decide))
    (by decide)

theorem inline41Site_startPC : inline41Site.startPC = UInt256.ofNat 3027 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2195) = UInt256.ofNat 3027
  rw [inline41_instructionPC]


theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2237).take PairedSynthCoreTrace.inline42Template.length = PairedSynthCoreTrace.inline42Template := by
  rfl

theorem inline42_instructionPC :
    Artifact.submissionArtifact.instructionPC 2237 = 3076 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline42Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline42Template 2237 inline42_slice
    (by
      change 2237 + PairedSynthCoreTrace.inline42Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline42Template) (by decide))
    (by decide)

theorem inline42Site_startPC : inline42Site.startPC = UInt256.ofNat 3076 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2237) = UInt256.ofNat 3076
  rw [inline42_instructionPC]


theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2278).take PairedSynthCoreTrace.inline43Template.length = PairedSynthCoreTrace.inline43Template := by
  rfl

theorem inline43_instructionPC :
    Artifact.submissionArtifact.instructionPC 2278 = 3123 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline43Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline43Template 2278 inline43_slice
    (by
      change 2278 + PairedSynthCoreTrace.inline43Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline43Template) (by decide))
    (by decide)

theorem inline43Site_startPC : inline43Site.startPC = UInt256.ofNat 3123 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2278) = UInt256.ofNat 3123
  rw [inline43_instructionPC]


theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2320).take PairedSynthCoreTrace.inline44Template.length = PairedSynthCoreTrace.inline44Template := by
  rfl

theorem inline44_instructionPC :
    Artifact.submissionArtifact.instructionPC 2320 = 3172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline44Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline44Template 2320 inline44_slice
    (by
      change 2320 + PairedSynthCoreTrace.inline44Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline44Template) (by decide))
    (by decide)

theorem inline44Site_startPC : inline44Site.startPC = UInt256.ofNat 3172 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2320) = UInt256.ofNat 3172
  rw [inline44_instructionPC]


theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2362).take PairedSynthCoreTrace.inline45Template.length = PairedSynthCoreTrace.inline45Template := by
  rfl

theorem inline45_instructionPC :
    Artifact.submissionArtifact.instructionPC 2362 = 3221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline45Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline45Template 2362 inline45_slice
    (by
      change 2362 + PairedSynthCoreTrace.inline45Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline45Template) (by decide))
    (by decide)

theorem inline45Site_startPC : inline45Site.startPC = UInt256.ofNat 3221 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2362) = UInt256.ofNat 3221
  rw [inline45_instructionPC]


theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2404).take PairedSynthCoreTrace.inline46Template.length = PairedSynthCoreTrace.inline46Template := by
  rfl

theorem inline46_instructionPC :
    Artifact.submissionArtifact.instructionPC 2404 = 3269 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline46Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline46Template 2404 inline46_slice
    (by
      change 2404 + PairedSynthCoreTrace.inline46Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline46Template) (by decide))
    (by decide)

theorem inline46Site_startPC : inline46Site.startPC = UInt256.ofNat 3269 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2404) = UInt256.ofNat 3269
  rw [inline46_instructionPC]


theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2437).take PairedSynthCoreTrace.inline47Template.length = PairedSynthCoreTrace.inline47Template := by
  rfl

theorem inline47_instructionPC :
    Artifact.submissionArtifact.instructionPC 2437 = 3308 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline47Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline47Template 2437 inline47_slice
    (by
      change 2437 + PairedSynthCoreTrace.inline47Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline47Template) (by decide))
    (by decide)

theorem inline47Site_startPC : inline47Site.startPC = UInt256.ofNat 3308 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2437) = UInt256.ofNat 3308
  rw [inline47_instructionPC]


theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2470).take PairedHelperBooleanTrace.group48Template.length = PairedHelperBooleanTrace.group48Template := by
  rfl

theorem group48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2470 = 3347 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.group48Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.group48Template 2470 group48_slice
    (by
      change 2470 + PairedHelperBooleanTrace.group48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.group48Template) (by decide))
    (by decide)

theorem group48Site_startPC : group48Site.startPC = UInt256.ofNat 3347 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2470) = UInt256.ofNat 3347
  rw [group48_instructionPC]


theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2473).take PairedSynthCoreTrace.inline48Template.length = PairedSynthCoreTrace.inline48Template := by
  rfl

theorem inline48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2473 = 3370 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline48Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline48Template 2473 inline48_slice
    (by
      change 2473 + PairedSynthCoreTrace.inline48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline48Template) (by decide))
    (by decide)

theorem inline48Site_startPC : inline48Site.startPC = UInt256.ofNat 3370 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2473) = UInt256.ofNat 3370
  rw [inline48_instructionPC]


theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2522).take PairedSynthCoreTrace.inline49Template.length = PairedSynthCoreTrace.inline49Template := by
  rfl

theorem inline49_instructionPC :
    Artifact.submissionArtifact.instructionPC 2522 = 3425 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline49Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline49Template 2522 inline49_slice
    (by
      change 2522 + PairedSynthCoreTrace.inline49Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline49Template) (by decide))
    (by decide)

theorem inline49Site_startPC : inline49Site.startPC = UInt256.ofNat 3425 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2522) = UInt256.ofNat 3425
  rw [inline49_instructionPC]


theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2570).take PairedSynthCoreTrace.inline50Template.length = PairedSynthCoreTrace.inline50Template := by
  rfl

theorem inline50_instructionPC :
    Artifact.submissionArtifact.instructionPC 2570 = 3480 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline50Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline50Template 2570 inline50_slice
    (by
      change 2570 + PairedSynthCoreTrace.inline50Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline50Template) (by decide))
    (by decide)

theorem inline50Site_startPC : inline50Site.startPC = UInt256.ofNat 3480 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2570) = UInt256.ofNat 3480
  rw [inline50_instructionPC]


theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2618).take PairedSynthCoreTrace.inline51Template.length = PairedSynthCoreTrace.inline51Template := by
  rfl

theorem inline51_instructionPC :
    Artifact.submissionArtifact.instructionPC 2618 = 3535 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline51Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline51Template 2618 inline51_slice
    (by
      change 2618 + PairedSynthCoreTrace.inline51Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline51Template) (by decide))
    (by decide)

theorem inline51Site_startPC : inline51Site.startPC = UInt256.ofNat 3535 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2618) = UInt256.ofNat 3535
  rw [inline51_instructionPC]


theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2666).take PairedSynthCoreTrace.inline52Template.length = PairedSynthCoreTrace.inline52Template := by
  rfl

theorem inline52_instructionPC :
    Artifact.submissionArtifact.instructionPC 2666 = 3589 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline52Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline52Template 2666 inline52_slice
    (by
      change 2666 + PairedSynthCoreTrace.inline52Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline52Template) (by decide))
    (by decide)

theorem inline52Site_startPC : inline52Site.startPC = UInt256.ofNat 3589 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2666) = UInt256.ofNat 3589
  rw [inline52_instructionPC]


theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2706).take PairedSynthCoreTrace.inline53Template.length = PairedSynthCoreTrace.inline53Template := by
  rfl

theorem inline53_instructionPC :
    Artifact.submissionArtifact.instructionPC 2706 = 3634 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline53Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline53Template 2706 inline53_slice
    (by
      change 2706 + PairedSynthCoreTrace.inline53Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline53Template) (by decide))
    (by decide)

theorem inline53Site_startPC : inline53Site.startPC = UInt256.ofNat 3634 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2706) = UInt256.ofNat 3634
  rw [inline53_instructionPC]


theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2754).take PairedSynthCoreTrace.inline54Template.length = PairedSynthCoreTrace.inline54Template := by
  rfl

theorem inline54_instructionPC :
    Artifact.submissionArtifact.instructionPC 2754 = 3689 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline54Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline54Template 2754 inline54_slice
    (by
      change 2754 + PairedSynthCoreTrace.inline54Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline54Template) (by decide))
    (by decide)

theorem inline54Site_startPC : inline54Site.startPC = UInt256.ofNat 3689 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2754) = UInt256.ofNat 3689
  rw [inline54_instructionPC]


theorem inline55_slice :
    (Artifact.submissionArtifact.instructions.drop 2802).take PairedSynthCoreTrace.inline55Template.length = PairedSynthCoreTrace.inline55Template := by
  rfl

theorem inline55_instructionPC :
    Artifact.submissionArtifact.instructionPC 2802 = 3744 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline55Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline55Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline55Template 2802 inline55_slice
    (by
      change 2802 + PairedSynthCoreTrace.inline55Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline55Template) (by decide))
    (by decide)

theorem inline55Site_startPC : inline55Site.startPC = UInt256.ofNat 3744 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2802) = UInt256.ofNat 3744
  rw [inline55_instructionPC]


theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 2851).take PairedSynthCoreTrace.inline56Template.length = PairedSynthCoreTrace.inline56Template := by
  rfl

theorem inline56_instructionPC :
    Artifact.submissionArtifact.instructionPC 2851 = 3799 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline56Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline56Template 2851 inline56_slice
    (by
      change 2851 + PairedSynthCoreTrace.inline56Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline56Template) (by decide))
    (by decide)

theorem inline56Site_startPC : inline56Site.startPC = UInt256.ofNat 3799 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2851) = UInt256.ofNat 3799
  rw [inline56_instructionPC]


theorem inline57_slice :
    (Artifact.submissionArtifact.instructions.drop 2899).take PairedSynthCoreTrace.inline57Template.length = PairedSynthCoreTrace.inline57Template := by
  rfl

theorem inline57_instructionPC :
    Artifact.submissionArtifact.instructionPC 2899 = 3854 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline57Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline57Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline57Template 2899 inline57_slice
    (by
      change 2899 + PairedSynthCoreTrace.inline57Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline57Template) (by decide))
    (by decide)

theorem inline57Site_startPC : inline57Site.startPC = UInt256.ofNat 3854 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2899) = UInt256.ofNat 3854
  rw [inline57_instructionPC]


theorem inline58_slice :
    (Artifact.submissionArtifact.instructions.drop 2947).take PairedSynthCoreTrace.inline58Template.length = PairedSynthCoreTrace.inline58Template := by
  rfl

theorem inline58_instructionPC :
    Artifact.submissionArtifact.instructionPC 2947 = 3909 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline58Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline58Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline58Template 2947 inline58_slice
    (by
      change 2947 + PairedSynthCoreTrace.inline58Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline58Template) (by decide))
    (by decide)

theorem inline58Site_startPC : inline58Site.startPC = UInt256.ofNat 3909 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2947) = UInt256.ofNat 3909
  rw [inline58_instructionPC]


theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 2996).take PairedSynthCoreTrace.inline59Template.length = PairedSynthCoreTrace.inline59Template := by
  rfl

theorem inline59_instructionPC :
    Artifact.submissionArtifact.instructionPC 2996 = 3965 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline59Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline59Template 2996 inline59_slice
    (by
      change 2996 + PairedSynthCoreTrace.inline59Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline59Template) (by decide))
    (by decide)

theorem inline59Site_startPC : inline59Site.startPC = UInt256.ofNat 3965 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2996) = UInt256.ofNat 3965
  rw [inline59_instructionPC]


theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 3045).take PairedSynthCoreTrace.inline60Template.length = PairedSynthCoreTrace.inline60Template := by
  rfl

theorem inline60_instructionPC :
    Artifact.submissionArtifact.instructionPC 3045 = 4021 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline60Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline60Template 3045 inline60_slice
    (by
      change 3045 + PairedSynthCoreTrace.inline60Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline60Template) (by decide))
    (by decide)

theorem inline60Site_startPC : inline60Site.startPC = UInt256.ofNat 4021 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3045) = UInt256.ofNat 4021
  rw [inline60_instructionPC]


theorem inline61_slice :
    (Artifact.submissionArtifact.instructions.drop 3094).take PairedSynthCoreTrace.inline61Template.length = PairedSynthCoreTrace.inline61Template := by
  rfl

theorem inline61_instructionPC :
    Artifact.submissionArtifact.instructionPC 3094 = 4077 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline61Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline61Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline61Template 3094 inline61_slice
    (by
      change 3094 + PairedSynthCoreTrace.inline61Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline61Template) (by decide))
    (by decide)

theorem inline61Site_startPC : inline61Site.startPC = UInt256.ofNat 4077 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3094) = UInt256.ofNat 4077
  rw [inline61_instructionPC]


theorem inline62_slice :
    (Artifact.submissionArtifact.instructions.drop 3142).take PairedSynthCoreTrace.inline62Template.length = PairedSynthCoreTrace.inline62Template := by
  rfl

theorem inline62_instructionPC :
    Artifact.submissionArtifact.instructionPC 3142 = 4132 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline62Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline62Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline62Template 3142 inline62_slice
    (by
      change 3142 + PairedSynthCoreTrace.inline62Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline62Template) (by decide))
    (by decide)

theorem inline62Site_startPC : inline62Site.startPC = UInt256.ofNat 4132 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3142) = UInt256.ofNat 4132
  rw [inline62_instructionPC]


theorem inline63_slice :
    (Artifact.submissionArtifact.instructions.drop 3191).take PairedSynthCoreTrace.inline63Template.length = PairedSynthCoreTrace.inline63Template := by
  rfl

theorem inline63_instructionPC :
    Artifact.submissionArtifact.instructionPC 3191 = 4188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline63Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline63Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline63Template 3191 inline63_slice
    (by
      change 3191 + PairedSynthCoreTrace.inline63Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline63Template) (by decide))
    (by decide)

theorem inline63Site_startPC : inline63Site.startPC = UInt256.ofNat 4188 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3191) = UInt256.ofNat 4188
  rw [inline63_instructionPC]


theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3239).take PairedHelperBooleanTrace.group64Template.length = PairedHelperBooleanTrace.group64Template := by
  rfl

theorem group64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3239 = 4243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.group64Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.group64Template 3239 group64_slice
    (by
      change 3239 + PairedHelperBooleanTrace.group64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.group64Template) (by decide))
    (by decide)

theorem group64Site_startPC : group64Site.startPC = UInt256.ofNat 4243 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3239) = UInt256.ofNat 4243
  rw [group64_instructionPC]


theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3242).take PairedSynthCoreTrace.inline64Template.length = PairedSynthCoreTrace.inline64Template := by
  rfl

theorem inline64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3242 = 4250 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline64Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline64Template 3242 inline64_slice
    (by
      change 3242 + PairedSynthCoreTrace.inline64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline64Template) (by decide))
    (by decide)

theorem inline64Site_startPC : inline64Site.startPC = UInt256.ofNat 4250 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3242) = UInt256.ofNat 4250
  rw [inline64_instructionPC]


theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3288).take PairedSynthCoreTrace.inline65Template.length = PairedSynthCoreTrace.inline65Template := by
  rfl

theorem inline65_instructionPC :
    Artifact.submissionArtifact.instructionPC 3288 = 4303 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline65Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline65Template 3288 inline65_slice
    (by
      change 3288 + PairedSynthCoreTrace.inline65Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline65Template) (by decide))
    (by decide)

theorem inline65Site_startPC : inline65Site.startPC = UInt256.ofNat 4303 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3288) = UInt256.ofNat 4303
  rw [inline65_instructionPC]


theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3334).take PairedSynthCoreTrace.inline66Template.length = PairedSynthCoreTrace.inline66Template := by
  rfl

theorem inline66_instructionPC :
    Artifact.submissionArtifact.instructionPC 3334 = 4355 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline66Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline66Template 3334 inline66_slice
    (by
      change 3334 + PairedSynthCoreTrace.inline66Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline66Template) (by decide))
    (by decide)

theorem inline66Site_startPC : inline66Site.startPC = UInt256.ofNat 4355 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3334) = UInt256.ofNat 4355
  rw [inline66_instructionPC]


theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3381).take PairedSynthCoreTrace.inline67Template.length = PairedSynthCoreTrace.inline67Template := by
  rfl

theorem inline67_instructionPC :
    Artifact.submissionArtifact.instructionPC 3381 = 4409 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline67Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline67Template 3381 inline67_slice
    (by
      change 3381 + PairedSynthCoreTrace.inline67Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline67Template) (by decide))
    (by decide)

theorem inline67Site_startPC : inline67Site.startPC = UInt256.ofNat 4409 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3381) = UInt256.ofNat 4409
  rw [inline67_instructionPC]


theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3427).take PairedSynthCoreTrace.inline68Template.length = PairedSynthCoreTrace.inline68Template := by
  rfl

theorem inline68_instructionPC :
    Artifact.submissionArtifact.instructionPC 3427 = 4462 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline68Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline68Template 3427 inline68_slice
    (by
      change 3427 + PairedSynthCoreTrace.inline68Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline68Template) (by decide))
    (by decide)

theorem inline68Site_startPC : inline68Site.startPC = UInt256.ofNat 4462 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3427) = UInt256.ofNat 4462
  rw [inline68_instructionPC]


theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3474).take PairedSynthCoreTrace.inline69Template.length = PairedSynthCoreTrace.inline69Template := by
  rfl

theorem inline69_instructionPC :
    Artifact.submissionArtifact.instructionPC 3474 = 4515 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline69Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline69Template 3474 inline69_slice
    (by
      change 3474 + PairedSynthCoreTrace.inline69Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline69Template) (by decide))
    (by decide)

theorem inline69Site_startPC : inline69Site.startPC = UInt256.ofNat 4515 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3474) = UInt256.ofNat 4515
  rw [inline69_instructionPC]


theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3520).take PairedSynthCoreTrace.inline70Template.length = PairedSynthCoreTrace.inline70Template := by
  rfl

theorem inline70_instructionPC :
    Artifact.submissionArtifact.instructionPC 3520 = 4568 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline70Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline70Template 3520 inline70_slice
    (by
      change 3520 + PairedSynthCoreTrace.inline70Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline70Template) (by decide))
    (by decide)

theorem inline70Site_startPC : inline70Site.startPC = UInt256.ofNat 4568 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3520) = UInt256.ofNat 4568
  rw [inline70_instructionPC]


theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3567).take PairedSynthCoreTrace.inline71Template.length = PairedSynthCoreTrace.inline71Template := by
  rfl

theorem inline71_instructionPC :
    Artifact.submissionArtifact.instructionPC 3567 = 4622 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline71Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline71Template 3567 inline71_slice
    (by
      change 3567 + PairedSynthCoreTrace.inline71Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline71Template) (by decide))
    (by decide)

theorem inline71Site_startPC : inline71Site.startPC = UInt256.ofNat 4622 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3567) = UInt256.ofNat 4622
  rw [inline71_instructionPC]


theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3613).take PairedSynthCoreTrace.inline72Template.length = PairedSynthCoreTrace.inline72Template := by
  rfl

theorem inline72_instructionPC :
    Artifact.submissionArtifact.instructionPC 3613 = 4675 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline72Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline72Template 3613 inline72_slice
    (by
      change 3613 + PairedSynthCoreTrace.inline72Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline72Template) (by decide))
    (by decide)

theorem inline72Site_startPC : inline72Site.startPC = UInt256.ofNat 4675 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3613) = UInt256.ofNat 4675
  rw [inline72_instructionPC]


theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3660).take PairedSynthCoreTrace.inline73Template.length = PairedSynthCoreTrace.inline73Template := by
  rfl

theorem inline73_instructionPC :
    Artifact.submissionArtifact.instructionPC 3660 = 4729 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline73Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline73Template 3660 inline73_slice
    (by
      change 3660 + PairedSynthCoreTrace.inline73Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline73Template) (by decide))
    (by decide)

theorem inline73Site_startPC : inline73Site.startPC = UInt256.ofNat 4729 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3660) = UInt256.ofNat 4729
  rw [inline73_instructionPC]


theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3707).take PairedSynthCoreTrace.inline74Template.length = PairedSynthCoreTrace.inline74Template := by
  rfl

theorem inline74_instructionPC :
    Artifact.submissionArtifact.instructionPC 3707 = 4782 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline74Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline74Template 3707 inline74_slice
    (by
      change 3707 + PairedSynthCoreTrace.inline74Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline74Template) (by decide))
    (by decide)

theorem inline74Site_startPC : inline74Site.startPC = UInt256.ofNat 4782 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3707) = UInt256.ofNat 4782
  rw [inline74_instructionPC]


theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3753).take PairedSynthCoreTrace.inline75Template.length = PairedSynthCoreTrace.inline75Template := by
  rfl

theorem inline75_instructionPC :
    Artifact.submissionArtifact.instructionPC 3753 = 4835 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline75Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline75Template 3753 inline75_slice
    (by
      change 3753 + PairedSynthCoreTrace.inline75Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline75Template) (by decide))
    (by decide)

theorem inline75Site_startPC : inline75Site.startPC = UInt256.ofNat 4835 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3753) = UInt256.ofNat 4835
  rw [inline75_instructionPC]


theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3799).take PairedSynthCoreTrace.inline76Template.length = PairedSynthCoreTrace.inline76Template := by
  rfl

theorem inline76_instructionPC :
    Artifact.submissionArtifact.instructionPC 3799 = 4888 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline76Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline76Template 3799 inline76_slice
    (by
      change 3799 + PairedSynthCoreTrace.inline76Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline76Template) (by decide))
    (by decide)

theorem inline76Site_startPC : inline76Site.startPC = UInt256.ofNat 4888 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3799) = UInt256.ofNat 4888
  rw [inline76_instructionPC]


theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 3846).take PairedSynthCoreTrace.inline77Template.length = PairedSynthCoreTrace.inline77Template := by
  rfl

theorem inline77_instructionPC :
    Artifact.submissionArtifact.instructionPC 3846 = 4941 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline77Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline77Template 3846 inline77_slice
    (by
      change 3846 + PairedSynthCoreTrace.inline77Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline77Template) (by decide))
    (by decide)

theorem inline77Site_startPC : inline77Site.startPC = UInt256.ofNat 4941 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3846) = UInt256.ofNat 4941
  rw [inline77_instructionPC]


theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3893).take PairedSynthCoreTrace.inline78Template.length = PairedSynthCoreTrace.inline78Template := by
  rfl

theorem inline78_instructionPC :
    Artifact.submissionArtifact.instructionPC 3893 = 4995 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline78Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline78Template 3893 inline78_slice
    (by
      change 3893 + PairedSynthCoreTrace.inline78Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline78Template) (by decide))
    (by decide)

theorem inline78Site_startPC : inline78Site.startPC = UInt256.ofNat 4995 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3893) = UInt256.ofNat 4995
  rw [inline78_instructionPC]


theorem inline79_slice :
    (Artifact.submissionArtifact.instructions.drop 3940).take PairedSynthCoreTrace.inline79Template.length = PairedSynthCoreTrace.inline79Template := by
  rfl

theorem inline79_instructionPC :
    Artifact.submissionArtifact.instructionPC 3940 = 5049 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline79Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline79Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline79Template 3940 inline79_slice
    (by
      change 3940 + PairedSynthCoreTrace.inline79Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline79Template) (by decide))
    (by decide)

theorem inline79Site_startPC : inline79Site.startPC = UInt256.ofNat 5049 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3940) = UInt256.ofNat 5049
  rw [inline79_instructionPC]


theorem coreExit_slice :
    (Artifact.submissionArtifact.instructions.drop 3987).take PairedHelperBooleanTrace.coreExitTemplate.length = PairedHelperBooleanTrace.coreExitTemplate := by
  rfl

theorem coreExit_instructionPC :
    Artifact.submissionArtifact.instructionPC 3987 = 5103 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def coreExitSite : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.coreExitTemplate :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.coreExitTemplate 3987 coreExit_slice
    (by
      change 3987 + PairedHelperBooleanTrace.coreExitTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.coreExitTemplate) (by decide))
    (by decide)

theorem coreExitSite_startPC : coreExitSite.startPC = UInt256.ofNat 5103 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3987) = UInt256.ofNat 5103
  rw [coreExit_instructionPC]


theorem helper_slice :
    (Artifact.submissionArtifact.instructions.drop 4059).take PairedSynthCoreTrace.fullTemplate.length = PairedSynthCoreTrace.fullTemplate := by
  rfl

theorem helper_instructionPC :
    Artifact.submissionArtifact.instructionPC 4059 = 5190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def helperSite : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.fullTemplate :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.fullTemplate 4059 helper_slice
    (by
      change 4059 + PairedSynthCoreTrace.fullTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.fullTemplate) (by decide))
    (by decide)

theorem helperSite_startPC : helperSite.startPC = UInt256.ofNat 5190 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4059) = UInt256.ofNat 5190
  rw [helper_instructionPC]


def wholeSites : PairedSynthCoreTrace.WholeCoreSites Artifact.submissionArtifact .Osaka where
  group0 := ⟨group0Site, group0Site_startPC⟩
  inline0 := ⟨inline0Site, inline0Site_startPC⟩
  inline1 := ⟨inline1Site, inline1Site_startPC⟩
  inline2 := ⟨inline2Site, inline2Site_startPC⟩
  inline3 := ⟨inline3Site, inline3Site_startPC⟩
  inline4 := ⟨inline4Site, inline4Site_startPC⟩
  inline5 := ⟨inline5Site, inline5Site_startPC⟩
  inline6 := ⟨inline6Site, inline6Site_startPC⟩
  inline7 := ⟨inline7Site, inline7Site_startPC⟩
  inline8 := ⟨inline8Site, inline8Site_startPC⟩
  inline9 := ⟨inline9Site, inline9Site_startPC⟩
  inline10 := ⟨inline10Site, inline10Site_startPC⟩
  inline11 := ⟨inline11Site, inline11Site_startPC⟩
  inline12 := ⟨inline12Site, inline12Site_startPC⟩
  inline13 := ⟨inline13Site, inline13Site_startPC⟩
  inline14 := ⟨inline14Site, inline14Site_startPC⟩
  inline15 := ⟨inline15Site, inline15Site_startPC⟩
  group16 := ⟨group16Site, group16Site_startPC⟩
  call16 := ⟨call16Site, call16Site_startPC⟩
  return18 := ⟨return18Site, return18Site_startPC⟩
  inline18 := ⟨inline18Site, inline18Site_startPC⟩
  inline19 := ⟨inline19Site, inline19Site_startPC⟩
  inline20 := ⟨inline20Site, inline20Site_startPC⟩
  inline21 := ⟨inline21Site, inline21Site_startPC⟩
  inline22 := ⟨inline22Site, inline22Site_startPC⟩
  inline23 := ⟨inline23Site, inline23Site_startPC⟩
  inline24 := ⟨inline24Site, inline24Site_startPC⟩
  inline25 := ⟨inline25Site, inline25Site_startPC⟩
  inline26 := ⟨inline26Site, inline26Site_startPC⟩
  inline27 := ⟨inline27Site, inline27Site_startPC⟩
  call28 := ⟨call28Site, call28Site_startPC⟩
  return30 := ⟨return30Site, return30Site_startPC⟩
  inline30 := ⟨inline30Site, inline30Site_startPC⟩
  inline31 := ⟨inline31Site, inline31Site_startPC⟩
  group32 := ⟨group32Site, group32Site_startPC⟩
  inline32 := ⟨inline32Site, inline32Site_startPC⟩
  inline33 := ⟨inline33Site, inline33Site_startPC⟩
  inline34 := ⟨inline34Site, inline34Site_startPC⟩
  inline35 := ⟨inline35Site, inline35Site_startPC⟩
  inline36 := ⟨inline36Site, inline36Site_startPC⟩
  inline37 := ⟨inline37Site, inline37Site_startPC⟩
  inline38 := ⟨inline38Site, inline38Site_startPC⟩
  inline39 := ⟨inline39Site, inline39Site_startPC⟩
  inline40 := ⟨inline40Site, inline40Site_startPC⟩
  inline41 := ⟨inline41Site, inline41Site_startPC⟩
  inline42 := ⟨inline42Site, inline42Site_startPC⟩
  inline43 := ⟨inline43Site, inline43Site_startPC⟩
  inline44 := ⟨inline44Site, inline44Site_startPC⟩
  inline45 := ⟨inline45Site, inline45Site_startPC⟩
  inline46 := ⟨inline46Site, inline46Site_startPC⟩
  inline47 := ⟨inline47Site, inline47Site_startPC⟩
  group48 := ⟨group48Site, group48Site_startPC⟩
  inline48 := ⟨inline48Site, inline48Site_startPC⟩
  inline49 := ⟨inline49Site, inline49Site_startPC⟩
  inline50 := ⟨inline50Site, inline50Site_startPC⟩
  inline51 := ⟨inline51Site, inline51Site_startPC⟩
  inline52 := ⟨inline52Site, inline52Site_startPC⟩
  inline53 := ⟨inline53Site, inline53Site_startPC⟩
  inline54 := ⟨inline54Site, inline54Site_startPC⟩
  inline55 := ⟨inline55Site, inline55Site_startPC⟩
  inline56 := ⟨inline56Site, inline56Site_startPC⟩
  inline57 := ⟨inline57Site, inline57Site_startPC⟩
  inline58 := ⟨inline58Site, inline58Site_startPC⟩
  inline59 := ⟨inline59Site, inline59Site_startPC⟩
  inline60 := ⟨inline60Site, inline60Site_startPC⟩
  inline61 := ⟨inline61Site, inline61Site_startPC⟩
  inline62 := ⟨inline62Site, inline62Site_startPC⟩
  inline63 := ⟨inline63Site, inline63Site_startPC⟩
  group64 := ⟨group64Site, group64Site_startPC⟩
  inline64 := ⟨inline64Site, inline64Site_startPC⟩
  inline65 := ⟨inline65Site, inline65Site_startPC⟩
  inline66 := ⟨inline66Site, inline66Site_startPC⟩
  inline67 := ⟨inline67Site, inline67Site_startPC⟩
  inline68 := ⟨inline68Site, inline68Site_startPC⟩
  inline69 := ⟨inline69Site, inline69Site_startPC⟩
  inline70 := ⟨inline70Site, inline70Site_startPC⟩
  inline71 := ⟨inline71Site, inline71Site_startPC⟩
  inline72 := ⟨inline72Site, inline72Site_startPC⟩
  inline73 := ⟨inline73Site, inline73Site_startPC⟩
  inline74 := ⟨inline74Site, inline74Site_startPC⟩
  inline75 := ⟨inline75Site, inline75Site_startPC⟩
  inline76 := ⟨inline76Site, inline76Site_startPC⟩
  inline77 := ⟨inline77Site, inline77Site_startPC⟩
  inline78 := ⟨inline78Site, inline78Site_startPC⟩
  inline79 := ⟨inline79Site, inline79Site_startPC⟩
  coreExit := ⟨coreExitSite, coreExitSite_startPC⟩
  helper := ⟨helperSite, helperSite_startPC⟩

theorem validJumpDest_5190 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 5190 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4059 (by rfl)
  rw [helper_instructionPC] at h
  exact h

theorem validJumpDest_1894 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 1894 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1238 (by rfl)
  rw [return18_instructionPC] at h
  exact h

theorem validJumpDest_2471 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2471 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1733 (by rfl)
  rw [return30_instructionPC] at h
  exact h

theorem coreJumpValid (s : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) : PairedSynthCoreTrace.CoreJumpValid s := by
  intro dest hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  all_goals rw [hcode]
  · exact validJumpDest_5190
  · exact validJumpDest_1894
  · exact validJumpDest_2471

def gasSteps_core_normalized (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hready : NormalizedScheduleReady s.memory words) :
    GasSteps {s with pc := UInt256.ofNat 960, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho}
      {s with pc := UInt256.ofNat 5105, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (coreCryptoResult words left right) rho} :=
  PairedSynthCoreTrace.gasSteps_wholeCore_normalized wholeSites s words left right rho hstack hrun hactive
    (coreJumpValid s hcode) hcode hfork hnp hready

#print axioms group0_slice
#print axioms group0_instructionPC
#print axioms group0Site_startPC
#print axioms inline0_slice
#print axioms inline0_instructionPC
#print axioms inline0Site_startPC
#print axioms inline1_slice
#print axioms inline1_instructionPC
#print axioms inline1Site_startPC
#print axioms inline2_slice
#print axioms inline2_instructionPC
#print axioms inline2Site_startPC
#print axioms inline3_slice
#print axioms inline3_instructionPC
#print axioms inline3Site_startPC
#print axioms inline4_slice
#print axioms inline4_instructionPC
#print axioms inline4Site_startPC
#print axioms inline5_slice
#print axioms inline5_instructionPC
#print axioms inline5Site_startPC
#print axioms inline6_slice
#print axioms inline6_instructionPC
#print axioms inline6Site_startPC
#print axioms inline7_slice
#print axioms inline7_instructionPC
#print axioms inline7Site_startPC
#print axioms inline8_slice
#print axioms inline8_instructionPC
#print axioms inline8Site_startPC
#print axioms inline9_slice
#print axioms inline9_instructionPC
#print axioms inline9Site_startPC
#print axioms inline10_slice
#print axioms inline10_instructionPC
#print axioms inline10Site_startPC
#print axioms inline11_slice
#print axioms inline11_instructionPC
#print axioms inline11Site_startPC
#print axioms inline12_slice
#print axioms inline12_instructionPC
#print axioms inline12Site_startPC
#print axioms inline13_slice
#print axioms inline13_instructionPC
#print axioms inline13Site_startPC
#print axioms inline14_slice
#print axioms inline14_instructionPC
#print axioms inline14Site_startPC
#print axioms inline15_slice
#print axioms inline15_instructionPC
#print axioms inline15Site_startPC
#print axioms group16_slice
#print axioms group16_instructionPC
#print axioms group16Site_startPC
#print axioms call16_slice
#print axioms call16_instructionPC
#print axioms call16Site_startPC
#print axioms return18_slice
#print axioms return18_instructionPC
#print axioms return18Site_startPC
#print axioms inline18_slice
#print axioms inline18_instructionPC
#print axioms inline18Site_startPC
#print axioms inline19_slice
#print axioms inline19_instructionPC
#print axioms inline19Site_startPC
#print axioms inline20_slice
#print axioms inline20_instructionPC
#print axioms inline20Site_startPC
#print axioms inline21_slice
#print axioms inline21_instructionPC
#print axioms inline21Site_startPC
#print axioms inline22_slice
#print axioms inline22_instructionPC
#print axioms inline22Site_startPC
#print axioms inline23_slice
#print axioms inline23_instructionPC
#print axioms inline23Site_startPC
#print axioms inline24_slice
#print axioms inline24_instructionPC
#print axioms inline24Site_startPC
#print axioms inline25_slice
#print axioms inline25_instructionPC
#print axioms inline25Site_startPC
#print axioms inline26_slice
#print axioms inline26_instructionPC
#print axioms inline26Site_startPC
#print axioms inline27_slice
#print axioms inline27_instructionPC
#print axioms inline27Site_startPC
#print axioms call28_slice
#print axioms call28_instructionPC
#print axioms call28Site_startPC
#print axioms return30_slice
#print axioms return30_instructionPC
#print axioms return30Site_startPC
#print axioms inline30_slice
#print axioms inline30_instructionPC
#print axioms inline30Site_startPC
#print axioms inline31_slice
#print axioms inline31_instructionPC
#print axioms inline31Site_startPC
#print axioms group32_slice
#print axioms group32_instructionPC
#print axioms group32Site_startPC
#print axioms inline32_slice
#print axioms inline32_instructionPC
#print axioms inline32Site_startPC
#print axioms inline33_slice
#print axioms inline33_instructionPC
#print axioms inline33Site_startPC
#print axioms inline34_slice
#print axioms inline34_instructionPC
#print axioms inline34Site_startPC
#print axioms inline35_slice
#print axioms inline35_instructionPC
#print axioms inline35Site_startPC
#print axioms inline36_slice
#print axioms inline36_instructionPC
#print axioms inline36Site_startPC
#print axioms inline37_slice
#print axioms inline37_instructionPC
#print axioms inline37Site_startPC
#print axioms inline38_slice
#print axioms inline38_instructionPC
#print axioms inline38Site_startPC
#print axioms inline39_slice
#print axioms inline39_instructionPC
#print axioms inline39Site_startPC
#print axioms inline40_slice
#print axioms inline40_instructionPC
#print axioms inline40Site_startPC
#print axioms inline41_slice
#print axioms inline41_instructionPC
#print axioms inline41Site_startPC
#print axioms inline42_slice
#print axioms inline42_instructionPC
#print axioms inline42Site_startPC
#print axioms inline43_slice
#print axioms inline43_instructionPC
#print axioms inline43Site_startPC
#print axioms inline44_slice
#print axioms inline44_instructionPC
#print axioms inline44Site_startPC
#print axioms inline45_slice
#print axioms inline45_instructionPC
#print axioms inline45Site_startPC
#print axioms inline46_slice
#print axioms inline46_instructionPC
#print axioms inline46Site_startPC
#print axioms inline47_slice
#print axioms inline47_instructionPC
#print axioms inline47Site_startPC
#print axioms group48_slice
#print axioms group48_instructionPC
#print axioms group48Site_startPC
#print axioms inline48_slice
#print axioms inline48_instructionPC
#print axioms inline48Site_startPC
#print axioms inline49_slice
#print axioms inline49_instructionPC
#print axioms inline49Site_startPC
#print axioms inline50_slice
#print axioms inline50_instructionPC
#print axioms inline50Site_startPC
#print axioms inline51_slice
#print axioms inline51_instructionPC
#print axioms inline51Site_startPC
#print axioms inline52_slice
#print axioms inline52_instructionPC
#print axioms inline52Site_startPC
#print axioms inline53_slice
#print axioms inline53_instructionPC
#print axioms inline53Site_startPC
#print axioms inline54_slice
#print axioms inline54_instructionPC
#print axioms inline54Site_startPC
#print axioms inline55_slice
#print axioms inline55_instructionPC
#print axioms inline55Site_startPC
#print axioms inline56_slice
#print axioms inline56_instructionPC
#print axioms inline56Site_startPC
#print axioms inline57_slice
#print axioms inline57_instructionPC
#print axioms inline57Site_startPC
#print axioms inline58_slice
#print axioms inline58_instructionPC
#print axioms inline58Site_startPC
#print axioms inline59_slice
#print axioms inline59_instructionPC
#print axioms inline59Site_startPC
#print axioms inline60_slice
#print axioms inline60_instructionPC
#print axioms inline60Site_startPC
#print axioms inline61_slice
#print axioms inline61_instructionPC
#print axioms inline61Site_startPC
#print axioms inline62_slice
#print axioms inline62_instructionPC
#print axioms inline62Site_startPC
#print axioms inline63_slice
#print axioms inline63_instructionPC
#print axioms inline63Site_startPC
#print axioms group64_slice
#print axioms group64_instructionPC
#print axioms group64Site_startPC
#print axioms inline64_slice
#print axioms inline64_instructionPC
#print axioms inline64Site_startPC
#print axioms inline65_slice
#print axioms inline65_instructionPC
#print axioms inline65Site_startPC
#print axioms inline66_slice
#print axioms inline66_instructionPC
#print axioms inline66Site_startPC
#print axioms inline67_slice
#print axioms inline67_instructionPC
#print axioms inline67Site_startPC
#print axioms inline68_slice
#print axioms inline68_instructionPC
#print axioms inline68Site_startPC
#print axioms inline69_slice
#print axioms inline69_instructionPC
#print axioms inline69Site_startPC
#print axioms inline70_slice
#print axioms inline70_instructionPC
#print axioms inline70Site_startPC
#print axioms inline71_slice
#print axioms inline71_instructionPC
#print axioms inline71Site_startPC
#print axioms inline72_slice
#print axioms inline72_instructionPC
#print axioms inline72Site_startPC
#print axioms inline73_slice
#print axioms inline73_instructionPC
#print axioms inline73Site_startPC
#print axioms inline74_slice
#print axioms inline74_instructionPC
#print axioms inline74Site_startPC
#print axioms inline75_slice
#print axioms inline75_instructionPC
#print axioms inline75Site_startPC
#print axioms inline76_slice
#print axioms inline76_instructionPC
#print axioms inline76Site_startPC
#print axioms inline77_slice
#print axioms inline77_instructionPC
#print axioms inline77Site_startPC
#print axioms inline78_slice
#print axioms inline78_instructionPC
#print axioms inline78Site_startPC
#print axioms inline79_slice
#print axioms inline79_instructionPC
#print axioms inline79Site_startPC
#print axioms coreExit_slice
#print axioms coreExit_instructionPC
#print axioms coreExitSite_startPC
#print axioms helper_slice
#print axioms helper_instructionPC
#print axioms helperSite_startPC
#print axioms wholeSites
#print axioms validJumpDest_5190
#print axioms validJumpDest_1894
#print axioms validJumpDest_2471
#print axioms coreJumpValid
#print axioms gasSteps_core_normalized

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreSites

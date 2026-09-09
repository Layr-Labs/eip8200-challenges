import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate PairedHelperBooleanTrace

/-- Exact eighty inline rounds and six straightline seams of frozen5307/raw87c04874. -/

theorem group0_slice :
    (Artifact.submissionArtifact.instructions.drop 468).take PairedAllInlineCoreTrace.group0Template.length = PairedAllInlineCoreTrace.group0Template := by
  rfl

theorem group0_instructionPC :
    Artifact.submissionArtifact.instructionPC 468 = 769 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group0Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group0Template 468 group0_slice
    (by
      change 468 + PairedAllInlineCoreTrace.group0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group0Template) (by decide))
    (by decide)

theorem group0Site_startPC : group0Site.startPC = UInt256.ofNat 769 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 468) = UInt256.ofNat 769
  rw [group0_instructionPC]

theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 471).take PairedSynthCoreTrace.inline0Template.length = PairedSynthCoreTrace.inline0Template := by
  rfl

theorem inline0_instructionPC :
    Artifact.submissionArtifact.instructionPC 471 = 777 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline0Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline0Template 471 inline0_slice
    (by
      change 471 + PairedSynthCoreTrace.inline0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline0Template) (by decide))
    (by decide)

theorem inline0Site_startPC : inline0Site.startPC = UInt256.ofNat 777 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 471) = UInt256.ofNat 777
  rw [inline0_instructionPC]

theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 515).take PairedSynthCoreTrace.inline1Template.length = PairedSynthCoreTrace.inline1Template := by
  rfl

theorem inline1_instructionPC :
    Artifact.submissionArtifact.instructionPC 515 = 827 := by
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

theorem inline1Site_startPC : inline1Site.startPC = UInt256.ofNat 827 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 515) = UInt256.ofNat 827
  rw [inline1_instructionPC]

theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 559).take PairedSynthCoreTrace.inline2Template.length = PairedSynthCoreTrace.inline2Template := by
  rfl

theorem inline2_instructionPC :
    Artifact.submissionArtifact.instructionPC 559 = 877 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline2Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline2Template 559 inline2_slice
    (by
      change 559 + PairedSynthCoreTrace.inline2Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline2Template) (by decide))
    (by decide)

theorem inline2Site_startPC : inline2Site.startPC = UInt256.ofNat 877 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 559) = UInt256.ofNat 877
  rw [inline2_instructionPC]

theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 603).take PairedSynthCoreTrace.inline3Template.length = PairedSynthCoreTrace.inline3Template := by
  rfl

theorem inline3_instructionPC :
    Artifact.submissionArtifact.instructionPC 603 = 928 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline3Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline3Template 603 inline3_slice
    (by
      change 603 + PairedSynthCoreTrace.inline3Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline3Template) (by decide))
    (by decide)

theorem inline3Site_startPC : inline3Site.startPC = UInt256.ofNat 928 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 603) = UInt256.ofNat 928
  rw [inline3_instructionPC]

theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 645).take PairedSynthCoreTrace.inline4Template.length = PairedSynthCoreTrace.inline4Template := by
  rfl

theorem inline4_instructionPC :
    Artifact.submissionArtifact.instructionPC 645 = 975 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline4Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline4Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline4Template 645 inline4_slice
    (by
      change 645 + PairedSynthCoreTrace.inline4Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline4Template) (by decide))
    (by decide)

theorem inline4Site_startPC : inline4Site.startPC = UInt256.ofNat 975 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 645) = UInt256.ofNat 975
  rw [inline4_instructionPC]

theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 689).take PairedSynthCoreTrace.inline5Template.length = PairedSynthCoreTrace.inline5Template := by
  rfl

theorem inline5_instructionPC :
    Artifact.submissionArtifact.instructionPC 689 = 1026 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline5Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline5Template 689 inline5_slice
    (by
      change 689 + PairedSynthCoreTrace.inline5Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline5Template) (by decide))
    (by decide)

theorem inline5Site_startPC : inline5Site.startPC = UInt256.ofNat 1026 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 689) = UInt256.ofNat 1026
  rw [inline5_instructionPC]

theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 733).take PairedSynthCoreTrace.inline6Template.length = PairedSynthCoreTrace.inline6Template := by
  rfl

theorem inline6_instructionPC :
    Artifact.submissionArtifact.instructionPC 733 = 1077 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline6Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline6Template 733 inline6_slice
    (by
      change 733 + PairedSynthCoreTrace.inline6Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline6Template) (by decide))
    (by decide)

theorem inline6Site_startPC : inline6Site.startPC = UInt256.ofNat 1077 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 733) = UInt256.ofNat 1077
  rw [inline6_instructionPC]

theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 777).take PairedSynthCoreTrace.inline7Template.length = PairedSynthCoreTrace.inline7Template := by
  rfl

theorem inline7_instructionPC :
    Artifact.submissionArtifact.instructionPC 777 = 1128 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline7Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline7Template 777 inline7_slice
    (by
      change 777 + PairedSynthCoreTrace.inline7Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline7Template) (by decide))
    (by decide)

theorem inline7Site_startPC : inline7Site.startPC = UInt256.ofNat 1128 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 777) = UInt256.ofNat 1128
  rw [inline7_instructionPC]

theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 821).take PairedSynthCoreTrace.inline8Template.length = PairedSynthCoreTrace.inline8Template := by
  rfl

theorem inline8_instructionPC :
    Artifact.submissionArtifact.instructionPC 821 = 1179 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline8Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline8Template 821 inline8_slice
    (by
      change 821 + PairedSynthCoreTrace.inline8Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline8Template) (by decide))
    (by decide)

theorem inline8Site_startPC : inline8Site.startPC = UInt256.ofNat 1179 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 821) = UInt256.ofNat 1179
  rw [inline8_instructionPC]

theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 865).take PairedSynthCoreTrace.inline9Template.length = PairedSynthCoreTrace.inline9Template := by
  rfl

theorem inline9_instructionPC :
    Artifact.submissionArtifact.instructionPC 865 = 1230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline9Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline9Template 865 inline9_slice
    (by
      change 865 + PairedSynthCoreTrace.inline9Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline9Template) (by decide))
    (by decide)

theorem inline9Site_startPC : inline9Site.startPC = UInt256.ofNat 1230 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 865) = UInt256.ofNat 1230
  rw [inline9_instructionPC]

theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 909).take PairedSynthCoreTrace.inline10Template.length = PairedSynthCoreTrace.inline10Template := by
  rfl

theorem inline10_instructionPC :
    Artifact.submissionArtifact.instructionPC 909 = 1281 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline10Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline10Template 909 inline10_slice
    (by
      change 909 + PairedSynthCoreTrace.inline10Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline10Template) (by decide))
    (by decide)

theorem inline10Site_startPC : inline10Site.startPC = UInt256.ofNat 1281 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 909) = UInt256.ofNat 1281
  rw [inline10_instructionPC]

theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 953).take PairedSynthCoreTrace.inline11Template.length = PairedSynthCoreTrace.inline11Template := by
  rfl

theorem inline11_instructionPC :
    Artifact.submissionArtifact.instructionPC 953 = 1332 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline11Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline11Template 953 inline11_slice
    (by
      change 953 + PairedSynthCoreTrace.inline11Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline11Template) (by decide))
    (by decide)

theorem inline11Site_startPC : inline11Site.startPC = UInt256.ofNat 1332 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 953) = UInt256.ofNat 1332
  rw [inline11_instructionPC]

theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 997).take PairedSynthCoreTrace.inline12Template.length = PairedSynthCoreTrace.inline12Template := by
  rfl

theorem inline12_instructionPC :
    Artifact.submissionArtifact.instructionPC 997 = 1383 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline12Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline12Template 997 inline12_slice
    (by
      change 997 + PairedSynthCoreTrace.inline12Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline12Template) (by decide))
    (by decide)

theorem inline12Site_startPC : inline12Site.startPC = UInt256.ofNat 1383 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 997) = UInt256.ofNat 1383
  rw [inline12_instructionPC]

theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1041).take PairedSynthCoreTrace.inline13Template.length = PairedSynthCoreTrace.inline13Template := by
  rfl

theorem inline13_instructionPC :
    Artifact.submissionArtifact.instructionPC 1041 = 1433 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline13Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline13Template 1041 inline13_slice
    (by
      change 1041 + PairedSynthCoreTrace.inline13Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline13Template) (by decide))
    (by decide)

theorem inline13Site_startPC : inline13Site.startPC = UInt256.ofNat 1433 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1041) = UInt256.ofNat 1433
  rw [inline13_instructionPC]

theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1085).take PairedSynthCoreTrace.inline14Template.length = PairedSynthCoreTrace.inline14Template := by
  rfl

theorem inline14_instructionPC :
    Artifact.submissionArtifact.instructionPC 1085 = 1484 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline14Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline14Template 1085 inline14_slice
    (by
      change 1085 + PairedSynthCoreTrace.inline14Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline14Template) (by decide))
    (by decide)

theorem inline14Site_startPC : inline14Site.startPC = UInt256.ofNat 1484 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1085) = UInt256.ofNat 1484
  rw [inline14_instructionPC]

theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1129).take PairedSynthCoreTrace.inline15Template.length = PairedSynthCoreTrace.inline15Template := by
  rfl

theorem inline15_instructionPC :
    Artifact.submissionArtifact.instructionPC 1129 = 1535 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline15Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline15Template 1129 inline15_slice
    (by
      change 1129 + PairedSynthCoreTrace.inline15Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline15Template) (by decide))
    (by decide)

theorem inline15Site_startPC : inline15Site.startPC = UInt256.ofNat 1535 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1129) = UInt256.ofNat 1535
  rw [inline15_instructionPC]

theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1173).take PairedAllInlineCoreTrace.group16Template.length = PairedAllInlineCoreTrace.group16Template := by
  rfl

theorem group16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1173 = 1586 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group16Template 1173 group16_slice
    (by
      change 1173 + PairedAllInlineCoreTrace.group16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group16Template) (by decide))
    (by decide)

theorem group16Site_startPC : group16Site.startPC = UInt256.ofNat 1586 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1173) = UInt256.ofNat 1586
  rw [group16_instructionPC]

theorem inline16_slice :
    (Artifact.submissionArtifact.instructions.drop 1180).take PairedAllInlineNewPairs.inline16Template.length = PairedAllInlineNewPairs.inline16Template := by
  rfl

theorem inline16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1180 = 1602 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline16Template 1180 inline16_slice
    (by
      change 1180 + PairedAllInlineNewPairs.inline16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline16Template) (by decide))
    (by decide)

theorem inline16Site_startPC : inline16Site.startPC = UInt256.ofNat 1602 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1180) = UInt256.ofNat 1602
  rw [inline16_instructionPC]

theorem inline17_slice :
    (Artifact.submissionArtifact.instructions.drop 1226).take PairedAllInlineNewPairs.inline17Template.length = PairedAllInlineNewPairs.inline17Template := by
  rfl

theorem inline17_instructionPC :
    Artifact.submissionArtifact.instructionPC 1226 = 1655 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline17Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline17Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline17Template 1226 inline17_slice
    (by
      change 1226 + PairedAllInlineNewPairs.inline17Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline17Template) (by decide))
    (by decide)

theorem inline17Site_startPC : inline17Site.startPC = UInt256.ofNat 1655 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1226) = UInt256.ofNat 1655
  rw [inline17_instructionPC]

theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1272).take PairedAllInlineCoreTrace.inline18Template.length = PairedAllInlineCoreTrace.inline18Template := by
  rfl

theorem inline18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1272 = 1708 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline18Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline18Template 1272 inline18_slice
    (by
      change 1272 + PairedAllInlineCoreTrace.inline18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline18Template) (by decide))
    (by decide)

theorem inline18Site_startPC : inline18Site.startPC = UInt256.ofNat 1708 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1272) = UInt256.ofNat 1708
  rw [inline18_instructionPC]

theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1318).take PairedAllInlineCoreTrace.inline19Template.length = PairedAllInlineCoreTrace.inline19Template := by
  rfl

theorem inline19_instructionPC :
    Artifact.submissionArtifact.instructionPC 1318 = 1761 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline19Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline19Template 1318 inline19_slice
    (by
      change 1318 + PairedAllInlineCoreTrace.inline19Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline19Template) (by decide))
    (by decide)

theorem inline19Site_startPC : inline19Site.startPC = UInt256.ofNat 1761 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1318) = UInt256.ofNat 1761
  rw [inline19_instructionPC]

theorem inline20_slice :
    (Artifact.submissionArtifact.instructions.drop 1364).take PairedAllInlineCoreTrace.inline20Template.length = PairedAllInlineCoreTrace.inline20Template := by
  rfl

theorem inline20_instructionPC :
    Artifact.submissionArtifact.instructionPC 1364 = 1813 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline20Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline20Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline20Template 1364 inline20_slice
    (by
      change 1364 + PairedAllInlineCoreTrace.inline20Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline20Template) (by decide))
    (by decide)

theorem inline20Site_startPC : inline20Site.startPC = UInt256.ofNat 1813 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1364) = UInt256.ofNat 1813
  rw [inline20_instructionPC]

theorem inline21_slice :
    (Artifact.submissionArtifact.instructions.drop 1408).take PairedAllInlineCoreTrace.inline21Template.length = PairedAllInlineCoreTrace.inline21Template := by
  rfl

theorem inline21_instructionPC :
    Artifact.submissionArtifact.instructionPC 1408 = 1862 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline21Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline21Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline21Template 1408 inline21_slice
    (by
      change 1408 + PairedAllInlineCoreTrace.inline21Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline21Template) (by decide))
    (by decide)

theorem inline21Site_startPC : inline21Site.startPC = UInt256.ofNat 1862 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1408) = UInt256.ofNat 1862
  rw [inline21_instructionPC]

theorem inline22_slice :
    (Artifact.submissionArtifact.instructions.drop 1452).take PairedAllInlineCoreTrace.inline22Template.length = PairedAllInlineCoreTrace.inline22Template := by
  rfl

theorem inline22_instructionPC :
    Artifact.submissionArtifact.instructionPC 1452 = 1912 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline22Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline22Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline22Template 1452 inline22_slice
    (by
      change 1452 + PairedAllInlineCoreTrace.inline22Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline22Template) (by decide))
    (by decide)

theorem inline22Site_startPC : inline22Site.startPC = UInt256.ofNat 1912 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1452) = UInt256.ofNat 1912
  rw [inline22_instructionPC]

theorem inline23_slice :
    (Artifact.submissionArtifact.instructions.drop 1498).take PairedAllInlineCoreTrace.inline23Template.length = PairedAllInlineCoreTrace.inline23Template := by
  rfl

theorem inline23_instructionPC :
    Artifact.submissionArtifact.instructionPC 1498 = 1965 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline23Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline23Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline23Template 1498 inline23_slice
    (by
      change 1498 + PairedAllInlineCoreTrace.inline23Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline23Template) (by decide))
    (by decide)

theorem inline23Site_startPC : inline23Site.startPC = UInt256.ofNat 1965 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1498) = UInt256.ofNat 1965
  rw [inline23_instructionPC]

theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1544).take PairedAllInlineCoreTrace.inline24Template.length = PairedAllInlineCoreTrace.inline24Template := by
  rfl

theorem inline24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1544 = 2018 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline24Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline24Template 1544 inline24_slice
    (by
      change 1544 + PairedAllInlineCoreTrace.inline24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline24Template) (by decide))
    (by decide)

theorem inline24Site_startPC : inline24Site.startPC = UInt256.ofNat 2018 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1544) = UInt256.ofNat 2018
  rw [inline24_instructionPC]

theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1584).take PairedAllInlineCoreTrace.inline25Template.length = PairedAllInlineCoreTrace.inline25Template := by
  rfl

theorem inline25_instructionPC :
    Artifact.submissionArtifact.instructionPC 1584 = 2064 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline25Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline25Template 1584 inline25_slice
    (by
      change 1584 + PairedAllInlineCoreTrace.inline25Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline25Template) (by decide))
    (by decide)

theorem inline25Site_startPC : inline25Site.startPC = UInt256.ofNat 2064 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1584) = UInt256.ofNat 2064
  rw [inline25_instructionPC]

theorem inline26_slice :
    (Artifact.submissionArtifact.instructions.drop 1630).take PairedAllInlineCoreTrace.inline26Template.length = PairedAllInlineCoreTrace.inline26Template := by
  rfl

theorem inline26_instructionPC :
    Artifact.submissionArtifact.instructionPC 1630 = 2116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline26Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline26Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline26Template 1630 inline26_slice
    (by
      change 1630 + PairedAllInlineCoreTrace.inline26Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline26Template) (by decide))
    (by decide)

theorem inline26Site_startPC : inline26Site.startPC = UInt256.ofNat 2116 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1630) = UInt256.ofNat 2116
  rw [inline26_instructionPC]

theorem inline27_slice :
    (Artifact.submissionArtifact.instructions.drop 1676).take PairedAllInlineCoreTrace.inline27Template.length = PairedAllInlineCoreTrace.inline27Template := by
  rfl

theorem inline27_instructionPC :
    Artifact.submissionArtifact.instructionPC 1676 = 2169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline27Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline27Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline27Template 1676 inline27_slice
    (by
      change 1676 + PairedAllInlineCoreTrace.inline27Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline27Template) (by decide))
    (by decide)

theorem inline27Site_startPC : inline27Site.startPC = UInt256.ofNat 2169 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1676) = UInt256.ofNat 2169
  rw [inline27_instructionPC]

theorem inline28_slice :
    (Artifact.submissionArtifact.instructions.drop 1722).take PairedAllInlineNewPairs.inline28Template.length = PairedAllInlineNewPairs.inline28Template := by
  rfl

theorem inline28_instructionPC :
    Artifact.submissionArtifact.instructionPC 1722 = 2222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline28Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline28Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline28Template 1722 inline28_slice
    (by
      change 1722 + PairedAllInlineNewPairs.inline28Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline28Template) (by decide))
    (by decide)

theorem inline28Site_startPC : inline28Site.startPC = UInt256.ofNat 2222 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1722) = UInt256.ofNat 2222
  rw [inline28_instructionPC]

theorem inline29_slice :
    (Artifact.submissionArtifact.instructions.drop 1768).take PairedAllInlineNewPairs.inline29Template.length = PairedAllInlineNewPairs.inline29Template := by
  rfl

theorem inline29_instructionPC :
    Artifact.submissionArtifact.instructionPC 1768 = 2275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline29Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline29Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline29Template 1768 inline29_slice
    (by
      change 1768 + PairedAllInlineNewPairs.inline29Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline29Template) (by decide))
    (by decide)

theorem inline29Site_startPC : inline29Site.startPC = UInt256.ofNat 2275 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1768) = UInt256.ofNat 2275
  rw [inline29_instructionPC]

theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1814).take PairedAllInlineCoreTrace.inline30Template.length = PairedAllInlineCoreTrace.inline30Template := by
  rfl

theorem inline30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1814 = 2328 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline30Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline30Template 1814 inline30_slice
    (by
      change 1814 + PairedAllInlineCoreTrace.inline30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline30Template) (by decide))
    (by decide)

theorem inline30Site_startPC : inline30Site.startPC = UInt256.ofNat 2328 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1814) = UInt256.ofNat 2328
  rw [inline30_instructionPC]

theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1854).take PairedAllInlineCoreTrace.inline31Template.length = PairedAllInlineCoreTrace.inline31Template := by
  rfl

theorem inline31_instructionPC :
    Artifact.submissionArtifact.instructionPC 1854 = 2373 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline31Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline31Template 1854 inline31_slice
    (by
      change 1854 + PairedAllInlineCoreTrace.inline31Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline31Template) (by decide))
    (by decide)

theorem inline31Site_startPC : inline31Site.startPC = UInt256.ofNat 2373 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1854) = UInt256.ofNat 2373
  rw [inline31_instructionPC]

theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1898).take PairedAllInlineCoreTrace.group32Template.length = PairedAllInlineCoreTrace.group32Template := by
  rfl

theorem group32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1898 = 2423 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group32Template 1898 group32_slice
    (by
      change 1898 + PairedAllInlineCoreTrace.group32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group32Template) (by decide))
    (by decide)

theorem group32Site_startPC : group32Site.startPC = UInt256.ofNat 2423 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1898) = UInt256.ofNat 2423
  rw [group32_instructionPC]

theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1901).take PairedAllInlineCoreTrace.inline32Template.length = PairedAllInlineCoreTrace.inline32Template := by
  rfl

theorem inline32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1901 = 2447 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline32Template 1901 inline32_slice
    (by
      change 1901 + PairedAllInlineCoreTrace.inline32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline32Template) (by decide))
    (by decide)

theorem inline32Site_startPC : inline32Site.startPC = UInt256.ofNat 2447 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1901) = UInt256.ofNat 2447
  rw [inline32_instructionPC]

theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 1940).take PairedAllInlineCoreTrace.inline33Template.length = PairedAllInlineCoreTrace.inline33Template := by
  rfl

theorem inline33_instructionPC :
    Artifact.submissionArtifact.instructionPC 1940 = 2493 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline33Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline33Template 1940 inline33_slice
    (by
      change 1940 + PairedAllInlineCoreTrace.inline33Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline33Template) (by decide))
    (by decide)

theorem inline33Site_startPC : inline33Site.startPC = UInt256.ofNat 2493 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1940) = UInt256.ofNat 2493
  rw [inline33_instructionPC]

theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 1979).take PairedAllInlineCoreTrace.inline34Template.length = PairedAllInlineCoreTrace.inline34Template := by
  rfl

theorem inline34_instructionPC :
    Artifact.submissionArtifact.instructionPC 1979 = 2539 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline34Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline34Template 1979 inline34_slice
    (by
      change 1979 + PairedAllInlineCoreTrace.inline34Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline34Template) (by decide))
    (by decide)

theorem inline34Site_startPC : inline34Site.startPC = UInt256.ofNat 2539 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1979) = UInt256.ofNat 2539
  rw [inline34_instructionPC]

theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 2018).take PairedAllInlineCoreTrace.inline35Template.length = PairedAllInlineCoreTrace.inline35Template := by
  rfl

theorem inline35_instructionPC :
    Artifact.submissionArtifact.instructionPC 2018 = 2585 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline35Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline35Template 2018 inline35_slice
    (by
      change 2018 + PairedAllInlineCoreTrace.inline35Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline35Template) (by decide))
    (by decide)

theorem inline35Site_startPC : inline35Site.startPC = UInt256.ofNat 2585 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2018) = UInt256.ofNat 2585
  rw [inline35_instructionPC]

theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 2057).take PairedAllInlineCoreTrace.inline36Template.length = PairedAllInlineCoreTrace.inline36Template := by
  rfl

theorem inline36_instructionPC :
    Artifact.submissionArtifact.instructionPC 2057 = 2631 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline36Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline36Template 2057 inline36_slice
    (by
      change 2057 + PairedAllInlineCoreTrace.inline36Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline36Template) (by decide))
    (by decide)

theorem inline36Site_startPC : inline36Site.startPC = UInt256.ofNat 2631 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2057) = UInt256.ofNat 2631
  rw [inline36_instructionPC]

theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 2096).take PairedAllInlineCoreTrace.inline37Template.length = PairedAllInlineCoreTrace.inline37Template := by
  rfl

theorem inline37_instructionPC :
    Artifact.submissionArtifact.instructionPC 2096 = 2677 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline37Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline37Template 2096 inline37_slice
    (by
      change 2096 + PairedAllInlineCoreTrace.inline37Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline37Template) (by decide))
    (by decide)

theorem inline37Site_startPC : inline37Site.startPC = UInt256.ofNat 2677 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2096) = UInt256.ofNat 2677
  rw [inline37_instructionPC]

theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 2135).take PairedAllInlineCoreTrace.inline38Template.length = PairedAllInlineCoreTrace.inline38Template := by
  rfl

theorem inline38_instructionPC :
    Artifact.submissionArtifact.instructionPC 2135 = 2723 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline38Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline38Template 2135 inline38_slice
    (by
      change 2135 + PairedAllInlineCoreTrace.inline38Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline38Template) (by decide))
    (by decide)

theorem inline38Site_startPC : inline38Site.startPC = UInt256.ofNat 2723 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2135) = UInt256.ofNat 2723
  rw [inline38_instructionPC]

theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 2174).take PairedAllInlineCoreTrace.inline39Template.length = PairedAllInlineCoreTrace.inline39Template := by
  rfl

theorem inline39_instructionPC :
    Artifact.submissionArtifact.instructionPC 2174 = 2769 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline39Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline39Template 2174 inline39_slice
    (by
      change 2174 + PairedAllInlineCoreTrace.inline39Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline39Template) (by decide))
    (by decide)

theorem inline39Site_startPC : inline39Site.startPC = UInt256.ofNat 2769 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2174) = UInt256.ofNat 2769
  rw [inline39_instructionPC]

theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 2211).take PairedAllInlineCoreTrace.inline40Template.length = PairedAllInlineCoreTrace.inline40Template := by
  rfl

theorem inline40_instructionPC :
    Artifact.submissionArtifact.instructionPC 2211 = 2811 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline40Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline40Template 2211 inline40_slice
    (by
      change 2211 + PairedAllInlineCoreTrace.inline40Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline40Template) (by decide))
    (by decide)

theorem inline40Site_startPC : inline40Site.startPC = UInt256.ofNat 2811 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2211) = UInt256.ofNat 2811
  rw [inline40_instructionPC]

theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2250).take PairedAllInlineCoreTrace.inline41Template.length = PairedAllInlineCoreTrace.inline41Template := by
  rfl

theorem inline41_instructionPC :
    Artifact.submissionArtifact.instructionPC 2250 = 2857 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline41Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline41Template 2250 inline41_slice
    (by
      change 2250 + PairedAllInlineCoreTrace.inline41Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline41Template) (by decide))
    (by decide)

theorem inline41Site_startPC : inline41Site.startPC = UInt256.ofNat 2857 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2250) = UInt256.ofNat 2857
  rw [inline41_instructionPC]

theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2289).take PairedAllInlineCoreTrace.inline42Template.length = PairedAllInlineCoreTrace.inline42Template := by
  rfl

theorem inline42_instructionPC :
    Artifact.submissionArtifact.instructionPC 2289 = 2903 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline42Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline42Template 2289 inline42_slice
    (by
      change 2289 + PairedAllInlineCoreTrace.inline42Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline42Template) (by decide))
    (by decide)

theorem inline42Site_startPC : inline42Site.startPC = UInt256.ofNat 2903 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2289) = UInt256.ofNat 2903
  rw [inline42_instructionPC]

theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2328).take PairedAllInlineCoreTrace.inline43Template.length = PairedAllInlineCoreTrace.inline43Template := by
  rfl

theorem inline43_instructionPC :
    Artifact.submissionArtifact.instructionPC 2328 = 2948 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline43Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline43Template 2328 inline43_slice
    (by
      change 2328 + PairedAllInlineCoreTrace.inline43Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline43Template) (by decide))
    (by decide)

theorem inline43Site_startPC : inline43Site.startPC = UInt256.ofNat 2948 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2328) = UInt256.ofNat 2948
  rw [inline43_instructionPC]

theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2367).take PairedAllInlineCoreTrace.inline44Template.length = PairedAllInlineCoreTrace.inline44Template := by
  rfl

theorem inline44_instructionPC :
    Artifact.submissionArtifact.instructionPC 2367 = 2994 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline44Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline44Template 2367 inline44_slice
    (by
      change 2367 + PairedAllInlineCoreTrace.inline44Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline44Template) (by decide))
    (by decide)

theorem inline44Site_startPC : inline44Site.startPC = UInt256.ofNat 2994 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2367) = UInt256.ofNat 2994
  rw [inline44_instructionPC]

theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2406).take PairedAllInlineCoreTrace.inline45Template.length = PairedAllInlineCoreTrace.inline45Template := by
  rfl

theorem inline45_instructionPC :
    Artifact.submissionArtifact.instructionPC 2406 = 3040 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline45Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline45Template 2406 inline45_slice
    (by
      change 2406 + PairedAllInlineCoreTrace.inline45Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline45Template) (by decide))
    (by decide)

theorem inline45Site_startPC : inline45Site.startPC = UInt256.ofNat 3040 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2406) = UInt256.ofNat 3040
  rw [inline45_instructionPC]

theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2443).take PairedAllInlineCoreTrace.inline46Template.length = PairedAllInlineCoreTrace.inline46Template := by
  rfl

theorem inline46_instructionPC :
    Artifact.submissionArtifact.instructionPC 2443 = 3082 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline46Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline46Template 2443 inline46_slice
    (by
      change 2443 + PairedAllInlineCoreTrace.inline46Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline46Template) (by decide))
    (by decide)

theorem inline46Site_startPC : inline46Site.startPC = UInt256.ofNat 3082 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2443) = UInt256.ofNat 3082
  rw [inline46_instructionPC]

theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2476).take PairedAllInlineCoreTrace.inline47Template.length = PairedAllInlineCoreTrace.inline47Template := by
  rfl

theorem inline47_instructionPC :
    Artifact.submissionArtifact.instructionPC 2476 = 3121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline47Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline47Template 2476 inline47_slice
    (by
      change 2476 + PairedAllInlineCoreTrace.inline47Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline47Template) (by decide))
    (by decide)

theorem inline47Site_startPC : inline47Site.startPC = UInt256.ofNat 3121 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2476) = UInt256.ofNat 3121
  rw [inline47_instructionPC]

theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2509).take PairedAllInlineCoreTrace.group48Template.length = PairedAllInlineCoreTrace.group48Template := by
  rfl

theorem group48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2509 = 3160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group48Template 2509 group48_slice
    (by
      change 2509 + PairedAllInlineCoreTrace.group48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group48Template) (by decide))
    (by decide)

theorem group48Site_startPC : group48Site.startPC = UInt256.ofNat 3160 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2509) = UInt256.ofNat 3160
  rw [group48_instructionPC]

theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2512).take PairedAllInlineCoreTrace.inline48Template.length = PairedAllInlineCoreTrace.inline48Template := by
  rfl

theorem inline48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2512 = 3183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline48Template 2512 inline48_slice
    (by
      change 2512 + PairedAllInlineCoreTrace.inline48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline48Template) (by decide))
    (by decide)

theorem inline48Site_startPC : inline48Site.startPC = UInt256.ofNat 3183 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2512) = UInt256.ofNat 3183
  rw [inline48_instructionPC]

theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2558).take PairedAllInlineCoreTrace.inline49Template.length = PairedAllInlineCoreTrace.inline49Template := by
  rfl

theorem inline49_instructionPC :
    Artifact.submissionArtifact.instructionPC 2558 = 3235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline49Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline49Template 2558 inline49_slice
    (by
      change 2558 + PairedAllInlineCoreTrace.inline49Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline49Template) (by decide))
    (by decide)

theorem inline49Site_startPC : inline49Site.startPC = UInt256.ofNat 3235 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2558) = UInt256.ofNat 3235
  rw [inline49_instructionPC]

theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2604).take PairedAllInlineCoreTrace.inline50Template.length = PairedAllInlineCoreTrace.inline50Template := by
  rfl

theorem inline50_instructionPC :
    Artifact.submissionArtifact.instructionPC 2604 = 3288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline50Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline50Template 2604 inline50_slice
    (by
      change 2604 + PairedAllInlineCoreTrace.inline50Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline50Template) (by decide))
    (by decide)

theorem inline50Site_startPC : inline50Site.startPC = UInt256.ofNat 3288 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2604) = UInt256.ofNat 3288
  rw [inline50_instructionPC]

theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2650).take PairedAllInlineCoreTrace.inline51Template.length = PairedAllInlineCoreTrace.inline51Template := by
  rfl

theorem inline51_instructionPC :
    Artifact.submissionArtifact.instructionPC 2650 = 3341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline51Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline51Template 2650 inline51_slice
    (by
      change 2650 + PairedAllInlineCoreTrace.inline51Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline51Template) (by decide))
    (by decide)

theorem inline51Site_startPC : inline51Site.startPC = UInt256.ofNat 3341 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2650) = UInt256.ofNat 3341
  rw [inline51_instructionPC]

theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2696).take PairedAllInlineCoreTrace.inline52Template.length = PairedAllInlineCoreTrace.inline52Template := by
  rfl

theorem inline52_instructionPC :
    Artifact.submissionArtifact.instructionPC 2696 = 3393 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline52Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline52Template 2696 inline52_slice
    (by
      change 2696 + PairedAllInlineCoreTrace.inline52Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline52Template) (by decide))
    (by decide)

theorem inline52Site_startPC : inline52Site.startPC = UInt256.ofNat 3393 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2696) = UInt256.ofNat 3393
  rw [inline52_instructionPC]

theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2736).take PairedAllInlineCoreTrace.inline53Template.length = PairedAllInlineCoreTrace.inline53Template := by
  rfl

theorem inline53_instructionPC :
    Artifact.submissionArtifact.instructionPC 2736 = 3438 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline53Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline53Template 2736 inline53_slice
    (by
      change 2736 + PairedAllInlineCoreTrace.inline53Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline53Template) (by decide))
    (by decide)

theorem inline53Site_startPC : inline53Site.startPC = UInt256.ofNat 3438 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2736) = UInt256.ofNat 3438
  rw [inline53_instructionPC]

theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2780).take PairedAllInlineCoreTrace.inline54Template.length = PairedAllInlineCoreTrace.inline54Template := by
  rfl

theorem inline54_instructionPC :
    Artifact.submissionArtifact.instructionPC 2780 = 3488 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline54Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline54Template 2780 inline54_slice
    (by
      change 2780 + PairedAllInlineCoreTrace.inline54Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline54Template) (by decide))
    (by decide)

theorem inline54Site_startPC : inline54Site.startPC = UInt256.ofNat 3488 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2780) = UInt256.ofNat 3488
  rw [inline54_instructionPC]

theorem inline55_slice :
    (Artifact.submissionArtifact.instructions.drop 2826).take PairedAllInlineCoreTrace.inline55Template.length = PairedAllInlineCoreTrace.inline55Template := by
  rfl

theorem inline55_instructionPC :
    Artifact.submissionArtifact.instructionPC 2826 = 3541 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline55Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline55Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline55Template 2826 inline55_slice
    (by
      change 2826 + PairedAllInlineCoreTrace.inline55Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline55Template) (by decide))
    (by decide)

theorem inline55Site_startPC : inline55Site.startPC = UInt256.ofNat 3541 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2826) = UInt256.ofNat 3541
  rw [inline55_instructionPC]

theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 2872).take PairedAllInlineCoreTrace.inline56Template.length = PairedAllInlineCoreTrace.inline56Template := by
  rfl

theorem inline56_instructionPC :
    Artifact.submissionArtifact.instructionPC 2872 = 3593 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline56Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline56Template 2872 inline56_slice
    (by
      change 2872 + PairedAllInlineCoreTrace.inline56Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline56Template) (by decide))
    (by decide)

theorem inline56Site_startPC : inline56Site.startPC = UInt256.ofNat 3593 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2872) = UInt256.ofNat 3593
  rw [inline56_instructionPC]

theorem inline57_slice :
    (Artifact.submissionArtifact.instructions.drop 2918).take PairedAllInlineCoreTrace.inline57Template.length = PairedAllInlineCoreTrace.inline57Template := by
  rfl

theorem inline57_instructionPC :
    Artifact.submissionArtifact.instructionPC 2918 = 3646 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline57Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline57Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline57Template 2918 inline57_slice
    (by
      change 2918 + PairedAllInlineCoreTrace.inline57Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline57Template) (by decide))
    (by decide)

theorem inline57Site_startPC : inline57Site.startPC = UInt256.ofNat 3646 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2918) = UInt256.ofNat 3646
  rw [inline57_instructionPC]

theorem inline58_slice :
    (Artifact.submissionArtifact.instructions.drop 2964).take PairedAllInlineCoreTrace.inline58Template.length = PairedAllInlineCoreTrace.inline58Template := by
  rfl

theorem inline58_instructionPC :
    Artifact.submissionArtifact.instructionPC 2964 = 3699 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline58Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline58Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline58Template 2964 inline58_slice
    (by
      change 2964 + PairedAllInlineCoreTrace.inline58Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline58Template) (by decide))
    (by decide)

theorem inline58Site_startPC : inline58Site.startPC = UInt256.ofNat 3699 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2964) = UInt256.ofNat 3699
  rw [inline58_instructionPC]

theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 3010).take PairedAllInlineCoreTrace.inline59Template.length = PairedAllInlineCoreTrace.inline59Template := by
  rfl

theorem inline59_instructionPC :
    Artifact.submissionArtifact.instructionPC 3010 = 3752 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline59Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline59Template 3010 inline59_slice
    (by
      change 3010 + PairedAllInlineCoreTrace.inline59Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline59Template) (by decide))
    (by decide)

theorem inline59Site_startPC : inline59Site.startPC = UInt256.ofNat 3752 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3010) = UInt256.ofNat 3752
  rw [inline59_instructionPC]

theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 3056).take PairedAllInlineCoreTrace.inline60Template.length = PairedAllInlineCoreTrace.inline60Template := by
  rfl

theorem inline60_instructionPC :
    Artifact.submissionArtifact.instructionPC 3056 = 3805 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline60Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline60Template 3056 inline60_slice
    (by
      change 3056 + PairedAllInlineCoreTrace.inline60Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline60Template) (by decide))
    (by decide)

theorem inline60Site_startPC : inline60Site.startPC = UInt256.ofNat 3805 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3056) = UInt256.ofNat 3805
  rw [inline60_instructionPC]

theorem inline61_slice :
    (Artifact.submissionArtifact.instructions.drop 3102).take PairedAllInlineCoreTrace.inline61Template.length = PairedAllInlineCoreTrace.inline61Template := by
  rfl

theorem inline61_instructionPC :
    Artifact.submissionArtifact.instructionPC 3102 = 3858 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline61Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline61Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline61Template 3102 inline61_slice
    (by
      change 3102 + PairedAllInlineCoreTrace.inline61Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline61Template) (by decide))
    (by decide)

theorem inline61Site_startPC : inline61Site.startPC = UInt256.ofNat 3858 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3102) = UInt256.ofNat 3858
  rw [inline61_instructionPC]

theorem inline62_slice :
    (Artifact.submissionArtifact.instructions.drop 3146).take PairedAllInlineCoreTrace.inline62Template.length = PairedAllInlineCoreTrace.inline62Template := by
  rfl

theorem inline62_instructionPC :
    Artifact.submissionArtifact.instructionPC 3146 = 3908 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline62Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline62Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline62Template 3146 inline62_slice
    (by
      change 3146 + PairedAllInlineCoreTrace.inline62Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline62Template) (by decide))
    (by decide)

theorem inline62Site_startPC : inline62Site.startPC = UInt256.ofNat 3908 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3146) = UInt256.ofNat 3908
  rw [inline62_instructionPC]

theorem inline63_slice :
    (Artifact.submissionArtifact.instructions.drop 3192).take PairedAllInlineCoreTrace.inline63Template.length = PairedAllInlineCoreTrace.inline63Template := by
  rfl

theorem inline63_instructionPC :
    Artifact.submissionArtifact.instructionPC 3192 = 3962 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline63Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline63Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline63Template 3192 inline63_slice
    (by
      change 3192 + PairedAllInlineCoreTrace.inline63Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline63Template) (by decide))
    (by decide)

theorem inline63Site_startPC : inline63Site.startPC = UInt256.ofNat 3962 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3192) = UInt256.ofNat 3962
  rw [inline63_instructionPC]

theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3238).take PairedAllInlineCoreTrace.group64Template.length = PairedAllInlineCoreTrace.group64Template := by
  rfl

theorem group64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3238 = 4015 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group64Template 3238 group64_slice
    (by
      change 3238 + PairedAllInlineCoreTrace.group64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group64Template) (by decide))
    (by decide)

theorem group64Site_startPC : group64Site.startPC = UInt256.ofNat 4015 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3238) = UInt256.ofNat 4015
  rw [group64_instructionPC]

theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3241).take PairedAllInlineCoreTrace.inline64Template.length = PairedAllInlineCoreTrace.inline64Template := by
  rfl

theorem inline64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3241 = 4022 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline64Template 3241 inline64_slice
    (by
      change 3241 + PairedAllInlineCoreTrace.inline64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline64Template) (by decide))
    (by decide)

theorem inline64Site_startPC : inline64Site.startPC = UInt256.ofNat 4022 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3241) = UInt256.ofNat 4022
  rw [inline64_instructionPC]

theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3283).take PairedAllInlineCoreTrace.inline65Template.length = PairedAllInlineCoreTrace.inline65Template := by
  rfl

theorem inline65_instructionPC :
    Artifact.submissionArtifact.instructionPC 3283 = 4070 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline65Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline65Template 3283 inline65_slice
    (by
      change 3283 + PairedAllInlineCoreTrace.inline65Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline65Template) (by decide))
    (by decide)

theorem inline65Site_startPC : inline65Site.startPC = UInt256.ofNat 4070 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3283) = UInt256.ofNat 4070
  rw [inline65_instructionPC]

theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3327).take PairedAllInlineCoreTrace.inline66Template.length = PairedAllInlineCoreTrace.inline66Template := by
  rfl

theorem inline66_instructionPC :
    Artifact.submissionArtifact.instructionPC 3327 = 4121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline66Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline66Template 3327 inline66_slice
    (by
      change 3327 + PairedAllInlineCoreTrace.inline66Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline66Template) (by decide))
    (by decide)

theorem inline66Site_startPC : inline66Site.startPC = UInt256.ofNat 4121 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3327) = UInt256.ofNat 4121
  rw [inline66_instructionPC]

theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3371).take PairedAllInlineCoreTrace.inline67Template.length = PairedAllInlineCoreTrace.inline67Template := by
  rfl

theorem inline67_instructionPC :
    Artifact.submissionArtifact.instructionPC 3371 = 4172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline67Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline67Template 3371 inline67_slice
    (by
      change 3371 + PairedAllInlineCoreTrace.inline67Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline67Template) (by decide))
    (by decide)

theorem inline67Site_startPC : inline67Site.startPC = UInt256.ofNat 4172 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3371) = UInt256.ofNat 4172
  rw [inline67_instructionPC]

theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3415).take PairedAllInlineCoreTrace.inline68Template.length = PairedAllInlineCoreTrace.inline68Template := by
  rfl

theorem inline68_instructionPC :
    Artifact.submissionArtifact.instructionPC 3415 = 4223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline68Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline68Template 3415 inline68_slice
    (by
      change 3415 + PairedAllInlineCoreTrace.inline68Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline68Template) (by decide))
    (by decide)

theorem inline68Site_startPC : inline68Site.startPC = UInt256.ofNat 4223 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3415) = UInt256.ofNat 4223
  rw [inline68_instructionPC]

theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3459).take PairedAllInlineCoreTrace.inline69Template.length = PairedAllInlineCoreTrace.inline69Template := by
  rfl

theorem inline69_instructionPC :
    Artifact.submissionArtifact.instructionPC 3459 = 4273 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline69Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline69Template 3459 inline69_slice
    (by
      change 3459 + PairedAllInlineCoreTrace.inline69Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline69Template) (by decide))
    (by decide)

theorem inline69Site_startPC : inline69Site.startPC = UInt256.ofNat 4273 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3459) = UInt256.ofNat 4273
  rw [inline69_instructionPC]

theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3503).take PairedAllInlineCoreTrace.inline70Template.length = PairedAllInlineCoreTrace.inline70Template := by
  rfl

theorem inline70_instructionPC :
    Artifact.submissionArtifact.instructionPC 3503 = 4324 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline70Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline70Template 3503 inline70_slice
    (by
      change 3503 + PairedAllInlineCoreTrace.inline70Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline70Template) (by decide))
    (by decide)

theorem inline70Site_startPC : inline70Site.startPC = UInt256.ofNat 4324 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3503) = UInt256.ofNat 4324
  rw [inline70_instructionPC]

theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3545).take PairedAllInlineCoreTrace.inline71Template.length = PairedAllInlineCoreTrace.inline71Template := by
  rfl

theorem inline71_instructionPC :
    Artifact.submissionArtifact.instructionPC 3545 = 4372 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline71Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline71Template 3545 inline71_slice
    (by
      change 3545 + PairedAllInlineCoreTrace.inline71Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline71Template) (by decide))
    (by decide)

theorem inline71Site_startPC : inline71Site.startPC = UInt256.ofNat 4372 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3545) = UInt256.ofNat 4372
  rw [inline71_instructionPC]

theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3589).take PairedAllInlineCoreTrace.inline72Template.length = PairedAllInlineCoreTrace.inline72Template := by
  rfl

theorem inline72_instructionPC :
    Artifact.submissionArtifact.instructionPC 3589 = 4423 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline72Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline72Template 3589 inline72_slice
    (by
      change 3589 + PairedAllInlineCoreTrace.inline72Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline72Template) (by decide))
    (by decide)

theorem inline72Site_startPC : inline72Site.startPC = UInt256.ofNat 4423 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3589) = UInt256.ofNat 4423
  rw [inline72_instructionPC]

theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3633).take PairedAllInlineCoreTrace.inline73Template.length = PairedAllInlineCoreTrace.inline73Template := by
  rfl

theorem inline73_instructionPC :
    Artifact.submissionArtifact.instructionPC 3633 = 4474 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline73Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline73Template 3633 inline73_slice
    (by
      change 3633 + PairedAllInlineCoreTrace.inline73Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline73Template) (by decide))
    (by decide)

theorem inline73Site_startPC : inline73Site.startPC = UInt256.ofNat 4474 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3633) = UInt256.ofNat 4474
  rw [inline73_instructionPC]

theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3675).take PairedAllInlineCoreTrace.inline74Template.length = PairedAllInlineCoreTrace.inline74Template := by
  rfl

theorem inline74_instructionPC :
    Artifact.submissionArtifact.instructionPC 3675 = 4521 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline74Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline74Template 3675 inline74_slice
    (by
      change 3675 + PairedAllInlineCoreTrace.inline74Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline74Template) (by decide))
    (by decide)

theorem inline74Site_startPC : inline74Site.startPC = UInt256.ofNat 4521 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3675) = UInt256.ofNat 4521
  rw [inline74_instructionPC]

theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3719).take PairedAllInlineCoreTrace.inline75Template.length = PairedAllInlineCoreTrace.inline75Template := by
  rfl

theorem inline75_instructionPC :
    Artifact.submissionArtifact.instructionPC 3719 = 4572 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline75Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline75Template 3719 inline75_slice
    (by
      change 3719 + PairedAllInlineCoreTrace.inline75Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline75Template) (by decide))
    (by decide)

theorem inline75Site_startPC : inline75Site.startPC = UInt256.ofNat 4572 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3719) = UInt256.ofNat 4572
  rw [inline75_instructionPC]

theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3763).take PairedAllInlineCoreTrace.inline76Template.length = PairedAllInlineCoreTrace.inline76Template := by
  rfl

theorem inline76_instructionPC :
    Artifact.submissionArtifact.instructionPC 3763 = 4624 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline76Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline76Template 3763 inline76_slice
    (by
      change 3763 + PairedAllInlineCoreTrace.inline76Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline76Template) (by decide))
    (by decide)

theorem inline76Site_startPC : inline76Site.startPC = UInt256.ofNat 4624 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3763) = UInt256.ofNat 4624
  rw [inline76_instructionPC]

theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 3807).take PairedAllInlineCoreTrace.inline77Template.length = PairedAllInlineCoreTrace.inline77Template := by
  rfl

theorem inline77_instructionPC :
    Artifact.submissionArtifact.instructionPC 3807 = 4674 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline77Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline77Template 3807 inline77_slice
    (by
      change 3807 + PairedAllInlineCoreTrace.inline77Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline77Template) (by decide))
    (by decide)

theorem inline77Site_startPC : inline77Site.startPC = UInt256.ofNat 4674 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3807) = UInt256.ofNat 4674
  rw [inline77_instructionPC]

theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3851).take PairedAllInlineCoreTrace.inline78Template.length = PairedAllInlineCoreTrace.inline78Template := by
  rfl

theorem inline78_instructionPC :
    Artifact.submissionArtifact.instructionPC 3851 = 4725 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline78Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline78Template 3851 inline78_slice
    (by
      change 3851 + PairedAllInlineCoreTrace.inline78Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline78Template) (by decide))
    (by decide)

theorem inline78Site_startPC : inline78Site.startPC = UInt256.ofNat 4725 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3851) = UInt256.ofNat 4725
  rw [inline78_instructionPC]

theorem inline79_slice :
    (Artifact.submissionArtifact.instructions.drop 3895).take PairedAllInlineCoreTrace.inline79Template.length = PairedAllInlineCoreTrace.inline79Template := by
  rfl

theorem inline79_instructionPC :
    Artifact.submissionArtifact.instructionPC 3895 = 4776 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline79Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline79Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline79Template 3895 inline79_slice
    (by
      change 3895 + PairedAllInlineCoreTrace.inline79Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline79Template) (by decide))
    (by decide)

theorem inline79Site_startPC : inline79Site.startPC = UInt256.ofNat 4776 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3895) = UInt256.ofNat 4776
  rw [inline79_instructionPC]

theorem coreExit_slice :
    (Artifact.submissionArtifact.instructions.drop 3939).take PairedAllInlineCoreTrace.coreExitTemplate.length = PairedAllInlineCoreTrace.coreExitTemplate := by
  rfl

theorem coreExit_instructionPC :
    Artifact.submissionArtifact.instructionPC 3939 = 4827 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def coreExitSite : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.coreExitTemplate :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.coreExitTemplate 3939 coreExit_slice
    (by
      change 3939 + PairedAllInlineCoreTrace.coreExitTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.coreExitTemplate) (by decide))
    (by decide)

theorem coreExitSite_startPC : coreExitSite.startPC = UInt256.ofNat 4827 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3939) = UInt256.ofNat 4827
  rw [coreExit_instructionPC]

def wholeSites : PairedAllInlineCoreTrace.WholeCoreSites Artifact.submissionArtifact .Osaka where
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
  inline16 := ⟨inline16Site, inline16Site_startPC⟩
  inline17 := ⟨inline17Site, inline17Site_startPC⟩
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
  inline28 := ⟨inline28Site, inline28Site_startPC⟩
  inline29 := ⟨inline29Site, inline29Site_startPC⟩
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

def gasSteps_core_normalized (s : State) (words : Nat → UInt32)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hready : NormalizedScheduleReady s.memory words) :
    GasSteps {s with pc := UInt256.ofNat 769, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho}
      {s with pc := UInt256.ofNat 4829, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (coreCryptoResult words left right) rho} :=
  PairedAllInlineCoreTrace.gasSteps_wholeCore_normalized wholeSites s words left right rho hstack hrun hactive
    hcode hfork hnp hready

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
#print axioms inline16_slice
#print axioms inline16_instructionPC
#print axioms inline16Site_startPC
#print axioms inline17_slice
#print axioms inline17_instructionPC
#print axioms inline17Site_startPC
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
#print axioms inline28_slice
#print axioms inline28_instructionPC
#print axioms inline28Site_startPC
#print axioms inline29_slice
#print axioms inline29_instructionPC
#print axioms inline29Site_startPC
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
#print axioms wholeSites
#print axioms gasSteps_core_normalized

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites


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
    (Artifact.submissionArtifact.instructions.drop 486).take PairedAllInlineCoreTrace.group0Template.length = PairedAllInlineCoreTrace.group0Template := by
  rfl

theorem group0_instructionPC :
    Artifact.submissionArtifact.instructionPC 486 = 919 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group0Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group0Template 486 group0_slice
    (by
      change 486 + PairedAllInlineCoreTrace.group0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group0Template) (by decide))
    (by decide)

theorem group0Site_startPC : group0Site.startPC = UInt256.ofNat 919 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 486) = UInt256.ofNat 919
  rw [group0_instructionPC]

theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 487).take PairedSynthCoreTrace.inline0Template.length = PairedSynthCoreTrace.inline0Template := by
  rfl

theorem inline0_instructionPC :
    Artifact.submissionArtifact.instructionPC 487 = 940 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline0Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline0Template 487 inline0_slice
    (by
      change 487 + PairedSynthCoreTrace.inline0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline0Template) (by decide))
    (by decide)

theorem inline0Site_startPC : inline0Site.startPC = UInt256.ofNat 940 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 487) = UInt256.ofNat 940
  rw [inline0_instructionPC]

theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 531).take PairedSynthCoreTrace.inline1Template.length = PairedSynthCoreTrace.inline1Template := by
  rfl

theorem inline1_instructionPC :
    Artifact.submissionArtifact.instructionPC 531 = 990 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline1Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline1Template 531 inline1_slice
    (by
      change 531 + PairedSynthCoreTrace.inline1Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline1Template) (by decide))
    (by decide)

theorem inline1Site_startPC : inline1Site.startPC = UInt256.ofNat 990 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 531) = UInt256.ofNat 990
  rw [inline1_instructionPC]

theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 575).take PairedSynthCoreTrace.inline2Template.length = PairedSynthCoreTrace.inline2Template := by
  rfl

theorem inline2_instructionPC :
    Artifact.submissionArtifact.instructionPC 575 = 1040 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline2Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline2Template 575 inline2_slice
    (by
      change 575 + PairedSynthCoreTrace.inline2Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline2Template) (by decide))
    (by decide)

theorem inline2Site_startPC : inline2Site.startPC = UInt256.ofNat 1040 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 575) = UInt256.ofNat 1040
  rw [inline2_instructionPC]

theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 619).take PairedSynthCoreTrace.inline3Template.length = PairedSynthCoreTrace.inline3Template := by
  rfl

theorem inline3_instructionPC :
    Artifact.submissionArtifact.instructionPC 619 = 1091 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline3Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline3Template 619 inline3_slice
    (by
      change 619 + PairedSynthCoreTrace.inline3Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline3Template) (by decide))
    (by decide)

theorem inline3Site_startPC : inline3Site.startPC = UInt256.ofNat 1091 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 619) = UInt256.ofNat 1091
  rw [inline3_instructionPC]

theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 661).take PairedSynthCoreTrace.inline4Template.length = PairedSynthCoreTrace.inline4Template := by
  rfl

theorem inline4_instructionPC :
    Artifact.submissionArtifact.instructionPC 661 = 1138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline4Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline4Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline4Template 661 inline4_slice
    (by
      change 661 + PairedSynthCoreTrace.inline4Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline4Template) (by decide))
    (by decide)

theorem inline4Site_startPC : inline4Site.startPC = UInt256.ofNat 1138 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 661) = UInt256.ofNat 1138
  rw [inline4_instructionPC]

theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 705).take PairedSynthCoreTrace.inline5Template.length = PairedSynthCoreTrace.inline5Template := by
  rfl

theorem inline5_instructionPC :
    Artifact.submissionArtifact.instructionPC 705 = 1189 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline5Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline5Template 705 inline5_slice
    (by
      change 705 + PairedSynthCoreTrace.inline5Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline5Template) (by decide))
    (by decide)

theorem inline5Site_startPC : inline5Site.startPC = UInt256.ofNat 1189 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 705) = UInt256.ofNat 1189
  rw [inline5_instructionPC]

theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 749).take PairedSynthCoreTrace.inline6Template.length = PairedSynthCoreTrace.inline6Template := by
  rfl

theorem inline6_instructionPC :
    Artifact.submissionArtifact.instructionPC 749 = 1240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline6Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline6Template 749 inline6_slice
    (by
      change 749 + PairedSynthCoreTrace.inline6Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline6Template) (by decide))
    (by decide)

theorem inline6Site_startPC : inline6Site.startPC = UInt256.ofNat 1240 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 749) = UInt256.ofNat 1240
  rw [inline6_instructionPC]

theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 793).take PairedSynthCoreTrace.inline7Template.length = PairedSynthCoreTrace.inline7Template := by
  rfl

theorem inline7_instructionPC :
    Artifact.submissionArtifact.instructionPC 793 = 1291 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline7Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline7Template 793 inline7_slice
    (by
      change 793 + PairedSynthCoreTrace.inline7Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline7Template) (by decide))
    (by decide)

theorem inline7Site_startPC : inline7Site.startPC = UInt256.ofNat 1291 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 793) = UInt256.ofNat 1291
  rw [inline7_instructionPC]

theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 837).take PairedSynthCoreTrace.inline8Template.length = PairedSynthCoreTrace.inline8Template := by
  rfl

theorem inline8_instructionPC :
    Artifact.submissionArtifact.instructionPC 837 = 1342 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline8Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline8Template 837 inline8_slice
    (by
      change 837 + PairedSynthCoreTrace.inline8Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline8Template) (by decide))
    (by decide)

theorem inline8Site_startPC : inline8Site.startPC = UInt256.ofNat 1342 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 837) = UInt256.ofNat 1342
  rw [inline8_instructionPC]

theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 881).take PairedSynthCoreTrace.inline9Template.length = PairedSynthCoreTrace.inline9Template := by
  rfl

theorem inline9_instructionPC :
    Artifact.submissionArtifact.instructionPC 881 = 1393 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline9Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline9Template 881 inline9_slice
    (by
      change 881 + PairedSynthCoreTrace.inline9Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline9Template) (by decide))
    (by decide)

theorem inline9Site_startPC : inline9Site.startPC = UInt256.ofNat 1393 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 881) = UInt256.ofNat 1393
  rw [inline9_instructionPC]

theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 925).take PairedSynthCoreTrace.inline10Template.length = PairedSynthCoreTrace.inline10Template := by
  rfl

theorem inline10_instructionPC :
    Artifact.submissionArtifact.instructionPC 925 = 1444 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline10Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline10Template 925 inline10_slice
    (by
      change 925 + PairedSynthCoreTrace.inline10Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline10Template) (by decide))
    (by decide)

theorem inline10Site_startPC : inline10Site.startPC = UInt256.ofNat 1444 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 925) = UInt256.ofNat 1444
  rw [inline10_instructionPC]

theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 969).take PairedSynthCoreTrace.inline11Template.length = PairedSynthCoreTrace.inline11Template := by
  rfl

theorem inline11_instructionPC :
    Artifact.submissionArtifact.instructionPC 969 = 1495 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline11Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline11Template 969 inline11_slice
    (by
      change 969 + PairedSynthCoreTrace.inline11Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline11Template) (by decide))
    (by decide)

theorem inline11Site_startPC : inline11Site.startPC = UInt256.ofNat 1495 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 969) = UInt256.ofNat 1495
  rw [inline11_instructionPC]

theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1013).take PairedSynthCoreTrace.inline12Template.length = PairedSynthCoreTrace.inline12Template := by
  rfl

theorem inline12_instructionPC :
    Artifact.submissionArtifact.instructionPC 1013 = 1546 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline12Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline12Template 1013 inline12_slice
    (by
      change 1013 + PairedSynthCoreTrace.inline12Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline12Template) (by decide))
    (by decide)

theorem inline12Site_startPC : inline12Site.startPC = UInt256.ofNat 1546 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1013) = UInt256.ofNat 1546
  rw [inline12_instructionPC]

theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1057).take PairedSynthCoreTrace.inline13Template.length = PairedSynthCoreTrace.inline13Template := by
  rfl

theorem inline13_instructionPC :
    Artifact.submissionArtifact.instructionPC 1057 = 1596 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline13Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline13Template 1057 inline13_slice
    (by
      change 1057 + PairedSynthCoreTrace.inline13Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline13Template) (by decide))
    (by decide)

theorem inline13Site_startPC : inline13Site.startPC = UInt256.ofNat 1596 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1057) = UInt256.ofNat 1596
  rw [inline13_instructionPC]

theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1101).take PairedSynthCoreTrace.inline14Template.length = PairedSynthCoreTrace.inline14Template := by
  rfl

theorem inline14_instructionPC :
    Artifact.submissionArtifact.instructionPC 1101 = 1647 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline14Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline14Template 1101 inline14_slice
    (by
      change 1101 + PairedSynthCoreTrace.inline14Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline14Template) (by decide))
    (by decide)

theorem inline14Site_startPC : inline14Site.startPC = UInt256.ofNat 1647 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1101) = UInt256.ofNat 1647
  rw [inline14_instructionPC]

theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1145).take PairedSynthCoreTrace.inline15Template.length = PairedSynthCoreTrace.inline15Template := by
  rfl

theorem inline15_instructionPC :
    Artifact.submissionArtifact.instructionPC 1145 = 1698 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline15Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline15Template 1145 inline15_slice
    (by
      change 1145 + PairedSynthCoreTrace.inline15Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline15Template) (by decide))
    (by decide)

theorem inline15Site_startPC : inline15Site.startPC = UInt256.ofNat 1698 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1145) = UInt256.ofNat 1698
  rw [inline15_instructionPC]

theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1189).take PairedAllInlineCoreTrace.group16Template.length = PairedAllInlineCoreTrace.group16Template := by
  rfl

theorem group16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1189 = 1749 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group16Template 1189 group16_slice
    (by
      change 1189 + PairedAllInlineCoreTrace.group16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group16Template) (by decide))
    (by decide)

theorem group16Site_startPC : group16Site.startPC = UInt256.ofNat 1749 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1189) = UInt256.ofNat 1749
  rw [group16_instructionPC]

theorem inline16_slice :
    (Artifact.submissionArtifact.instructions.drop 1192).take PairedAllInlineNewPairs.inline16Template.length = PairedAllInlineNewPairs.inline16Template := by
  rfl

theorem inline16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1192 = 1772 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline16Template 1192 inline16_slice
    (by
      change 1192 + PairedAllInlineNewPairs.inline16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline16Template) (by decide))
    (by decide)

theorem inline16Site_startPC : inline16Site.startPC = UInt256.ofNat 1772 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1192) = UInt256.ofNat 1772
  rw [inline16_instructionPC]

theorem inline17_slice :
    (Artifact.submissionArtifact.instructions.drop 1238).take PairedAllInlineNewPairs.inline17Template.length = PairedAllInlineNewPairs.inline17Template := by
  rfl

theorem inline17_instructionPC :
    Artifact.submissionArtifact.instructionPC 1238 = 1825 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline17Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline17Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline17Template 1238 inline17_slice
    (by
      change 1238 + PairedAllInlineNewPairs.inline17Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline17Template) (by decide))
    (by decide)

theorem inline17Site_startPC : inline17Site.startPC = UInt256.ofNat 1825 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1238) = UInt256.ofNat 1825
  rw [inline17_instructionPC]

theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1284).take PairedAllInlineCoreTrace.inline18Template.length = PairedAllInlineCoreTrace.inline18Template := by
  rfl

theorem inline18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1284 = 1878 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline18Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline18Template 1284 inline18_slice
    (by
      change 1284 + PairedAllInlineCoreTrace.inline18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline18Template) (by decide))
    (by decide)

theorem inline18Site_startPC : inline18Site.startPC = UInt256.ofNat 1878 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1284) = UInt256.ofNat 1878
  rw [inline18_instructionPC]

theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1330).take PairedAllInlineCoreTrace.inline19Template.length = PairedAllInlineCoreTrace.inline19Template := by
  rfl

theorem inline19_instructionPC :
    Artifact.submissionArtifact.instructionPC 1330 = 1931 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline19Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline19Template 1330 inline19_slice
    (by
      change 1330 + PairedAllInlineCoreTrace.inline19Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline19Template) (by decide))
    (by decide)

theorem inline19Site_startPC : inline19Site.startPC = UInt256.ofNat 1931 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1330) = UInt256.ofNat 1931
  rw [inline19_instructionPC]

theorem inline20_slice :
    (Artifact.submissionArtifact.instructions.drop 1376).take PairedAllInlineCoreTrace.inline20Template.length = PairedAllInlineCoreTrace.inline20Template := by
  rfl

theorem inline20_instructionPC :
    Artifact.submissionArtifact.instructionPC 1376 = 1983 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline20Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline20Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline20Template 1376 inline20_slice
    (by
      change 1376 + PairedAllInlineCoreTrace.inline20Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline20Template) (by decide))
    (by decide)

theorem inline20Site_startPC : inline20Site.startPC = UInt256.ofNat 1983 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1376) = UInt256.ofNat 1983
  rw [inline20_instructionPC]

theorem inline21_slice :
    (Artifact.submissionArtifact.instructions.drop 1420).take PairedAllInlineCoreTrace.inline21Template.length = PairedAllInlineCoreTrace.inline21Template := by
  rfl

theorem inline21_instructionPC :
    Artifact.submissionArtifact.instructionPC 1420 = 2032 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline21Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline21Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline21Template 1420 inline21_slice
    (by
      change 1420 + PairedAllInlineCoreTrace.inline21Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline21Template) (by decide))
    (by decide)

theorem inline21Site_startPC : inline21Site.startPC = UInt256.ofNat 2032 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1420) = UInt256.ofNat 2032
  rw [inline21_instructionPC]

theorem inline22_slice :
    (Artifact.submissionArtifact.instructions.drop 1464).take PairedAllInlineCoreTrace.inline22Template.length = PairedAllInlineCoreTrace.inline22Template := by
  rfl

theorem inline22_instructionPC :
    Artifact.submissionArtifact.instructionPC 1464 = 2082 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline22Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline22Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline22Template 1464 inline22_slice
    (by
      change 1464 + PairedAllInlineCoreTrace.inline22Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline22Template) (by decide))
    (by decide)

theorem inline22Site_startPC : inline22Site.startPC = UInt256.ofNat 2082 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1464) = UInt256.ofNat 2082
  rw [inline22_instructionPC]

theorem inline23_slice :
    (Artifact.submissionArtifact.instructions.drop 1510).take PairedAllInlineCoreTrace.inline23Template.length = PairedAllInlineCoreTrace.inline23Template := by
  rfl

theorem inline23_instructionPC :
    Artifact.submissionArtifact.instructionPC 1510 = 2135 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline23Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline23Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline23Template 1510 inline23_slice
    (by
      change 1510 + PairedAllInlineCoreTrace.inline23Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline23Template) (by decide))
    (by decide)

theorem inline23Site_startPC : inline23Site.startPC = UInt256.ofNat 2135 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1510) = UInt256.ofNat 2135
  rw [inline23_instructionPC]

theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1556).take PairedAllInlineCoreTrace.inline24Template.length = PairedAllInlineCoreTrace.inline24Template := by
  rfl

theorem inline24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1556 = 2188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline24Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline24Template 1556 inline24_slice
    (by
      change 1556 + PairedAllInlineCoreTrace.inline24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline24Template) (by decide))
    (by decide)

theorem inline24Site_startPC : inline24Site.startPC = UInt256.ofNat 2188 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1556) = UInt256.ofNat 2188
  rw [inline24_instructionPC]

theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1596).take PairedAllInlineCoreTrace.inline25Template.length = PairedAllInlineCoreTrace.inline25Template := by
  rfl

theorem inline25_instructionPC :
    Artifact.submissionArtifact.instructionPC 1596 = 2234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline25Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline25Template 1596 inline25_slice
    (by
      change 1596 + PairedAllInlineCoreTrace.inline25Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline25Template) (by decide))
    (by decide)

theorem inline25Site_startPC : inline25Site.startPC = UInt256.ofNat 2234 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1596) = UInt256.ofNat 2234
  rw [inline25_instructionPC]

theorem inline26_slice :
    (Artifact.submissionArtifact.instructions.drop 1642).take PairedAllInlineCoreTrace.inline26Template.length = PairedAllInlineCoreTrace.inline26Template := by
  rfl

theorem inline26_instructionPC :
    Artifact.submissionArtifact.instructionPC 1642 = 2286 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline26Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline26Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline26Template 1642 inline26_slice
    (by
      change 1642 + PairedAllInlineCoreTrace.inline26Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline26Template) (by decide))
    (by decide)

theorem inline26Site_startPC : inline26Site.startPC = UInt256.ofNat 2286 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1642) = UInt256.ofNat 2286
  rw [inline26_instructionPC]

theorem inline27_slice :
    (Artifact.submissionArtifact.instructions.drop 1688).take PairedAllInlineCoreTrace.inline27Template.length = PairedAllInlineCoreTrace.inline27Template := by
  rfl

theorem inline27_instructionPC :
    Artifact.submissionArtifact.instructionPC 1688 = 2339 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline27Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline27Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline27Template 1688 inline27_slice
    (by
      change 1688 + PairedAllInlineCoreTrace.inline27Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline27Template) (by decide))
    (by decide)

theorem inline27Site_startPC : inline27Site.startPC = UInt256.ofNat 2339 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1688) = UInt256.ofNat 2339
  rw [inline27_instructionPC]

theorem inline28_slice :
    (Artifact.submissionArtifact.instructions.drop 1734).take PairedAllInlineNewPairs.inline28Template.length = PairedAllInlineNewPairs.inline28Template := by
  rfl

theorem inline28_instructionPC :
    Artifact.submissionArtifact.instructionPC 1734 = 2392 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline28Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline28Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline28Template 1734 inline28_slice
    (by
      change 1734 + PairedAllInlineNewPairs.inline28Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline28Template) (by decide))
    (by decide)

theorem inline28Site_startPC : inline28Site.startPC = UInt256.ofNat 2392 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1734) = UInt256.ofNat 2392
  rw [inline28_instructionPC]

theorem inline29_slice :
    (Artifact.submissionArtifact.instructions.drop 1780).take PairedAllInlineNewPairs.inline29Template.length = PairedAllInlineNewPairs.inline29Template := by
  rfl

theorem inline29_instructionPC :
    Artifact.submissionArtifact.instructionPC 1780 = 2445 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline29Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline29Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline29Template 1780 inline29_slice
    (by
      change 1780 + PairedAllInlineNewPairs.inline29Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline29Template) (by decide))
    (by decide)

theorem inline29Site_startPC : inline29Site.startPC = UInt256.ofNat 2445 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1780) = UInt256.ofNat 2445
  rw [inline29_instructionPC]

theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1826).take PairedAllInlineCoreTrace.inline30Template.length = PairedAllInlineCoreTrace.inline30Template := by
  rfl

theorem inline30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1826 = 2498 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline30Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline30Template 1826 inline30_slice
    (by
      change 1826 + PairedAllInlineCoreTrace.inline30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline30Template) (by decide))
    (by decide)

theorem inline30Site_startPC : inline30Site.startPC = UInt256.ofNat 2498 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1826) = UInt256.ofNat 2498
  rw [inline30_instructionPC]

theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1866).take PairedAllInlineCoreTrace.inline31Template.length = PairedAllInlineCoreTrace.inline31Template := by
  rfl

theorem inline31_instructionPC :
    Artifact.submissionArtifact.instructionPC 1866 = 2543 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline31Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline31Template 1866 inline31_slice
    (by
      change 1866 + PairedAllInlineCoreTrace.inline31Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline31Template) (by decide))
    (by decide)

theorem inline31Site_startPC : inline31Site.startPC = UInt256.ofNat 2543 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1866) = UInt256.ofNat 2543
  rw [inline31_instructionPC]

theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1910).take PairedAllInlineCoreTrace.group32Template.length = PairedAllInlineCoreTrace.group32Template := by
  rfl

theorem group32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1910 = 2593 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group32Template 1910 group32_slice
    (by
      change 1910 + PairedAllInlineCoreTrace.group32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group32Template) (by decide))
    (by decide)

theorem group32Site_startPC : group32Site.startPC = UInt256.ofNat 2593 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1910) = UInt256.ofNat 2593
  rw [group32_instructionPC]

theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1913).take PairedAllInlineCoreTrace.inline32Template.length = PairedAllInlineCoreTrace.inline32Template := by
  rfl

theorem inline32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1913 = 2617 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline32Template 1913 inline32_slice
    (by
      change 1913 + PairedAllInlineCoreTrace.inline32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline32Template) (by decide))
    (by decide)

theorem inline32Site_startPC : inline32Site.startPC = UInt256.ofNat 2617 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1913) = UInt256.ofNat 2617
  rw [inline32_instructionPC]

theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 1952).take PairedAllInlineCoreTrace.inline33Template.length = PairedAllInlineCoreTrace.inline33Template := by
  rfl

theorem inline33_instructionPC :
    Artifact.submissionArtifact.instructionPC 1952 = 2663 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline33Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline33Template 1952 inline33_slice
    (by
      change 1952 + PairedAllInlineCoreTrace.inline33Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline33Template) (by decide))
    (by decide)

theorem inline33Site_startPC : inline33Site.startPC = UInt256.ofNat 2663 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1952) = UInt256.ofNat 2663
  rw [inline33_instructionPC]

theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 1991).take PairedAllInlineCoreTrace.inline34Template.length = PairedAllInlineCoreTrace.inline34Template := by
  rfl

theorem inline34_instructionPC :
    Artifact.submissionArtifact.instructionPC 1991 = 2709 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline34Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline34Template 1991 inline34_slice
    (by
      change 1991 + PairedAllInlineCoreTrace.inline34Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline34Template) (by decide))
    (by decide)

theorem inline34Site_startPC : inline34Site.startPC = UInt256.ofNat 2709 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1991) = UInt256.ofNat 2709
  rw [inline34_instructionPC]

theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 2030).take PairedAllInlineCoreTrace.inline35Template.length = PairedAllInlineCoreTrace.inline35Template := by
  rfl

theorem inline35_instructionPC :
    Artifact.submissionArtifact.instructionPC 2030 = 2755 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline35Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline35Template 2030 inline35_slice
    (by
      change 2030 + PairedAllInlineCoreTrace.inline35Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline35Template) (by decide))
    (by decide)

theorem inline35Site_startPC : inline35Site.startPC = UInt256.ofNat 2755 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2030) = UInt256.ofNat 2755
  rw [inline35_instructionPC]

theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 2069).take PairedAllInlineCoreTrace.inline36Template.length = PairedAllInlineCoreTrace.inline36Template := by
  rfl

theorem inline36_instructionPC :
    Artifact.submissionArtifact.instructionPC 2069 = 2801 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline36Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline36Template 2069 inline36_slice
    (by
      change 2069 + PairedAllInlineCoreTrace.inline36Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline36Template) (by decide))
    (by decide)

theorem inline36Site_startPC : inline36Site.startPC = UInt256.ofNat 2801 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2069) = UInt256.ofNat 2801
  rw [inline36_instructionPC]

theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 2108).take PairedAllInlineCoreTrace.inline37Template.length = PairedAllInlineCoreTrace.inline37Template := by
  rfl

theorem inline37_instructionPC :
    Artifact.submissionArtifact.instructionPC 2108 = 2847 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline37Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline37Template 2108 inline37_slice
    (by
      change 2108 + PairedAllInlineCoreTrace.inline37Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline37Template) (by decide))
    (by decide)

theorem inline37Site_startPC : inline37Site.startPC = UInt256.ofNat 2847 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2108) = UInt256.ofNat 2847
  rw [inline37_instructionPC]

theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 2147).take PairedAllInlineCoreTrace.inline38Template.length = PairedAllInlineCoreTrace.inline38Template := by
  rfl

theorem inline38_instructionPC :
    Artifact.submissionArtifact.instructionPC 2147 = 2893 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline38Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline38Template 2147 inline38_slice
    (by
      change 2147 + PairedAllInlineCoreTrace.inline38Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline38Template) (by decide))
    (by decide)

theorem inline38Site_startPC : inline38Site.startPC = UInt256.ofNat 2893 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2147) = UInt256.ofNat 2893
  rw [inline38_instructionPC]

theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 2186).take PairedAllInlineCoreTrace.inline39Template.length = PairedAllInlineCoreTrace.inline39Template := by
  rfl

theorem inline39_instructionPC :
    Artifact.submissionArtifact.instructionPC 2186 = 2939 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline39Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline39Template 2186 inline39_slice
    (by
      change 2186 + PairedAllInlineCoreTrace.inline39Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline39Template) (by decide))
    (by decide)

theorem inline39Site_startPC : inline39Site.startPC = UInt256.ofNat 2939 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2186) = UInt256.ofNat 2939
  rw [inline39_instructionPC]

theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 2223).take PairedAllInlineCoreTrace.inline40Template.length = PairedAllInlineCoreTrace.inline40Template := by
  rfl

theorem inline40_instructionPC :
    Artifact.submissionArtifact.instructionPC 2223 = 2981 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline40Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline40Template 2223 inline40_slice
    (by
      change 2223 + PairedAllInlineCoreTrace.inline40Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline40Template) (by decide))
    (by decide)

theorem inline40Site_startPC : inline40Site.startPC = UInt256.ofNat 2981 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2223) = UInt256.ofNat 2981
  rw [inline40_instructionPC]

theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2262).take PairedAllInlineCoreTrace.inline41Template.length = PairedAllInlineCoreTrace.inline41Template := by
  rfl

theorem inline41_instructionPC :
    Artifact.submissionArtifact.instructionPC 2262 = 3027 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline41Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline41Template 2262 inline41_slice
    (by
      change 2262 + PairedAllInlineCoreTrace.inline41Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline41Template) (by decide))
    (by decide)

theorem inline41Site_startPC : inline41Site.startPC = UInt256.ofNat 3027 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2262) = UInt256.ofNat 3027
  rw [inline41_instructionPC]

theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2301).take PairedAllInlineCoreTrace.inline42Template.length = PairedAllInlineCoreTrace.inline42Template := by
  rfl

theorem inline42_instructionPC :
    Artifact.submissionArtifact.instructionPC 2301 = 3073 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline42Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline42Template 2301 inline42_slice
    (by
      change 2301 + PairedAllInlineCoreTrace.inline42Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline42Template) (by decide))
    (by decide)

theorem inline42Site_startPC : inline42Site.startPC = UInt256.ofNat 3073 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2301) = UInt256.ofNat 3073
  rw [inline42_instructionPC]

theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2340).take PairedAllInlineCoreTrace.inline43Template.length = PairedAllInlineCoreTrace.inline43Template := by
  rfl

theorem inline43_instructionPC :
    Artifact.submissionArtifact.instructionPC 2340 = 3118 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline43Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline43Template 2340 inline43_slice
    (by
      change 2340 + PairedAllInlineCoreTrace.inline43Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline43Template) (by decide))
    (by decide)

theorem inline43Site_startPC : inline43Site.startPC = UInt256.ofNat 3118 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2340) = UInt256.ofNat 3118
  rw [inline43_instructionPC]

theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2379).take PairedAllInlineCoreTrace.inline44Template.length = PairedAllInlineCoreTrace.inline44Template := by
  rfl

theorem inline44_instructionPC :
    Artifact.submissionArtifact.instructionPC 2379 = 3164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline44Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline44Template 2379 inline44_slice
    (by
      change 2379 + PairedAllInlineCoreTrace.inline44Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline44Template) (by decide))
    (by decide)

theorem inline44Site_startPC : inline44Site.startPC = UInt256.ofNat 3164 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2379) = UInt256.ofNat 3164
  rw [inline44_instructionPC]

theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2418).take PairedAllInlineCoreTrace.inline45Template.length = PairedAllInlineCoreTrace.inline45Template := by
  rfl

theorem inline45_instructionPC :
    Artifact.submissionArtifact.instructionPC 2418 = 3210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline45Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline45Template 2418 inline45_slice
    (by
      change 2418 + PairedAllInlineCoreTrace.inline45Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline45Template) (by decide))
    (by decide)

theorem inline45Site_startPC : inline45Site.startPC = UInt256.ofNat 3210 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2418) = UInt256.ofNat 3210
  rw [inline45_instructionPC]

theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2455).take PairedAllInlineCoreTrace.inline46Template.length = PairedAllInlineCoreTrace.inline46Template := by
  rfl

theorem inline46_instructionPC :
    Artifact.submissionArtifact.instructionPC 2455 = 3252 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline46Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline46Template 2455 inline46_slice
    (by
      change 2455 + PairedAllInlineCoreTrace.inline46Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline46Template) (by decide))
    (by decide)

theorem inline46Site_startPC : inline46Site.startPC = UInt256.ofNat 3252 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2455) = UInt256.ofNat 3252
  rw [inline46_instructionPC]

theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2488).take PairedAllInlineCoreTrace.inline47Template.length = PairedAllInlineCoreTrace.inline47Template := by
  rfl

theorem inline47_instructionPC :
    Artifact.submissionArtifact.instructionPC 2488 = 3291 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline47Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline47Template 2488 inline47_slice
    (by
      change 2488 + PairedAllInlineCoreTrace.inline47Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline47Template) (by decide))
    (by decide)

theorem inline47Site_startPC : inline47Site.startPC = UInt256.ofNat 3291 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2488) = UInt256.ofNat 3291
  rw [inline47_instructionPC]

theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2521).take PairedAllInlineCoreTrace.group48Template.length = PairedAllInlineCoreTrace.group48Template := by
  rfl

theorem group48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2521 = 3330 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group48Template 2521 group48_slice
    (by
      change 2521 + PairedAllInlineCoreTrace.group48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group48Template) (by decide))
    (by decide)

theorem group48Site_startPC : group48Site.startPC = UInt256.ofNat 3330 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2521) = UInt256.ofNat 3330
  rw [group48_instructionPC]

theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2524).take PairedAllInlineCoreTrace.inline48Template.length = PairedAllInlineCoreTrace.inline48Template := by
  rfl

theorem inline48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2524 = 3353 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline48Template 2524 inline48_slice
    (by
      change 2524 + PairedAllInlineCoreTrace.inline48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline48Template) (by decide))
    (by decide)

theorem inline48Site_startPC : inline48Site.startPC = UInt256.ofNat 3353 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2524) = UInt256.ofNat 3353
  rw [inline48_instructionPC]

theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2570).take PairedAllInlineCoreTrace.inline49Template.length = PairedAllInlineCoreTrace.inline49Template := by
  rfl

theorem inline49_instructionPC :
    Artifact.submissionArtifact.instructionPC 2570 = 3405 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline49Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline49Template 2570 inline49_slice
    (by
      change 2570 + PairedAllInlineCoreTrace.inline49Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline49Template) (by decide))
    (by decide)

theorem inline49Site_startPC : inline49Site.startPC = UInt256.ofNat 3405 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2570) = UInt256.ofNat 3405
  rw [inline49_instructionPC]

theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2616).take PairedAllInlineCoreTrace.inline50Template.length = PairedAllInlineCoreTrace.inline50Template := by
  rfl

theorem inline50_instructionPC :
    Artifact.submissionArtifact.instructionPC 2616 = 3458 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline50Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline50Template 2616 inline50_slice
    (by
      change 2616 + PairedAllInlineCoreTrace.inline50Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline50Template) (by decide))
    (by decide)

theorem inline50Site_startPC : inline50Site.startPC = UInt256.ofNat 3458 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2616) = UInt256.ofNat 3458
  rw [inline50_instructionPC]

theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2662).take PairedAllInlineCoreTrace.inline51Template.length = PairedAllInlineCoreTrace.inline51Template := by
  rfl

theorem inline51_instructionPC :
    Artifact.submissionArtifact.instructionPC 2662 = 3511 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline51Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline51Template 2662 inline51_slice
    (by
      change 2662 + PairedAllInlineCoreTrace.inline51Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline51Template) (by decide))
    (by decide)

theorem inline51Site_startPC : inline51Site.startPC = UInt256.ofNat 3511 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2662) = UInt256.ofNat 3511
  rw [inline51_instructionPC]

theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2708).take PairedAllInlineCoreTrace.inline52Template.length = PairedAllInlineCoreTrace.inline52Template := by
  rfl

theorem inline52_instructionPC :
    Artifact.submissionArtifact.instructionPC 2708 = 3563 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline52Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline52Template 2708 inline52_slice
    (by
      change 2708 + PairedAllInlineCoreTrace.inline52Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline52Template) (by decide))
    (by decide)

theorem inline52Site_startPC : inline52Site.startPC = UInt256.ofNat 3563 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2708) = UInt256.ofNat 3563
  rw [inline52_instructionPC]

theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2748).take PairedAllInlineCoreTrace.inline53Template.length = PairedAllInlineCoreTrace.inline53Template := by
  rfl

theorem inline53_instructionPC :
    Artifact.submissionArtifact.instructionPC 2748 = 3608 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline53Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline53Template 2748 inline53_slice
    (by
      change 2748 + PairedAllInlineCoreTrace.inline53Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline53Template) (by decide))
    (by decide)

theorem inline53Site_startPC : inline53Site.startPC = UInt256.ofNat 3608 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2748) = UInt256.ofNat 3608
  rw [inline53_instructionPC]

theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2792).take PairedAllInlineCoreTrace.inline54Template.length = PairedAllInlineCoreTrace.inline54Template := by
  rfl

theorem inline54_instructionPC :
    Artifact.submissionArtifact.instructionPC 2792 = 3658 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline54Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline54Template 2792 inline54_slice
    (by
      change 2792 + PairedAllInlineCoreTrace.inline54Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline54Template) (by decide))
    (by decide)

theorem inline54Site_startPC : inline54Site.startPC = UInt256.ofNat 3658 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2792) = UInt256.ofNat 3658
  rw [inline54_instructionPC]

theorem inline55_slice :
    (Artifact.submissionArtifact.instructions.drop 2838).take PairedAllInlineCoreTrace.inline55Template.length = PairedAllInlineCoreTrace.inline55Template := by
  rfl

theorem inline55_instructionPC :
    Artifact.submissionArtifact.instructionPC 2838 = 3711 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline55Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline55Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline55Template 2838 inline55_slice
    (by
      change 2838 + PairedAllInlineCoreTrace.inline55Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline55Template) (by decide))
    (by decide)

theorem inline55Site_startPC : inline55Site.startPC = UInt256.ofNat 3711 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2838) = UInt256.ofNat 3711
  rw [inline55_instructionPC]

theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 2884).take PairedAllInlineCoreTrace.inline56Template.length = PairedAllInlineCoreTrace.inline56Template := by
  rfl

theorem inline56_instructionPC :
    Artifact.submissionArtifact.instructionPC 2884 = 3763 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline56Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline56Template 2884 inline56_slice
    (by
      change 2884 + PairedAllInlineCoreTrace.inline56Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline56Template) (by decide))
    (by decide)

theorem inline56Site_startPC : inline56Site.startPC = UInt256.ofNat 3763 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2884) = UInt256.ofNat 3763
  rw [inline56_instructionPC]

theorem inline57_slice :
    (Artifact.submissionArtifact.instructions.drop 2930).take PairedAllInlineCoreTrace.inline57Template.length = PairedAllInlineCoreTrace.inline57Template := by
  rfl

theorem inline57_instructionPC :
    Artifact.submissionArtifact.instructionPC 2930 = 3816 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline57Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline57Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline57Template 2930 inline57_slice
    (by
      change 2930 + PairedAllInlineCoreTrace.inline57Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline57Template) (by decide))
    (by decide)

theorem inline57Site_startPC : inline57Site.startPC = UInt256.ofNat 3816 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2930) = UInt256.ofNat 3816
  rw [inline57_instructionPC]

theorem inline58_slice :
    (Artifact.submissionArtifact.instructions.drop 2976).take PairedAllInlineCoreTrace.inline58Template.length = PairedAllInlineCoreTrace.inline58Template := by
  rfl

theorem inline58_instructionPC :
    Artifact.submissionArtifact.instructionPC 2976 = 3869 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline58Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline58Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline58Template 2976 inline58_slice
    (by
      change 2976 + PairedAllInlineCoreTrace.inline58Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline58Template) (by decide))
    (by decide)

theorem inline58Site_startPC : inline58Site.startPC = UInt256.ofNat 3869 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2976) = UInt256.ofNat 3869
  rw [inline58_instructionPC]

theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 3022).take PairedAllInlineCoreTrace.inline59Template.length = PairedAllInlineCoreTrace.inline59Template := by
  rfl

theorem inline59_instructionPC :
    Artifact.submissionArtifact.instructionPC 3022 = 3922 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline59Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline59Template 3022 inline59_slice
    (by
      change 3022 + PairedAllInlineCoreTrace.inline59Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline59Template) (by decide))
    (by decide)

theorem inline59Site_startPC : inline59Site.startPC = UInt256.ofNat 3922 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3022) = UInt256.ofNat 3922
  rw [inline59_instructionPC]

theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 3068).take PairedAllInlineCoreTrace.inline60Template.length = PairedAllInlineCoreTrace.inline60Template := by
  rfl

theorem inline60_instructionPC :
    Artifact.submissionArtifact.instructionPC 3068 = 3975 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline60Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline60Template 3068 inline60_slice
    (by
      change 3068 + PairedAllInlineCoreTrace.inline60Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline60Template) (by decide))
    (by decide)

theorem inline60Site_startPC : inline60Site.startPC = UInt256.ofNat 3975 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3068) = UInt256.ofNat 3975
  rw [inline60_instructionPC]

theorem inline61_slice :
    (Artifact.submissionArtifact.instructions.drop 3114).take PairedAllInlineCoreTrace.inline61Template.length = PairedAllInlineCoreTrace.inline61Template := by
  rfl

theorem inline61_instructionPC :
    Artifact.submissionArtifact.instructionPC 3114 = 4028 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline61Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline61Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline61Template 3114 inline61_slice
    (by
      change 3114 + PairedAllInlineCoreTrace.inline61Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline61Template) (by decide))
    (by decide)

theorem inline61Site_startPC : inline61Site.startPC = UInt256.ofNat 4028 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3114) = UInt256.ofNat 4028
  rw [inline61_instructionPC]

theorem inline62_slice :
    (Artifact.submissionArtifact.instructions.drop 3158).take PairedAllInlineCoreTrace.inline62Template.length = PairedAllInlineCoreTrace.inline62Template := by
  rfl

theorem inline62_instructionPC :
    Artifact.submissionArtifact.instructionPC 3158 = 4078 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline62Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline62Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline62Template 3158 inline62_slice
    (by
      change 3158 + PairedAllInlineCoreTrace.inline62Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline62Template) (by decide))
    (by decide)

theorem inline62Site_startPC : inline62Site.startPC = UInt256.ofNat 4078 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3158) = UInt256.ofNat 4078
  rw [inline62_instructionPC]

theorem inline63_slice :
    (Artifact.submissionArtifact.instructions.drop 3204).take PairedAllInlineCoreTrace.inline63Template.length = PairedAllInlineCoreTrace.inline63Template := by
  rfl

theorem inline63_instructionPC :
    Artifact.submissionArtifact.instructionPC 3204 = 4132 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline63Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline63Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline63Template 3204 inline63_slice
    (by
      change 3204 + PairedAllInlineCoreTrace.inline63Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline63Template) (by decide))
    (by decide)

theorem inline63Site_startPC : inline63Site.startPC = UInt256.ofNat 4132 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3204) = UInt256.ofNat 4132
  rw [inline63_instructionPC]

theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3250).take PairedAllInlineCoreTrace.group64Template.length = PairedAllInlineCoreTrace.group64Template := by
  rfl

theorem group64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3250 = 4185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group64Template 3250 group64_slice
    (by
      change 3250 + PairedAllInlineCoreTrace.group64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group64Template) (by decide))
    (by decide)

theorem group64Site_startPC : group64Site.startPC = UInt256.ofNat 4185 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3250) = UInt256.ofNat 4185
  rw [group64_instructionPC]

theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3253).take PairedAllInlineCoreTrace.inline64Template.length = PairedAllInlineCoreTrace.inline64Template := by
  rfl

theorem inline64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3253 = 4192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline64Template 3253 inline64_slice
    (by
      change 3253 + PairedAllInlineCoreTrace.inline64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline64Template) (by decide))
    (by decide)

theorem inline64Site_startPC : inline64Site.startPC = UInt256.ofNat 4192 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3253) = UInt256.ofNat 4192
  rw [inline64_instructionPC]

theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3295).take PairedAllInlineCoreTrace.inline65Template.length = PairedAllInlineCoreTrace.inline65Template := by
  rfl

theorem inline65_instructionPC :
    Artifact.submissionArtifact.instructionPC 3295 = 4240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline65Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline65Template 3295 inline65_slice
    (by
      change 3295 + PairedAllInlineCoreTrace.inline65Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline65Template) (by decide))
    (by decide)

theorem inline65Site_startPC : inline65Site.startPC = UInt256.ofNat 4240 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3295) = UInt256.ofNat 4240
  rw [inline65_instructionPC]

theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3339).take PairedAllInlineCoreTrace.inline66Template.length = PairedAllInlineCoreTrace.inline66Template := by
  rfl

theorem inline66_instructionPC :
    Artifact.submissionArtifact.instructionPC 3339 = 4291 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline66Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline66Template 3339 inline66_slice
    (by
      change 3339 + PairedAllInlineCoreTrace.inline66Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline66Template) (by decide))
    (by decide)

theorem inline66Site_startPC : inline66Site.startPC = UInt256.ofNat 4291 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3339) = UInt256.ofNat 4291
  rw [inline66_instructionPC]

theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3383).take PairedAllInlineCoreTrace.inline67Template.length = PairedAllInlineCoreTrace.inline67Template := by
  rfl

theorem inline67_instructionPC :
    Artifact.submissionArtifact.instructionPC 3383 = 4342 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline67Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline67Template 3383 inline67_slice
    (by
      change 3383 + PairedAllInlineCoreTrace.inline67Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline67Template) (by decide))
    (by decide)

theorem inline67Site_startPC : inline67Site.startPC = UInt256.ofNat 4342 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3383) = UInt256.ofNat 4342
  rw [inline67_instructionPC]

theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3427).take PairedAllInlineCoreTrace.inline68Template.length = PairedAllInlineCoreTrace.inline68Template := by
  rfl

theorem inline68_instructionPC :
    Artifact.submissionArtifact.instructionPC 3427 = 4393 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline68Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline68Template 3427 inline68_slice
    (by
      change 3427 + PairedAllInlineCoreTrace.inline68Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline68Template) (by decide))
    (by decide)

theorem inline68Site_startPC : inline68Site.startPC = UInt256.ofNat 4393 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3427) = UInt256.ofNat 4393
  rw [inline68_instructionPC]

theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3471).take PairedAllInlineCoreTrace.inline69Template.length = PairedAllInlineCoreTrace.inline69Template := by
  rfl

theorem inline69_instructionPC :
    Artifact.submissionArtifact.instructionPC 3471 = 4443 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline69Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline69Template 3471 inline69_slice
    (by
      change 3471 + PairedAllInlineCoreTrace.inline69Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline69Template) (by decide))
    (by decide)

theorem inline69Site_startPC : inline69Site.startPC = UInt256.ofNat 4443 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3471) = UInt256.ofNat 4443
  rw [inline69_instructionPC]

theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3515).take PairedAllInlineCoreTrace.inline70Template.length = PairedAllInlineCoreTrace.inline70Template := by
  rfl

theorem inline70_instructionPC :
    Artifact.submissionArtifact.instructionPC 3515 = 4494 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline70Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline70Template 3515 inline70_slice
    (by
      change 3515 + PairedAllInlineCoreTrace.inline70Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline70Template) (by decide))
    (by decide)

theorem inline70Site_startPC : inline70Site.startPC = UInt256.ofNat 4494 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3515) = UInt256.ofNat 4494
  rw [inline70_instructionPC]

theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3557).take PairedAllInlineCoreTrace.inline71Template.length = PairedAllInlineCoreTrace.inline71Template := by
  rfl

theorem inline71_instructionPC :
    Artifact.submissionArtifact.instructionPC 3557 = 4542 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline71Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline71Template 3557 inline71_slice
    (by
      change 3557 + PairedAllInlineCoreTrace.inline71Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline71Template) (by decide))
    (by decide)

theorem inline71Site_startPC : inline71Site.startPC = UInt256.ofNat 4542 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3557) = UInt256.ofNat 4542
  rw [inline71_instructionPC]

theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3601).take PairedAllInlineCoreTrace.inline72Template.length = PairedAllInlineCoreTrace.inline72Template := by
  rfl

theorem inline72_instructionPC :
    Artifact.submissionArtifact.instructionPC 3601 = 4593 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline72Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline72Template 3601 inline72_slice
    (by
      change 3601 + PairedAllInlineCoreTrace.inline72Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline72Template) (by decide))
    (by decide)

theorem inline72Site_startPC : inline72Site.startPC = UInt256.ofNat 4593 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3601) = UInt256.ofNat 4593
  rw [inline72_instructionPC]

theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3645).take PairedAllInlineCoreTrace.inline73Template.length = PairedAllInlineCoreTrace.inline73Template := by
  rfl

theorem inline73_instructionPC :
    Artifact.submissionArtifact.instructionPC 3645 = 4644 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline73Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline73Template 3645 inline73_slice
    (by
      change 3645 + PairedAllInlineCoreTrace.inline73Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline73Template) (by decide))
    (by decide)

theorem inline73Site_startPC : inline73Site.startPC = UInt256.ofNat 4644 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3645) = UInt256.ofNat 4644
  rw [inline73_instructionPC]

theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3687).take PairedAllInlineCoreTrace.inline74Template.length = PairedAllInlineCoreTrace.inline74Template := by
  rfl

theorem inline74_instructionPC :
    Artifact.submissionArtifact.instructionPC 3687 = 4691 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline74Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline74Template 3687 inline74_slice
    (by
      change 3687 + PairedAllInlineCoreTrace.inline74Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline74Template) (by decide))
    (by decide)

theorem inline74Site_startPC : inline74Site.startPC = UInt256.ofNat 4691 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3687) = UInt256.ofNat 4691
  rw [inline74_instructionPC]

theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3731).take PairedAllInlineCoreTrace.inline75Template.length = PairedAllInlineCoreTrace.inline75Template := by
  rfl

theorem inline75_instructionPC :
    Artifact.submissionArtifact.instructionPC 3731 = 4742 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline75Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline75Template 3731 inline75_slice
    (by
      change 3731 + PairedAllInlineCoreTrace.inline75Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline75Template) (by decide))
    (by decide)

theorem inline75Site_startPC : inline75Site.startPC = UInt256.ofNat 4742 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3731) = UInt256.ofNat 4742
  rw [inline75_instructionPC]

theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3775).take PairedAllInlineCoreTrace.inline76Template.length = PairedAllInlineCoreTrace.inline76Template := by
  rfl

theorem inline76_instructionPC :
    Artifact.submissionArtifact.instructionPC 3775 = 4794 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline76Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline76Template 3775 inline76_slice
    (by
      change 3775 + PairedAllInlineCoreTrace.inline76Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline76Template) (by decide))
    (by decide)

theorem inline76Site_startPC : inline76Site.startPC = UInt256.ofNat 4794 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3775) = UInt256.ofNat 4794
  rw [inline76_instructionPC]

theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 3819).take PairedAllInlineCoreTrace.inline77Template.length = PairedAllInlineCoreTrace.inline77Template := by
  rfl

theorem inline77_instructionPC :
    Artifact.submissionArtifact.instructionPC 3819 = 4844 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline77Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline77Template 3819 inline77_slice
    (by
      change 3819 + PairedAllInlineCoreTrace.inline77Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline77Template) (by decide))
    (by decide)

theorem inline77Site_startPC : inline77Site.startPC = UInt256.ofNat 4844 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3819) = UInt256.ofNat 4844
  rw [inline77_instructionPC]

theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3863).take PairedAllInlineCoreTrace.inline78Template.length = PairedAllInlineCoreTrace.inline78Template := by
  rfl

theorem inline78_instructionPC :
    Artifact.submissionArtifact.instructionPC 3863 = 4895 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline78Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline78Template 3863 inline78_slice
    (by
      change 3863 + PairedAllInlineCoreTrace.inline78Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline78Template) (by decide))
    (by decide)

theorem inline78Site_startPC : inline78Site.startPC = UInt256.ofNat 4895 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3863) = UInt256.ofNat 4895
  rw [inline78_instructionPC]

def corePrefixSites : PairedAllInlineCoreTrace.CorePrefixSites Artifact.submissionArtifact .Osaka where
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

def gasSteps_core_prefix (s : State) (f : CoreFrame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 919, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f rho}
      {s with
        pc := UInt256.ofNat 4946
        stack := coreStack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower]
          (PairedAllInlineCoreTrace.corePrefixChain.eval s.memory f) rho} :=
  PairedAllInlineCoreTrace.gasSteps_core_prefix corePrefixSites s f rho hstack hrun hactive hcode hfork hnp

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites

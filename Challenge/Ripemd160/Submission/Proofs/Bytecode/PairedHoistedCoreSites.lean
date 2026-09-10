import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHoistedCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHoistedCoreSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate PairedHelperBooleanTrace

/-- Actual instruction windows for the frozen 5334-byte generic paired compressor. -/

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
    (Artifact.submissionArtifact.instructions.drop 469).take PairedHelperBooleanTrace.inline0Template.length = PairedHelperBooleanTrace.inline0Template := by
  rfl

theorem inline0_instructionPC :
    Artifact.submissionArtifact.instructionPC 469 = 981 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline0Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline0Template 469 inline0_slice
    (by
      change 469 + PairedHelperBooleanTrace.inline0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline0Template) (by decide))
    (by decide)

theorem inline0Site_startPC : inline0Site.startPC = UInt256.ofNat 981 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 469) = UInt256.ofNat 981
  rw [inline0_instructionPC]


theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 517).take PairedHelperBooleanTrace.inline1Template.length = PairedHelperBooleanTrace.inline1Template := by
  rfl

theorem inline1_instructionPC :
    Artifact.submissionArtifact.instructionPC 517 = 1035 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline1Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline1Template 517 inline1_slice
    (by
      change 517 + PairedHelperBooleanTrace.inline1Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline1Template) (by decide))
    (by decide)

theorem inline1Site_startPC : inline1Site.startPC = UInt256.ofNat 1035 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 517) = UInt256.ofNat 1035
  rw [inline1_instructionPC]


theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 565).take PairedHelperBooleanTrace.inline2Template.length = PairedHelperBooleanTrace.inline2Template := by
  rfl

theorem inline2_instructionPC :
    Artifact.submissionArtifact.instructionPC 565 = 1089 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline2Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline2Template 565 inline2_slice
    (by
      change 565 + PairedHelperBooleanTrace.inline2Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline2Template) (by decide))
    (by decide)

theorem inline2Site_startPC : inline2Site.startPC = UInt256.ofNat 1089 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 565) = UInt256.ofNat 1089
  rw [inline2_instructionPC]


theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 613).take PairedHelperBooleanTrace.inline3Template.length = PairedHelperBooleanTrace.inline3Template := by
  rfl

theorem inline3_instructionPC :
    Artifact.submissionArtifact.instructionPC 613 = 1144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline3Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline3Template 613 inline3_slice
    (by
      change 613 + PairedHelperBooleanTrace.inline3Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline3Template) (by decide))
    (by decide)

theorem inline3Site_startPC : inline3Site.startPC = UInt256.ofNat 1144 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 613) = UInt256.ofNat 1144
  rw [inline3_instructionPC]


theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 661).take PairedHelperBooleanTrace.inline4Template.length = PairedHelperBooleanTrace.inline4Template := by
  rfl

theorem inline4_instructionPC :
    Artifact.submissionArtifact.instructionPC 661 = 1198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline4Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline4Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline4Template 661 inline4_slice
    (by
      change 661 + PairedHelperBooleanTrace.inline4Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline4Template) (by decide))
    (by decide)

theorem inline4Site_startPC : inline4Site.startPC = UInt256.ofNat 1198 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 661) = UInt256.ofNat 1198
  rw [inline4_instructionPC]


theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 709).take PairedHelperBooleanTrace.inline5Template.length = PairedHelperBooleanTrace.inline5Template := by
  rfl

theorem inline5_instructionPC :
    Artifact.submissionArtifact.instructionPC 709 = 1253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline5Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline5Template 709 inline5_slice
    (by
      change 709 + PairedHelperBooleanTrace.inline5Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline5Template) (by decide))
    (by decide)

theorem inline5Site_startPC : inline5Site.startPC = UInt256.ofNat 1253 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 709) = UInt256.ofNat 1253
  rw [inline5_instructionPC]


theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 757).take PairedHelperBooleanTrace.inline6Template.length = PairedHelperBooleanTrace.inline6Template := by
  rfl

theorem inline6_instructionPC :
    Artifact.submissionArtifact.instructionPC 757 = 1308 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline6Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline6Template 757 inline6_slice
    (by
      change 757 + PairedHelperBooleanTrace.inline6Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline6Template) (by decide))
    (by decide)

theorem inline6Site_startPC : inline6Site.startPC = UInt256.ofNat 1308 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 757) = UInt256.ofNat 1308
  rw [inline6_instructionPC]


theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 805).take PairedHelperBooleanTrace.inline7Template.length = PairedHelperBooleanTrace.inline7Template := by
  rfl

theorem inline7_instructionPC :
    Artifact.submissionArtifact.instructionPC 805 = 1363 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline7Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline7Template 805 inline7_slice
    (by
      change 805 + PairedHelperBooleanTrace.inline7Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline7Template) (by decide))
    (by decide)

theorem inline7Site_startPC : inline7Site.startPC = UInt256.ofNat 1363 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 805) = UInt256.ofNat 1363
  rw [inline7_instructionPC]


theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 853).take PairedHelperBooleanTrace.inline8Template.length = PairedHelperBooleanTrace.inline8Template := by
  rfl

theorem inline8_instructionPC :
    Artifact.submissionArtifact.instructionPC 853 = 1418 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline8Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline8Template 853 inline8_slice
    (by
      change 853 + PairedHelperBooleanTrace.inline8Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline8Template) (by decide))
    (by decide)

theorem inline8Site_startPC : inline8Site.startPC = UInt256.ofNat 1418 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 853) = UInt256.ofNat 1418
  rw [inline8_instructionPC]


theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 901).take PairedHelperBooleanTrace.inline9Template.length = PairedHelperBooleanTrace.inline9Template := by
  rfl

theorem inline9_instructionPC :
    Artifact.submissionArtifact.instructionPC 901 = 1473 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline9Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline9Template 901 inline9_slice
    (by
      change 901 + PairedHelperBooleanTrace.inline9Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline9Template) (by decide))
    (by decide)

theorem inline9Site_startPC : inline9Site.startPC = UInt256.ofNat 1473 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 901) = UInt256.ofNat 1473
  rw [inline9_instructionPC]


theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 949).take PairedHelperBooleanTrace.inline10Template.length = PairedHelperBooleanTrace.inline10Template := by
  rfl

theorem inline10_instructionPC :
    Artifact.submissionArtifact.instructionPC 949 = 1528 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline10Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline10Template 949 inline10_slice
    (by
      change 949 + PairedHelperBooleanTrace.inline10Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline10Template) (by decide))
    (by decide)

theorem inline10Site_startPC : inline10Site.startPC = UInt256.ofNat 1528 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 949) = UInt256.ofNat 1528
  rw [inline10_instructionPC]


theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 997).take PairedHelperBooleanTrace.inline11Template.length = PairedHelperBooleanTrace.inline11Template := by
  rfl

theorem inline11_instructionPC :
    Artifact.submissionArtifact.instructionPC 997 = 1583 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline11Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline11Template 997 inline11_slice
    (by
      change 997 + PairedHelperBooleanTrace.inline11Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline11Template) (by decide))
    (by decide)

theorem inline11Site_startPC : inline11Site.startPC = UInt256.ofNat 1583 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 997) = UInt256.ofNat 1583
  rw [inline11_instructionPC]


theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1045).take PairedHelperBooleanTrace.inline12Template.length = PairedHelperBooleanTrace.inline12Template := by
  rfl

theorem inline12_instructionPC :
    Artifact.submissionArtifact.instructionPC 1045 = 1638 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline12Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline12Template 1045 inline12_slice
    (by
      change 1045 + PairedHelperBooleanTrace.inline12Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline12Template) (by decide))
    (by decide)

theorem inline12Site_startPC : inline12Site.startPC = UInt256.ofNat 1638 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1045) = UInt256.ofNat 1638
  rw [inline12_instructionPC]


theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1093).take PairedHelperBooleanTrace.inline13Template.length = PairedHelperBooleanTrace.inline13Template := by
  rfl

theorem inline13_instructionPC :
    Artifact.submissionArtifact.instructionPC 1093 = 1692 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline13Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline13Template 1093 inline13_slice
    (by
      change 1093 + PairedHelperBooleanTrace.inline13Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline13Template) (by decide))
    (by decide)

theorem inline13Site_startPC : inline13Site.startPC = UInt256.ofNat 1692 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1093) = UInt256.ofNat 1692
  rw [inline13_instructionPC]


theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1141).take PairedHelperBooleanTrace.inline14Template.length = PairedHelperBooleanTrace.inline14Template := by
  rfl

theorem inline14_instructionPC :
    Artifact.submissionArtifact.instructionPC 1141 = 1747 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline14Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline14Template 1141 inline14_slice
    (by
      change 1141 + PairedHelperBooleanTrace.inline14Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline14Template) (by decide))
    (by decide)

theorem inline14Site_startPC : inline14Site.startPC = UInt256.ofNat 1747 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1141) = UInt256.ofNat 1747
  rw [inline14_instructionPC]


theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1189).take PairedHelperBooleanTrace.inline15Template.length = PairedHelperBooleanTrace.inline15Template := by
  rfl

theorem inline15_instructionPC :
    Artifact.submissionArtifact.instructionPC 1189 = 1802 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline15Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline15Template 1189 inline15_slice
    (by
      change 1189 + PairedHelperBooleanTrace.inline15Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline15Template) (by decide))
    (by decide)

theorem inline15Site_startPC : inline15Site.startPC = UInt256.ofNat 1802 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1189) = UInt256.ofNat 1802
  rw [inline15_instructionPC]


theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1237).take PairedHelperBooleanTrace.group16Template.length = PairedHelperBooleanTrace.group16Template := by
  rfl

theorem group16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1237 = 1857 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.group16Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.group16Template 1237 group16_slice
    (by
      change 1237 + PairedHelperBooleanTrace.group16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.group16Template) (by decide))
    (by decide)

theorem group16Site_startPC : group16Site.startPC = UInt256.ofNat 1857 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1237) = UInt256.ofNat 1857
  rw [group16_instructionPC]


theorem call16_slice :
    (Artifact.submissionArtifact.instructions.drop 1240).take PairedHoistedCoreTrace.call16Template.length = PairedHoistedCoreTrace.call16Template := by
  rfl

theorem call16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1240 = 1880 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.call16Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.call16Template 1240 call16_slice
    (by
      change 1240 + PairedHoistedCoreTrace.call16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.call16Template) (by decide))
    (by decide)

theorem call16Site_startPC : call16Site.startPC = UInt256.ofNat 1880 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1240) = UInt256.ofNat 1880
  rw [call16_instructionPC]


theorem return18_slice :
    (Artifact.submissionArtifact.instructions.drop 1264).take PairedHelperBooleanTrace.return18Template.length = PairedHelperBooleanTrace.return18Template := by
  rfl

theorem return18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1264 = 1920 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.return18Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.return18Template 1264 return18_slice
    (by
      change 1264 + PairedHelperBooleanTrace.return18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.return18Template) (by decide))
    (by decide)

theorem return18Site_startPC : return18Site.startPC = UInt256.ofNat 1920 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1264) = UInt256.ofNat 1920
  rw [return18_instructionPC]


theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1265).take PairedHelperBooleanTrace.inline18Template.length = PairedHelperBooleanTrace.inline18Template := by
  rfl

theorem inline18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1265 = 1921 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline18Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline18Template 1265 inline18_slice
    (by
      change 1265 + PairedHelperBooleanTrace.inline18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline18Template) (by decide))
    (by decide)

theorem inline18Site_startPC : inline18Site.startPC = UInt256.ofNat 1921 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1265) = UInt256.ofNat 1921
  rw [inline18_instructionPC]


theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1318).take PairedHelperBooleanTrace.inline19Template.length = PairedHelperBooleanTrace.inline19Template := by
  rfl

theorem inline19_instructionPC :
    Artifact.submissionArtifact.instructionPC 1318 = 1981 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline19Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline19Template 1318 inline19_slice
    (by
      change 1318 + PairedHelperBooleanTrace.inline19Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline19Template) (by decide))
    (by decide)

theorem inline19Site_startPC : inline19Site.startPC = UInt256.ofNat 1981 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1318) = UInt256.ofNat 1981
  rw [inline19_instructionPC]


theorem call20_slice :
    (Artifact.submissionArtifact.instructions.drop 1372).take PairedHoistedCoreTrace.call20Template.length = PairedHoistedCoreTrace.call20Template := by
  rfl

theorem call20_instructionPC :
    Artifact.submissionArtifact.instructionPC 1372 = 2041 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call20Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.call20Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.call20Template 1372 call20_slice
    (by
      change 1372 + PairedHoistedCoreTrace.call20Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.call20Template) (by decide))
    (by decide)

theorem call20Site_startPC : call20Site.startPC = UInt256.ofNat 2041 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1372) = UInt256.ofNat 2041
  rw [call20_instructionPC]


theorem call22_slice :
    (Artifact.submissionArtifact.instructions.drop 1393).take PairedHoistedCoreTrace.call22Template.length = PairedHoistedCoreTrace.call22Template := by
  rfl

theorem call22_instructionPC :
    Artifact.submissionArtifact.instructionPC 1393 = 2077 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call22Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.call22Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.call22Template 1393 call22_slice
    (by
      change 1393 + PairedHoistedCoreTrace.call22Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.call22Template) (by decide))
    (by decide)

theorem call22Site_startPC : call22Site.startPC = UInt256.ofNat 2077 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1393) = UInt256.ofNat 2077
  rw [call22_instructionPC]


theorem return24_slice :
    (Artifact.submissionArtifact.instructions.drop 1416).take PairedHelperBooleanTrace.return24Template.length = PairedHelperBooleanTrace.return24Template := by
  rfl

theorem return24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1416 = 2116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return24Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.return24Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.return24Template 1416 return24_slice
    (by
      change 1416 + PairedHelperBooleanTrace.return24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.return24Template) (by decide))
    (by decide)

theorem return24Site_startPC : return24Site.startPC = UInt256.ofNat 2116 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1416) = UInt256.ofNat 2116
  rw [return24_instructionPC]


theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1417).take PairedHelperBooleanTrace.inline24Template.length = PairedHelperBooleanTrace.inline24Template := by
  rfl

theorem inline24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1417 = 2117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline24Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline24Template 1417 inline24_slice
    (by
      change 1417 + PairedHelperBooleanTrace.inline24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline24Template) (by decide))
    (by decide)

theorem inline24Site_startPC : inline24Site.startPC = UInt256.ofNat 2117 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1417) = UInt256.ofNat 2117
  rw [inline24_instructionPC]


theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1461).take PairedHelperBooleanTrace.inline25Template.length = PairedHelperBooleanTrace.inline25Template := by
  rfl

theorem inline25_instructionPC :
    Artifact.submissionArtifact.instructionPC 1461 = 2167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline25Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline25Template 1461 inline25_slice
    (by
      change 1461 + PairedHelperBooleanTrace.inline25Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline25Template) (by decide))
    (by decide)

theorem inline25Site_startPC : inline25Site.startPC = UInt256.ofNat 2167 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1461) = UInt256.ofNat 2167
  rw [inline25_instructionPC]


theorem call26_slice :
    (Artifact.submissionArtifact.instructions.drop 1515).take PairedHoistedCoreTrace.call26Template.length = PairedHoistedCoreTrace.call26Template := by
  rfl

theorem call26_instructionPC :
    Artifact.submissionArtifact.instructionPC 1515 = 2227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call26Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.call26Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.call26Template 1515 call26_slice
    (by
      change 1515 + PairedHoistedCoreTrace.call26Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.call26Template) (by decide))
    (by decide)

theorem call26Site_startPC : call26Site.startPC = UInt256.ofNat 2227 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1515) = UInt256.ofNat 2227
  rw [call26_instructionPC]


theorem call28_slice :
    (Artifact.submissionArtifact.instructions.drop 1536).take PairedHoistedCoreTrace.call28Template.length = PairedHoistedCoreTrace.call28Template := by
  rfl

theorem call28_instructionPC :
    Artifact.submissionArtifact.instructionPC 1536 = 2264 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call28Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.call28Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.call28Template 1536 call28_slice
    (by
      change 1536 + PairedHoistedCoreTrace.call28Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.call28Template) (by decide))
    (by decide)

theorem call28Site_startPC : call28Site.startPC = UInt256.ofNat 2264 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1536) = UInt256.ofNat 2264
  rw [call28_instructionPC]


theorem return30_slice :
    (Artifact.submissionArtifact.instructions.drop 1559).take PairedHelperBooleanTrace.return30Template.length = PairedHelperBooleanTrace.return30Template := by
  rfl

theorem return30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1559 = 2303 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.return30Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.return30Template 1559 return30_slice
    (by
      change 1559 + PairedHelperBooleanTrace.return30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.return30Template) (by decide))
    (by decide)

theorem return30Site_startPC : return30Site.startPC = UInt256.ofNat 2303 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1559) = UInt256.ofNat 2303
  rw [return30_instructionPC]


theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1560).take PairedHelperBooleanTrace.inline30Template.length = PairedHelperBooleanTrace.inline30Template := by
  rfl

theorem inline30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1560 = 2304 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline30Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline30Template 1560 inline30_slice
    (by
      change 1560 + PairedHelperBooleanTrace.inline30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline30Template) (by decide))
    (by decide)

theorem inline30Site_startPC : inline30Site.startPC = UInt256.ofNat 2304 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1560) = UInt256.ofNat 2304
  rw [inline30_instructionPC]


theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1604).take PairedHelperBooleanTrace.inline31Template.length = PairedHelperBooleanTrace.inline31Template := by
  rfl

theorem inline31_instructionPC :
    Artifact.submissionArtifact.instructionPC 1604 = 2353 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline31Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline31Template 1604 inline31_slice
    (by
      change 1604 + PairedHelperBooleanTrace.inline31Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline31Template) (by decide))
    (by decide)

theorem inline31Site_startPC : inline31Site.startPC = UInt256.ofNat 2353 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1604) = UInt256.ofNat 2353
  rw [inline31_instructionPC]


theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1658).take PairedHoistedCoreTrace.group32Template.length = PairedHoistedCoreTrace.group32Template := by
  rfl

theorem group32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1658 = 2414 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.group32Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.group32Template 1658 group32_slice
    (by
      change 1658 + PairedHoistedCoreTrace.group32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.group32Template) (by decide))
    (by decide)

theorem group32Site_startPC : group32Site.startPC = UInt256.ofNat 2414 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1658) = UInt256.ofNat 2414
  rw [group32_instructionPC]


theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1661).take PairedHoistedCoreTrace.inline32Template.length = PairedHoistedCoreTrace.inline32Template := by
  rfl

theorem inline32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1661 = 2438 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline32Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline32Template 1661 inline32_slice
    (by
      change 1661 + PairedHoistedCoreTrace.inline32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline32Template) (by decide))
    (by decide)

theorem inline32Site_startPC : inline32Site.startPC = UInt256.ofNat 2438 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1661) = UInt256.ofNat 2438
  rw [inline32_instructionPC]


theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 1703).take PairedHoistedCoreTrace.inline33Template.length = PairedHoistedCoreTrace.inline33Template := by
  rfl

theorem inline33_instructionPC :
    Artifact.submissionArtifact.instructionPC 1703 = 2487 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline33Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline33Template 1703 inline33_slice
    (by
      change 1703 + PairedHoistedCoreTrace.inline33Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline33Template) (by decide))
    (by decide)

theorem inline33Site_startPC : inline33Site.startPC = UInt256.ofNat 2487 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1703) = UInt256.ofNat 2487
  rw [inline33_instructionPC]


theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 1745).take PairedHoistedCoreTrace.inline34Template.length = PairedHoistedCoreTrace.inline34Template := by
  rfl

theorem inline34_instructionPC :
    Artifact.submissionArtifact.instructionPC 1745 = 2536 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline34Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline34Template 1745 inline34_slice
    (by
      change 1745 + PairedHoistedCoreTrace.inline34Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline34Template) (by decide))
    (by decide)

theorem inline34Site_startPC : inline34Site.startPC = UInt256.ofNat 2536 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1745) = UInt256.ofNat 2536
  rw [inline34_instructionPC]


theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 1787).take PairedHoistedCoreTrace.inline35Template.length = PairedHoistedCoreTrace.inline35Template := by
  rfl

theorem inline35_instructionPC :
    Artifact.submissionArtifact.instructionPC 1787 = 2584 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline35Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline35Template 1787 inline35_slice
    (by
      change 1787 + PairedHoistedCoreTrace.inline35Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline35Template) (by decide))
    (by decide)

theorem inline35Site_startPC : inline35Site.startPC = UInt256.ofNat 2584 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1787) = UInt256.ofNat 2584
  rw [inline35_instructionPC]


theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 1829).take PairedHoistedCoreTrace.inline36Template.length = PairedHoistedCoreTrace.inline36Template := by
  rfl

theorem inline36_instructionPC :
    Artifact.submissionArtifact.instructionPC 1829 = 2633 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline36Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline36Template 1829 inline36_slice
    (by
      change 1829 + PairedHoistedCoreTrace.inline36Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline36Template) (by decide))
    (by decide)

theorem inline36Site_startPC : inline36Site.startPC = UInt256.ofNat 2633 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1829) = UInt256.ofNat 2633
  rw [inline36_instructionPC]


theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 1871).take PairedHoistedCoreTrace.inline37Template.length = PairedHoistedCoreTrace.inline37Template := by
  rfl

theorem inline37_instructionPC :
    Artifact.submissionArtifact.instructionPC 1871 = 2682 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline37Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline37Template 1871 inline37_slice
    (by
      change 1871 + PairedHoistedCoreTrace.inline37Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline37Template) (by decide))
    (by decide)

theorem inline37Site_startPC : inline37Site.startPC = UInt256.ofNat 2682 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1871) = UInt256.ofNat 2682
  rw [inline37_instructionPC]


theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 1913).take PairedHoistedCoreTrace.inline38Template.length = PairedHoistedCoreTrace.inline38Template := by
  rfl

theorem inline38_instructionPC :
    Artifact.submissionArtifact.instructionPC 1913 = 2731 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline38Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline38Template 1913 inline38_slice
    (by
      change 1913 + PairedHoistedCoreTrace.inline38Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline38Template) (by decide))
    (by decide)

theorem inline38Site_startPC : inline38Site.startPC = UInt256.ofNat 2731 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1913) = UInt256.ofNat 2731
  rw [inline38_instructionPC]


theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 1955).take PairedHoistedCoreTrace.inline39Template.length = PairedHoistedCoreTrace.inline39Template := by
  rfl

theorem inline39_instructionPC :
    Artifact.submissionArtifact.instructionPC 1955 = 2780 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline39Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline39Template 1955 inline39_slice
    (by
      change 1955 + PairedHoistedCoreTrace.inline39Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline39Template) (by decide))
    (by decide)

theorem inline39Site_startPC : inline39Site.startPC = UInt256.ofNat 2780 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1955) = UInt256.ofNat 2780
  rw [inline39_instructionPC]


theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 1997).take PairedHoistedCoreTrace.inline40Template.length = PairedHoistedCoreTrace.inline40Template := by
  rfl

theorem inline40_instructionPC :
    Artifact.submissionArtifact.instructionPC 1997 = 2828 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline40Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline40Template 1997 inline40_slice
    (by
      change 1997 + PairedHoistedCoreTrace.inline40Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline40Template) (by decide))
    (by decide)

theorem inline40Site_startPC : inline40Site.startPC = UInt256.ofNat 2828 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1997) = UInt256.ofNat 2828
  rw [inline40_instructionPC]


theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2039).take PairedHoistedCoreTrace.inline41Template.length = PairedHoistedCoreTrace.inline41Template := by
  rfl

theorem inline41_instructionPC :
    Artifact.submissionArtifact.instructionPC 2039 = 2877 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline41Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline41Template 2039 inline41_slice
    (by
      change 2039 + PairedHoistedCoreTrace.inline41Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline41Template) (by decide))
    (by decide)

theorem inline41Site_startPC : inline41Site.startPC = UInt256.ofNat 2877 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2039) = UInt256.ofNat 2877
  rw [inline41_instructionPC]


theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2081).take PairedHoistedCoreTrace.inline42Template.length = PairedHoistedCoreTrace.inline42Template := by
  rfl

theorem inline42_instructionPC :
    Artifact.submissionArtifact.instructionPC 2081 = 2926 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline42Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline42Template 2081 inline42_slice
    (by
      change 2081 + PairedHoistedCoreTrace.inline42Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline42Template) (by decide))
    (by decide)

theorem inline42Site_startPC : inline42Site.startPC = UInt256.ofNat 2926 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2081) = UInt256.ofNat 2926
  rw [inline42_instructionPC]


theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2123).take PairedHoistedCoreTrace.inline43Template.length = PairedHoistedCoreTrace.inline43Template := by
  rfl

theorem inline43_instructionPC :
    Artifact.submissionArtifact.instructionPC 2123 = 2974 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline43Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline43Template 2123 inline43_slice
    (by
      change 2123 + PairedHoistedCoreTrace.inline43Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline43Template) (by decide))
    (by decide)

theorem inline43Site_startPC : inline43Site.startPC = UInt256.ofNat 2974 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2123) = UInt256.ofNat 2974
  rw [inline43_instructionPC]


theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2165).take PairedHoistedCoreTrace.inline44Template.length = PairedHoistedCoreTrace.inline44Template := by
  rfl

theorem inline44_instructionPC :
    Artifact.submissionArtifact.instructionPC 2165 = 3023 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline44Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline44Template 2165 inline44_slice
    (by
      change 2165 + PairedHoistedCoreTrace.inline44Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline44Template) (by decide))
    (by decide)

theorem inline44Site_startPC : inline44Site.startPC = UInt256.ofNat 3023 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2165) = UInt256.ofNat 3023
  rw [inline44_instructionPC]


theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2207).take PairedHoistedCoreTrace.inline45Template.length = PairedHoistedCoreTrace.inline45Template := by
  rfl

theorem inline45_instructionPC :
    Artifact.submissionArtifact.instructionPC 2207 = 3072 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline45Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline45Template 2207 inline45_slice
    (by
      change 2207 + PairedHoistedCoreTrace.inline45Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline45Template) (by decide))
    (by decide)

theorem inline45Site_startPC : inline45Site.startPC = UInt256.ofNat 3072 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2207) = UInt256.ofNat 3072
  rw [inline45_instructionPC]


theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2249).take PairedHoistedCoreTrace.inline46Template.length = PairedHoistedCoreTrace.inline46Template := by
  rfl

theorem inline46_instructionPC :
    Artifact.submissionArtifact.instructionPC 2249 = 3120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline46Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline46Template 2249 inline46_slice
    (by
      change 2249 + PairedHoistedCoreTrace.inline46Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline46Template) (by decide))
    (by decide)

theorem inline46Site_startPC : inline46Site.startPC = UInt256.ofNat 3120 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2249) = UInt256.ofNat 3120
  rw [inline46_instructionPC]


theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2282).take PairedHoistedCoreTrace.inline47Template.length = PairedHoistedCoreTrace.inline47Template := by
  rfl

theorem inline47_instructionPC :
    Artifact.submissionArtifact.instructionPC 2282 = 3159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHoistedCoreTrace.inline47Template :=
  StackSiteBuilder.ofSlice PairedHoistedCoreTrace.inline47Template 2282 inline47_slice
    (by
      change 2282 + PairedHoistedCoreTrace.inline47Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHoistedCoreTrace.inline47Template) (by decide))
    (by decide)

theorem inline47Site_startPC : inline47Site.startPC = UInt256.ofNat 3159 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2282) = UInt256.ofNat 3159
  rw [inline47_instructionPC]


theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2315).take PairedHelperBooleanTrace.group48Template.length = PairedHelperBooleanTrace.group48Template := by
  rfl

theorem group48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2315 = 3198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.group48Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.group48Template 2315 group48_slice
    (by
      change 2315 + PairedHelperBooleanTrace.group48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.group48Template) (by decide))
    (by decide)

theorem group48Site_startPC : group48Site.startPC = UInt256.ofNat 3198 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2315) = UInt256.ofNat 3198
  rw [group48_instructionPC]


theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2318).take PairedHelperBooleanTrace.inline48Template.length = PairedHelperBooleanTrace.inline48Template := by
  rfl

theorem inline48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2318 = 3221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline48Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline48Template 2318 inline48_slice
    (by
      change 2318 + PairedHelperBooleanTrace.inline48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline48Template) (by decide))
    (by decide)

theorem inline48Site_startPC : inline48Site.startPC = UInt256.ofNat 3221 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2318) = UInt256.ofNat 3221
  rw [inline48_instructionPC]


theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2372).take PairedHelperBooleanTrace.inline49Template.length = PairedHelperBooleanTrace.inline49Template := by
  rfl

theorem inline49_instructionPC :
    Artifact.submissionArtifact.instructionPC 2372 = 3281 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline49Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline49Template 2372 inline49_slice
    (by
      change 2372 + PairedHelperBooleanTrace.inline49Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline49Template) (by decide))
    (by decide)

theorem inline49Site_startPC : inline49Site.startPC = UInt256.ofNat 3281 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2372) = UInt256.ofNat 3281
  rw [inline49_instructionPC]


theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2426).take PairedHelperBooleanTrace.inline50Template.length = PairedHelperBooleanTrace.inline50Template := by
  rfl

theorem inline50_instructionPC :
    Artifact.submissionArtifact.instructionPC 2426 = 3342 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline50Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline50Template 2426 inline50_slice
    (by
      change 2426 + PairedHelperBooleanTrace.inline50Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline50Template) (by decide))
    (by decide)

theorem inline50Site_startPC : inline50Site.startPC = UInt256.ofNat 3342 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2426) = UInt256.ofNat 3342
  rw [inline50_instructionPC]


theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2480).take PairedHelperBooleanTrace.inline51Template.length = PairedHelperBooleanTrace.inline51Template := by
  rfl

theorem inline51_instructionPC :
    Artifact.submissionArtifact.instructionPC 2480 = 3403 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline51Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline51Template 2480 inline51_slice
    (by
      change 2480 + PairedHelperBooleanTrace.inline51Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline51Template) (by decide))
    (by decide)

theorem inline51Site_startPC : inline51Site.startPC = UInt256.ofNat 3403 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2480) = UInt256.ofNat 3403
  rw [inline51_instructionPC]


theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2534).take PairedHelperBooleanTrace.inline52Template.length = PairedHelperBooleanTrace.inline52Template := by
  rfl

theorem inline52_instructionPC :
    Artifact.submissionArtifact.instructionPC 2534 = 3463 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline52Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline52Template 2534 inline52_slice
    (by
      change 2534 + PairedHelperBooleanTrace.inline52Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline52Template) (by decide))
    (by decide)

theorem inline52Site_startPC : inline52Site.startPC = UInt256.ofNat 3463 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2534) = UInt256.ofNat 3463
  rw [inline52_instructionPC]


theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2579).take PairedHelperBooleanTrace.inline53Template.length = PairedHelperBooleanTrace.inline53Template := by
  rfl

theorem inline53_instructionPC :
    Artifact.submissionArtifact.instructionPC 2579 = 3513 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline53Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline53Template 2579 inline53_slice
    (by
      change 2579 + PairedHelperBooleanTrace.inline53Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline53Template) (by decide))
    (by decide)

theorem inline53Site_startPC : inline53Site.startPC = UInt256.ofNat 3513 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2579) = UInt256.ofNat 3513
  rw [inline53_instructionPC]


theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2633).take PairedHelperBooleanTrace.inline54Template.length = PairedHelperBooleanTrace.inline54Template := by
  rfl

theorem inline54_instructionPC :
    Artifact.submissionArtifact.instructionPC 2633 = 3574 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline54Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline54Template 2633 inline54_slice
    (by
      change 2633 + PairedHelperBooleanTrace.inline54Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline54Template) (by decide))
    (by decide)

theorem inline54Site_startPC : inline54Site.startPC = UInt256.ofNat 3574 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2633) = UInt256.ofNat 3574
  rw [inline54_instructionPC]


theorem inline55_slice :
    (Artifact.submissionArtifact.instructions.drop 2687).take PairedHelperBooleanTrace.inline55Template.length = PairedHelperBooleanTrace.inline55Template := by
  rfl

theorem inline55_instructionPC :
    Artifact.submissionArtifact.instructionPC 2687 = 3635 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline55Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline55Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline55Template 2687 inline55_slice
    (by
      change 2687 + PairedHelperBooleanTrace.inline55Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline55Template) (by decide))
    (by decide)

theorem inline55Site_startPC : inline55Site.startPC = UInt256.ofNat 3635 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2687) = UInt256.ofNat 3635
  rw [inline55_instructionPC]


theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 2741).take PairedHelperBooleanTrace.inline56Template.length = PairedHelperBooleanTrace.inline56Template := by
  rfl

theorem inline56_instructionPC :
    Artifact.submissionArtifact.instructionPC 2741 = 3695 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline56Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline56Template 2741 inline56_slice
    (by
      change 2741 + PairedHelperBooleanTrace.inline56Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline56Template) (by decide))
    (by decide)

theorem inline56Site_startPC : inline56Site.startPC = UInt256.ofNat 3695 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2741) = UInt256.ofNat 3695
  rw [inline56_instructionPC]


theorem inline57_slice :
    (Artifact.submissionArtifact.instructions.drop 2795).take PairedHelperBooleanTrace.inline57Template.length = PairedHelperBooleanTrace.inline57Template := by
  rfl

theorem inline57_instructionPC :
    Artifact.submissionArtifact.instructionPC 2795 = 3756 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline57Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline57Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline57Template 2795 inline57_slice
    (by
      change 2795 + PairedHelperBooleanTrace.inline57Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline57Template) (by decide))
    (by decide)

theorem inline57Site_startPC : inline57Site.startPC = UInt256.ofNat 3756 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2795) = UInt256.ofNat 3756
  rw [inline57_instructionPC]


theorem inline58_slice :
    (Artifact.submissionArtifact.instructions.drop 2849).take PairedHelperBooleanTrace.inline58Template.length = PairedHelperBooleanTrace.inline58Template := by
  rfl

theorem inline58_instructionPC :
    Artifact.submissionArtifact.instructionPC 2849 = 3817 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline58Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline58Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline58Template 2849 inline58_slice
    (by
      change 2849 + PairedHelperBooleanTrace.inline58Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline58Template) (by decide))
    (by decide)

theorem inline58Site_startPC : inline58Site.startPC = UInt256.ofNat 3817 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2849) = UInt256.ofNat 3817
  rw [inline58_instructionPC]


theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 2903).take PairedHelperBooleanTrace.inline59Template.length = PairedHelperBooleanTrace.inline59Template := by
  rfl

theorem inline59_instructionPC :
    Artifact.submissionArtifact.instructionPC 2903 = 3878 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline59Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline59Template 2903 inline59_slice
    (by
      change 2903 + PairedHelperBooleanTrace.inline59Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline59Template) (by decide))
    (by decide)

theorem inline59Site_startPC : inline59Site.startPC = UInt256.ofNat 3878 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2903) = UInt256.ofNat 3878
  rw [inline59_instructionPC]


theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 2957).take PairedHelperBooleanTrace.inline60Template.length = PairedHelperBooleanTrace.inline60Template := by
  rfl

theorem inline60_instructionPC :
    Artifact.submissionArtifact.instructionPC 2957 = 3939 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline60Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline60Template 2957 inline60_slice
    (by
      change 2957 + PairedHelperBooleanTrace.inline60Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline60Template) (by decide))
    (by decide)

theorem inline60Site_startPC : inline60Site.startPC = UInt256.ofNat 3939 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2957) = UInt256.ofNat 3939
  rw [inline60_instructionPC]


theorem inline61_slice :
    (Artifact.submissionArtifact.instructions.drop 3011).take PairedHelperBooleanTrace.inline61Template.length = PairedHelperBooleanTrace.inline61Template := by
  rfl

theorem inline61_instructionPC :
    Artifact.submissionArtifact.instructionPC 3011 = 4000 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline61Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline61Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline61Template 3011 inline61_slice
    (by
      change 3011 + PairedHelperBooleanTrace.inline61Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline61Template) (by decide))
    (by decide)

theorem inline61Site_startPC : inline61Site.startPC = UInt256.ofNat 4000 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3011) = UInt256.ofNat 4000
  rw [inline61_instructionPC]


theorem inline62_slice :
    (Artifact.submissionArtifact.instructions.drop 3065).take PairedHelperBooleanTrace.inline62Template.length = PairedHelperBooleanTrace.inline62Template := by
  rfl

theorem inline62_instructionPC :
    Artifact.submissionArtifact.instructionPC 3065 = 4061 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline62Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline62Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline62Template 3065 inline62_slice
    (by
      change 3065 + PairedHelperBooleanTrace.inline62Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline62Template) (by decide))
    (by decide)

theorem inline62Site_startPC : inline62Site.startPC = UInt256.ofNat 4061 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3065) = UInt256.ofNat 4061
  rw [inline62_instructionPC]


theorem inline63_slice :
    (Artifact.submissionArtifact.instructions.drop 3119).take PairedHelperBooleanTrace.inline63Template.length = PairedHelperBooleanTrace.inline63Template := by
  rfl

theorem inline63_instructionPC :
    Artifact.submissionArtifact.instructionPC 3119 = 4122 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline63Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline63Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline63Template 3119 inline63_slice
    (by
      change 3119 + PairedHelperBooleanTrace.inline63Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline63Template) (by decide))
    (by decide)

theorem inline63Site_startPC : inline63Site.startPC = UInt256.ofNat 4122 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3119) = UInt256.ofNat 4122
  rw [inline63_instructionPC]


theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3173).take PairedHelperBooleanTrace.group64Template.length = PairedHelperBooleanTrace.group64Template := by
  rfl

theorem group64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3173 = 4183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.group64Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.group64Template 3173 group64_slice
    (by
      change 3173 + PairedHelperBooleanTrace.group64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.group64Template) (by decide))
    (by decide)

theorem group64Site_startPC : group64Site.startPC = UInt256.ofNat 4183 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3173) = UInt256.ofNat 4183
  rw [group64_instructionPC]


theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3176).take PairedHelperBooleanTrace.inline64Template.length = PairedHelperBooleanTrace.inline64Template := by
  rfl

theorem inline64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3176 = 4190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline64Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline64Template 3176 inline64_slice
    (by
      change 3176 + PairedHelperBooleanTrace.inline64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline64Template) (by decide))
    (by decide)

theorem inline64Site_startPC : inline64Site.startPC = UInt256.ofNat 4190 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3176) = UInt256.ofNat 4190
  rw [inline64_instructionPC]


theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3224).take PairedHelperBooleanTrace.inline65Template.length = PairedHelperBooleanTrace.inline65Template := by
  rfl

theorem inline65_instructionPC :
    Artifact.submissionArtifact.instructionPC 3224 = 4245 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline65Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline65Template 3224 inline65_slice
    (by
      change 3224 + PairedHelperBooleanTrace.inline65Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline65Template) (by decide))
    (by decide)

theorem inline65Site_startPC : inline65Site.startPC = UInt256.ofNat 4245 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3224) = UInt256.ofNat 4245
  rw [inline65_instructionPC]


theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3272).take PairedHelperBooleanTrace.inline66Template.length = PairedHelperBooleanTrace.inline66Template := by
  rfl

theorem inline66_instructionPC :
    Artifact.submissionArtifact.instructionPC 3272 = 4299 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline66Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline66Template 3272 inline66_slice
    (by
      change 3272 + PairedHelperBooleanTrace.inline66Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline66Template) (by decide))
    (by decide)

theorem inline66Site_startPC : inline66Site.startPC = UInt256.ofNat 4299 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3272) = UInt256.ofNat 4299
  rw [inline66_instructionPC]


theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3320).take PairedHelperBooleanTrace.inline67Template.length = PairedHelperBooleanTrace.inline67Template := by
  rfl

theorem inline67_instructionPC :
    Artifact.submissionArtifact.instructionPC 3320 = 4354 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline67Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline67Template 3320 inline67_slice
    (by
      change 3320 + PairedHelperBooleanTrace.inline67Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline67Template) (by decide))
    (by decide)

theorem inline67Site_startPC : inline67Site.startPC = UInt256.ofNat 4354 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3320) = UInt256.ofNat 4354
  rw [inline67_instructionPC]


theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3368).take PairedHelperBooleanTrace.inline68Template.length = PairedHelperBooleanTrace.inline68Template := by
  rfl

theorem inline68_instructionPC :
    Artifact.submissionArtifact.instructionPC 3368 = 4409 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline68Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline68Template 3368 inline68_slice
    (by
      change 3368 + PairedHelperBooleanTrace.inline68Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline68Template) (by decide))
    (by decide)

theorem inline68Site_startPC : inline68Site.startPC = UInt256.ofNat 4409 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3368) = UInt256.ofNat 4409
  rw [inline68_instructionPC]


theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3416).take PairedHelperBooleanTrace.inline69Template.length = PairedHelperBooleanTrace.inline69Template := by
  rfl

theorem inline69_instructionPC :
    Artifact.submissionArtifact.instructionPC 3416 = 4463 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline69Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline69Template 3416 inline69_slice
    (by
      change 3416 + PairedHelperBooleanTrace.inline69Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline69Template) (by decide))
    (by decide)

theorem inline69Site_startPC : inline69Site.startPC = UInt256.ofNat 4463 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3416) = UInt256.ofNat 4463
  rw [inline69_instructionPC]


theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3464).take PairedHelperBooleanTrace.inline70Template.length = PairedHelperBooleanTrace.inline70Template := by
  rfl

theorem inline70_instructionPC :
    Artifact.submissionArtifact.instructionPC 3464 = 4518 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline70Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline70Template 3464 inline70_slice
    (by
      change 3464 + PairedHelperBooleanTrace.inline70Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline70Template) (by decide))
    (by decide)

theorem inline70Site_startPC : inline70Site.startPC = UInt256.ofNat 4518 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3464) = UInt256.ofNat 4518
  rw [inline70_instructionPC]


theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3512).take PairedHelperBooleanTrace.inline71Template.length = PairedHelperBooleanTrace.inline71Template := by
  rfl

theorem inline71_instructionPC :
    Artifact.submissionArtifact.instructionPC 3512 = 4573 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline71Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline71Template 3512 inline71_slice
    (by
      change 3512 + PairedHelperBooleanTrace.inline71Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline71Template) (by decide))
    (by decide)

theorem inline71Site_startPC : inline71Site.startPC = UInt256.ofNat 4573 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3512) = UInt256.ofNat 4573
  rw [inline71_instructionPC]


theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3560).take PairedHelperBooleanTrace.inline72Template.length = PairedHelperBooleanTrace.inline72Template := by
  rfl

theorem inline72_instructionPC :
    Artifact.submissionArtifact.instructionPC 3560 = 4628 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline72Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline72Template 3560 inline72_slice
    (by
      change 3560 + PairedHelperBooleanTrace.inline72Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline72Template) (by decide))
    (by decide)

theorem inline72Site_startPC : inline72Site.startPC = UInt256.ofNat 4628 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3560) = UInt256.ofNat 4628
  rw [inline72_instructionPC]


theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3608).take PairedHelperBooleanTrace.inline73Template.length = PairedHelperBooleanTrace.inline73Template := by
  rfl

theorem inline73_instructionPC :
    Artifact.submissionArtifact.instructionPC 3608 = 4683 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline73Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline73Template 3608 inline73_slice
    (by
      change 3608 + PairedHelperBooleanTrace.inline73Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline73Template) (by decide))
    (by decide)

theorem inline73Site_startPC : inline73Site.startPC = UInt256.ofNat 4683 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3608) = UInt256.ofNat 4683
  rw [inline73_instructionPC]


theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3656).take PairedHelperBooleanTrace.inline74Template.length = PairedHelperBooleanTrace.inline74Template := by
  rfl

theorem inline74_instructionPC :
    Artifact.submissionArtifact.instructionPC 3656 = 4737 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline74Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline74Template 3656 inline74_slice
    (by
      change 3656 + PairedHelperBooleanTrace.inline74Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline74Template) (by decide))
    (by decide)

theorem inline74Site_startPC : inline74Site.startPC = UInt256.ofNat 4737 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3656) = UInt256.ofNat 4737
  rw [inline74_instructionPC]


theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3704).take PairedHelperBooleanTrace.inline75Template.length = PairedHelperBooleanTrace.inline75Template := by
  rfl

theorem inline75_instructionPC :
    Artifact.submissionArtifact.instructionPC 3704 = 4792 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline75Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline75Template 3704 inline75_slice
    (by
      change 3704 + PairedHelperBooleanTrace.inline75Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline75Template) (by decide))
    (by decide)

theorem inline75Site_startPC : inline75Site.startPC = UInt256.ofNat 4792 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3704) = UInt256.ofNat 4792
  rw [inline75_instructionPC]


theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3752).take PairedHelperBooleanTrace.inline76Template.length = PairedHelperBooleanTrace.inline76Template := by
  rfl

theorem inline76_instructionPC :
    Artifact.submissionArtifact.instructionPC 3752 = 4847 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline76Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline76Template 3752 inline76_slice
    (by
      change 3752 + PairedHelperBooleanTrace.inline76Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline76Template) (by decide))
    (by decide)

theorem inline76Site_startPC : inline76Site.startPC = UInt256.ofNat 4847 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3752) = UInt256.ofNat 4847
  rw [inline76_instructionPC]


theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 3800).take PairedHelperBooleanTrace.inline77Template.length = PairedHelperBooleanTrace.inline77Template := by
  rfl

theorem inline77_instructionPC :
    Artifact.submissionArtifact.instructionPC 3800 = 4901 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline77Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline77Template 3800 inline77_slice
    (by
      change 3800 + PairedHelperBooleanTrace.inline77Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline77Template) (by decide))
    (by decide)

theorem inline77Site_startPC : inline77Site.startPC = UInt256.ofNat 4901 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3800) = UInt256.ofNat 4901
  rw [inline77_instructionPC]


theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3848).take PairedHelperBooleanTrace.inline78Template.length = PairedHelperBooleanTrace.inline78Template := by
  rfl

theorem inline78_instructionPC :
    Artifact.submissionArtifact.instructionPC 3848 = 4956 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline78Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline78Template 3848 inline78_slice
    (by
      change 3848 + PairedHelperBooleanTrace.inline78Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline78Template) (by decide))
    (by decide)

theorem inline78Site_startPC : inline78Site.startPC = UInt256.ofNat 4956 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3848) = UInt256.ofNat 4956
  rw [inline78_instructionPC]


theorem inline79_slice :
    (Artifact.submissionArtifact.instructions.drop 3896).take PairedHelperBooleanTrace.inline79Template.length = PairedHelperBooleanTrace.inline79Template := by
  rfl

theorem inline79_instructionPC :
    Artifact.submissionArtifact.instructionPC 3896 = 5011 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline79Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.inline79Template :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.inline79Template 3896 inline79_slice
    (by
      change 3896 + PairedHelperBooleanTrace.inline79Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.inline79Template) (by decide))
    (by decide)

theorem inline79Site_startPC : inline79Site.startPC = UInt256.ofNat 5011 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3896) = UInt256.ofNat 5011
  rw [inline79_instructionPC]


theorem coreExit_slice :
    (Artifact.submissionArtifact.instructions.drop 3944).take PairedHelperBooleanTrace.coreExitTemplate.length = PairedHelperBooleanTrace.coreExitTemplate := by
  rfl

theorem coreExit_instructionPC :
    Artifact.submissionArtifact.instructionPC 3944 = 5066 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def coreExitSite : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.coreExitTemplate :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.coreExitTemplate 3944 coreExit_slice
    (by
      change 3944 + PairedHelperBooleanTrace.coreExitTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.coreExitTemplate) (by decide))
    (by decide)

theorem coreExitSite_startPC : coreExitSite.startPC = UInt256.ofNat 5066 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3944) = UInt256.ofNat 5066
  rw [coreExit_instructionPC]


theorem helper_slice :
    (Artifact.submissionArtifact.instructions.drop 4016).take PairedHelperBooleanTrace.fullTemplate.length = PairedHelperBooleanTrace.fullTemplate := by
  rfl

theorem helper_instructionPC :
    Artifact.submissionArtifact.instructionPC 4016 = 5153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def helperSite : GenericRoundSite Artifact.submissionArtifact .Osaka PairedHelperBooleanTrace.fullTemplate :=
  StackSiteBuilder.ofSlice PairedHelperBooleanTrace.fullTemplate 4016 helper_slice
    (by
      change 4016 + PairedHelperBooleanTrace.fullTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedHelperBooleanTrace.fullTemplate) (by decide))
    (by decide)

theorem helperSite_startPC : helperSite.startPC = UInt256.ofNat 5153 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4016) = UInt256.ofNat 5153
  rw [helper_instructionPC]


def wholeSites : PairedHoistedCoreTrace.WholeCoreSites Artifact.submissionArtifact .Osaka where
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
  call20 := ⟨call20Site, call20Site_startPC⟩
  call22 := ⟨call22Site, call22Site_startPC⟩
  return24 := ⟨return24Site, return24Site_startPC⟩
  inline24 := ⟨inline24Site, inline24Site_startPC⟩
  inline25 := ⟨inline25Site, inline25Site_startPC⟩
  call26 := ⟨call26Site, call26Site_startPC⟩
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

theorem validJumpDest_5153 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 5153 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4016 (by rfl)
  rw [helper_instructionPC] at h
  exact h

theorem validJumpDest_1920 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 1920 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1264 (by rfl)
  rw [return18_instructionPC] at h
  exact h

theorem validJumpDest_2077 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2077 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1393 (by rfl)
  rw [call22_instructionPC] at h
  exact h

theorem validJumpDest_2116 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2116 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1416 (by rfl)
  rw [return24_instructionPC] at h
  exact h

theorem validJumpDest_2264 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2264 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1536 (by rfl)
  rw [call28_instructionPC] at h
  exact h

theorem validJumpDest_2303 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2303 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1559 (by rfl)
  rw [return30_instructionPC] at h
  exact h

theorem coreJumpValid (s : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) : PairedHoistedCoreTrace.CoreJumpValid s := by
  intro dest hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [hcode]
  · exact validJumpDest_5153
  · exact validJumpDest_1920
  · exact validJumpDest_2077
  · exact validJumpDest_2116
  · exact validJumpDest_2264
  · exact validJumpDest_2303

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
      {s with pc := UInt256.ofNat 5068, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (coreCryptoResult words left right) rho} :=
  PairedHoistedCoreTrace.gasSteps_wholeCore_normalized wholeSites s words left right rho hstack hrun hactive
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
#print axioms call20_slice
#print axioms call20_instructionPC
#print axioms call20Site_startPC
#print axioms call22_slice
#print axioms call22_instructionPC
#print axioms call22Site_startPC
#print axioms return24_slice
#print axioms return24_instructionPC
#print axioms return24Site_startPC
#print axioms inline24_slice
#print axioms inline24_instructionPC
#print axioms inline24Site_startPC
#print axioms inline25_slice
#print axioms inline25_instructionPC
#print axioms inline25Site_startPC
#print axioms call26_slice
#print axioms call26_instructionPC
#print axioms call26Site_startPC
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
#print axioms validJumpDest_5153
#print axioms validJumpDest_1920
#print axioms validJumpDest_2077
#print axioms validJumpDest_2116
#print axioms validJumpDest_2264
#print axioms validJumpDest_2303
#print axioms coreJumpValid
#print axioms gasSteps_core_normalized

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHoistedCoreSites

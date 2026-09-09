import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate PairedHelperBooleanTrace

/-- Exact eighty inline rounds and five straightline seams of frozen5298/raw469b1b15. -/

theorem group0_slice :
    (Artifact.submissionArtifact.instructions.drop 474).take PairedAllInlineCoreTrace.group0Template.length = PairedAllInlineCoreTrace.group0Template := by
  rfl

theorem group0_instructionPC :
    Artifact.submissionArtifact.instructionPC 474 = 769 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group0Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group0Template 474 group0_slice
    (by
      change 474 + PairedAllInlineCoreTrace.group0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group0Template) (by decide))
    (by decide)

theorem group0Site_startPC : group0Site.startPC = UInt256.ofNat 769 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 474) = UInt256.ofNat 769
  rw [group0_instructionPC]

theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 477).take PairedSynthCoreTrace.inline0Template.length = PairedSynthCoreTrace.inline0Template := by
  rfl

theorem inline0_instructionPC :
    Artifact.submissionArtifact.instructionPC 477 = 777 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline0Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline0Template 477 inline0_slice
    (by
      change 477 + PairedSynthCoreTrace.inline0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline0Template) (by decide))
    (by decide)

theorem inline0Site_startPC : inline0Site.startPC = UInt256.ofNat 777 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 477) = UInt256.ofNat 777
  rw [inline0_instructionPC]

theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 523).take PairedSynthCoreTrace.inline1Template.length = PairedSynthCoreTrace.inline1Template := by
  rfl

theorem inline1_instructionPC :
    Artifact.submissionArtifact.instructionPC 523 = 829 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline1Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline1Template 523 inline1_slice
    (by
      change 523 + PairedSynthCoreTrace.inline1Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline1Template) (by decide))
    (by decide)

theorem inline1Site_startPC : inline1Site.startPC = UInt256.ofNat 829 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 523) = UInt256.ofNat 829
  rw [inline1_instructionPC]

theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 569).take PairedSynthCoreTrace.inline2Template.length = PairedSynthCoreTrace.inline2Template := by
  rfl

theorem inline2_instructionPC :
    Artifact.submissionArtifact.instructionPC 569 = 881 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline2Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline2Template 569 inline2_slice
    (by
      change 569 + PairedSynthCoreTrace.inline2Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline2Template) (by decide))
    (by decide)

theorem inline2Site_startPC : inline2Site.startPC = UInt256.ofNat 881 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 569) = UInt256.ofNat 881
  rw [inline2_instructionPC]

theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 615).take PairedSynthCoreTrace.inline3Template.length = PairedSynthCoreTrace.inline3Template := by
  rfl

theorem inline3_instructionPC :
    Artifact.submissionArtifact.instructionPC 615 = 934 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline3Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline3Template 615 inline3_slice
    (by
      change 615 + PairedSynthCoreTrace.inline3Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline3Template) (by decide))
    (by decide)

theorem inline3Site_startPC : inline3Site.startPC = UInt256.ofNat 934 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 615) = UInt256.ofNat 934
  rw [inline3_instructionPC]

theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 661).take PairedSynthCoreTrace.inline4Template.length = PairedSynthCoreTrace.inline4Template := by
  rfl

theorem inline4_instructionPC :
    Artifact.submissionArtifact.instructionPC 661 = 986 := by
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

theorem inline4Site_startPC : inline4Site.startPC = UInt256.ofNat 986 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 661) = UInt256.ofNat 986
  rw [inline4_instructionPC]

theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 708).take PairedSynthCoreTrace.inline5Template.length = PairedSynthCoreTrace.inline5Template := by
  rfl

theorem inline5_instructionPC :
    Artifact.submissionArtifact.instructionPC 708 = 1040 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline5Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline5Template 708 inline5_slice
    (by
      change 708 + PairedSynthCoreTrace.inline5Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline5Template) (by decide))
    (by decide)

theorem inline5Site_startPC : inline5Site.startPC = UInt256.ofNat 1040 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 708) = UInt256.ofNat 1040
  rw [inline5_instructionPC]

theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 755).take PairedSynthCoreTrace.inline6Template.length = PairedSynthCoreTrace.inline6Template := by
  rfl

theorem inline6_instructionPC :
    Artifact.submissionArtifact.instructionPC 755 = 1094 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline6Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline6Template 755 inline6_slice
    (by
      change 755 + PairedSynthCoreTrace.inline6Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline6Template) (by decide))
    (by decide)

theorem inline6Site_startPC : inline6Site.startPC = UInt256.ofNat 1094 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 755) = UInt256.ofNat 1094
  rw [inline6_instructionPC]

theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 802).take PairedSynthCoreTrace.inline7Template.length = PairedSynthCoreTrace.inline7Template := by
  rfl

theorem inline7_instructionPC :
    Artifact.submissionArtifact.instructionPC 802 = 1148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline7Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline7Template 802 inline7_slice
    (by
      change 802 + PairedSynthCoreTrace.inline7Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline7Template) (by decide))
    (by decide)

theorem inline7Site_startPC : inline7Site.startPC = UInt256.ofNat 1148 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 802) = UInt256.ofNat 1148
  rw [inline7_instructionPC]

theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 848).take PairedSynthCoreTrace.inline8Template.length = PairedSynthCoreTrace.inline8Template := by
  rfl

theorem inline8_instructionPC :
    Artifact.submissionArtifact.instructionPC 848 = 1201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline8Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline8Template 848 inline8_slice
    (by
      change 848 + PairedSynthCoreTrace.inline8Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline8Template) (by decide))
    (by decide)

theorem inline8Site_startPC : inline8Site.startPC = UInt256.ofNat 1201 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 848) = UInt256.ofNat 1201
  rw [inline8_instructionPC]

theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 894).take PairedSynthCoreTrace.inline9Template.length = PairedSynthCoreTrace.inline9Template := by
  rfl

theorem inline9_instructionPC :
    Artifact.submissionArtifact.instructionPC 894 = 1254 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline9Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline9Template 894 inline9_slice
    (by
      change 894 + PairedSynthCoreTrace.inline9Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline9Template) (by decide))
    (by decide)

theorem inline9Site_startPC : inline9Site.startPC = UInt256.ofNat 1254 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 894) = UInt256.ofNat 1254
  rw [inline9_instructionPC]

theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 940).take PairedSynthCoreTrace.inline10Template.length = PairedSynthCoreTrace.inline10Template := by
  rfl

theorem inline10_instructionPC :
    Artifact.submissionArtifact.instructionPC 940 = 1307 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline10Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline10Template 940 inline10_slice
    (by
      change 940 + PairedSynthCoreTrace.inline10Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline10Template) (by decide))
    (by decide)

theorem inline10Site_startPC : inline10Site.startPC = UInt256.ofNat 1307 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 940) = UInt256.ofNat 1307
  rw [inline10_instructionPC]

theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 986).take PairedSynthCoreTrace.inline11Template.length = PairedSynthCoreTrace.inline11Template := by
  rfl

theorem inline11_instructionPC :
    Artifact.submissionArtifact.instructionPC 986 = 1360 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline11Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline11Template 986 inline11_slice
    (by
      change 986 + PairedSynthCoreTrace.inline11Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline11Template) (by decide))
    (by decide)

theorem inline11Site_startPC : inline11Site.startPC = UInt256.ofNat 1360 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 986) = UInt256.ofNat 1360
  rw [inline11_instructionPC]

theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1032).take PairedSynthCoreTrace.inline12Template.length = PairedSynthCoreTrace.inline12Template := by
  rfl

theorem inline12_instructionPC :
    Artifact.submissionArtifact.instructionPC 1032 = 1413 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline12Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline12Template 1032 inline12_slice
    (by
      change 1032 + PairedSynthCoreTrace.inline12Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline12Template) (by decide))
    (by decide)

theorem inline12Site_startPC : inline12Site.startPC = UInt256.ofNat 1413 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1032) = UInt256.ofNat 1413
  rw [inline12_instructionPC]

theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1079).take PairedSynthCoreTrace.inline13Template.length = PairedSynthCoreTrace.inline13Template := by
  rfl

theorem inline13_instructionPC :
    Artifact.submissionArtifact.instructionPC 1079 = 1466 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline13Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline13Template 1079 inline13_slice
    (by
      change 1079 + PairedSynthCoreTrace.inline13Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline13Template) (by decide))
    (by decide)

theorem inline13Site_startPC : inline13Site.startPC = UInt256.ofNat 1466 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1079) = UInt256.ofNat 1466
  rw [inline13_instructionPC]

theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1126).take PairedSynthCoreTrace.inline14Template.length = PairedSynthCoreTrace.inline14Template := by
  rfl

theorem inline14_instructionPC :
    Artifact.submissionArtifact.instructionPC 1126 = 1520 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline14Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline14Template 1126 inline14_slice
    (by
      change 1126 + PairedSynthCoreTrace.inline14Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline14Template) (by decide))
    (by decide)

theorem inline14Site_startPC : inline14Site.startPC = UInt256.ofNat 1520 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1126) = UInt256.ofNat 1520
  rw [inline14_instructionPC]

theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1173).take PairedAllInlineCoreTrace.groupK_consumed15Template.length = PairedAllInlineCoreTrace.groupK_consumed15Template := by
  rfl

theorem inline15_instructionPC :
    Artifact.submissionArtifact.instructionPC 1173 = 1574 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.groupK_consumed15Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.groupK_consumed15Template 1173 inline15_slice
    (by
      change 1173 + PairedAllInlineCoreTrace.groupK_consumed15Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.groupK_consumed15Template) (by decide))
    (by decide)

theorem inline15Site_startPC : inline15Site.startPC = UInt256.ofNat 1574 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1173) = UInt256.ofNat 1574
  rw [inline15_instructionPC]

theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1218).take PairedAllInlineCoreTrace.group16Template.length = PairedAllInlineCoreTrace.group16Template := by
  rfl

theorem group16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1218 = 1626 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group16Template 1218 group16_slice
    (by
      change 1218 + PairedAllInlineCoreTrace.group16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group16Template) (by decide))
    (by decide)

theorem group16Site_startPC : group16Site.startPC = UInt256.ofNat 1626 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1218) = UInt256.ofNat 1626
  rw [group16_instructionPC]

theorem inline16_slice :
    (Artifact.submissionArtifact.instructions.drop 1223).take PairedAllInlineNewPairs.inline16Template.length = PairedAllInlineNewPairs.inline16Template := by
  rfl

theorem inline16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1223 = 1640 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline16Template 1223 inline16_slice
    (by
      change 1223 + PairedAllInlineNewPairs.inline16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline16Template) (by decide))
    (by decide)

theorem inline16Site_startPC : inline16Site.startPC = UInt256.ofNat 1640 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1223) = UInt256.ofNat 1640
  rw [inline16_instructionPC]

theorem inline17_slice :
    (Artifact.submissionArtifact.instructions.drop 1272).take PairedAllInlineNewPairs.inline17Template.length = PairedAllInlineNewPairs.inline17Template := by
  rfl

theorem inline17_instructionPC :
    Artifact.submissionArtifact.instructionPC 1272 = 1696 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline17Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline17Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline17Template 1272 inline17_slice
    (by
      change 1272 + PairedAllInlineNewPairs.inline17Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline17Template) (by decide))
    (by decide)

theorem inline17Site_startPC : inline17Site.startPC = UInt256.ofNat 1696 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1272) = UInt256.ofNat 1696
  rw [inline17_instructionPC]

theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1321).take PairedAllInlineCoreTrace.inline18Template.length = PairedAllInlineCoreTrace.inline18Template := by
  rfl

theorem inline18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1321 = 1752 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline18Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline18Template 1321 inline18_slice
    (by
      change 1321 + PairedAllInlineCoreTrace.inline18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline18Template) (by decide))
    (by decide)

theorem inline18Site_startPC : inline18Site.startPC = UInt256.ofNat 1752 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1321) = UInt256.ofNat 1752
  rw [inline18_instructionPC]

theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1370).take PairedAllInlineCoreTrace.inline19Template.length = PairedAllInlineCoreTrace.inline19Template := by
  rfl

theorem inline19_instructionPC :
    Artifact.submissionArtifact.instructionPC 1370 = 1808 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline19Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline19Template 1370 inline19_slice
    (by
      change 1370 + PairedAllInlineCoreTrace.inline19Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline19Template) (by decide))
    (by decide)

theorem inline19Site_startPC : inline19Site.startPC = UInt256.ofNat 1808 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1370) = UInt256.ofNat 1808
  rw [inline19_instructionPC]

theorem inline20_slice :
    (Artifact.submissionArtifact.instructions.drop 1418).take PairedAllInlineCoreTrace.inline20Template.length = PairedAllInlineCoreTrace.inline20Template := by
  rfl

theorem inline20_instructionPC :
    Artifact.submissionArtifact.instructionPC 1418 = 1862 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline20Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline20Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline20Template 1418 inline20_slice
    (by
      change 1418 + PairedAllInlineCoreTrace.inline20Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline20Template) (by decide))
    (by decide)

theorem inline20Site_startPC : inline20Site.startPC = UInt256.ofNat 1862 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1418) = UInt256.ofNat 1862
  rw [inline20_instructionPC]

theorem inline21_slice :
    (Artifact.submissionArtifact.instructions.drop 1467).take PairedAllInlineCoreTrace.inline21Template.length = PairedAllInlineCoreTrace.inline21Template := by
  rfl

theorem inline21_instructionPC :
    Artifact.submissionArtifact.instructionPC 1467 = 1917 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline21Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline21Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline21Template 1467 inline21_slice
    (by
      change 1467 + PairedAllInlineCoreTrace.inline21Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline21Template) (by decide))
    (by decide)

theorem inline21Site_startPC : inline21Site.startPC = UInt256.ofNat 1917 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1467) = UInt256.ofNat 1917
  rw [inline21_instructionPC]

theorem inline22_slice :
    (Artifact.submissionArtifact.instructions.drop 1515).take PairedAllInlineCoreTrace.inline22Template.length = PairedAllInlineCoreTrace.inline22Template := by
  rfl

theorem inline22_instructionPC :
    Artifact.submissionArtifact.instructionPC 1515 = 1972 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline22Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline22Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline22Template 1515 inline22_slice
    (by
      change 1515 + PairedAllInlineCoreTrace.inline22Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline22Template) (by decide))
    (by decide)

theorem inline22Site_startPC : inline22Site.startPC = UInt256.ofNat 1972 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1515) = UInt256.ofNat 1972
  rw [inline22_instructionPC]

theorem inline23_slice :
    (Artifact.submissionArtifact.instructions.drop 1564).take PairedAllInlineCoreTrace.inline23Template.length = PairedAllInlineCoreTrace.inline23Template := by
  rfl

theorem inline23_instructionPC :
    Artifact.submissionArtifact.instructionPC 1564 = 2028 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline23Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline23Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline23Template 1564 inline23_slice
    (by
      change 1564 + PairedAllInlineCoreTrace.inline23Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline23Template) (by decide))
    (by decide)

theorem inline23Site_startPC : inline23Site.startPC = UInt256.ofNat 2028 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1564) = UInt256.ofNat 2028
  rw [inline23_instructionPC]

theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1612).take PairedAllInlineCoreTrace.inline24Template.length = PairedAllInlineCoreTrace.inline24Template := by
  rfl

theorem inline24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1612 = 2083 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline24Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline24Template 1612 inline24_slice
    (by
      change 1612 + PairedAllInlineCoreTrace.inline24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline24Template) (by decide))
    (by decide)

theorem inline24Site_startPC : inline24Site.startPC = UInt256.ofNat 2083 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1612) = UInt256.ofNat 2083
  rw [inline24_instructionPC]

theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1652).take PairedAllInlineCoreTrace.inline25Template.length = PairedAllInlineCoreTrace.inline25Template := by
  rfl

theorem inline25_instructionPC :
    Artifact.submissionArtifact.instructionPC 1652 = 2129 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline25Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline25Template 1652 inline25_slice
    (by
      change 1652 + PairedAllInlineCoreTrace.inline25Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline25Template) (by decide))
    (by decide)

theorem inline25Site_startPC : inline25Site.startPC = UInt256.ofNat 2129 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1652) = UInt256.ofNat 2129
  rw [inline25_instructionPC]

theorem inline26_slice :
    (Artifact.submissionArtifact.instructions.drop 1700).take PairedAllInlineCoreTrace.inline26Template.length = PairedAllInlineCoreTrace.inline26Template := by
  rfl

theorem inline26_instructionPC :
    Artifact.submissionArtifact.instructionPC 1700 = 2183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline26Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline26Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline26Template 1700 inline26_slice
    (by
      change 1700 + PairedAllInlineCoreTrace.inline26Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline26Template) (by decide))
    (by decide)

theorem inline26Site_startPC : inline26Site.startPC = UInt256.ofNat 2183 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1700) = UInt256.ofNat 2183
  rw [inline26_instructionPC]

theorem inline27_slice :
    (Artifact.submissionArtifact.instructions.drop 1748).take PairedAllInlineCoreTrace.inline27Template.length = PairedAllInlineCoreTrace.inline27Template := by
  rfl

theorem inline27_instructionPC :
    Artifact.submissionArtifact.instructionPC 1748 = 2238 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline27Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline27Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline27Template 1748 inline27_slice
    (by
      change 1748 + PairedAllInlineCoreTrace.inline27Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline27Template) (by decide))
    (by decide)

theorem inline27Site_startPC : inline27Site.startPC = UInt256.ofNat 2238 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1748) = UInt256.ofNat 2238
  rw [inline27_instructionPC]

theorem inline28_slice :
    (Artifact.submissionArtifact.instructions.drop 1796).take PairedAllInlineNewPairs.inline28Template.length = PairedAllInlineNewPairs.inline28Template := by
  rfl

theorem inline28_instructionPC :
    Artifact.submissionArtifact.instructionPC 1796 = 2293 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline28Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline28Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline28Template 1796 inline28_slice
    (by
      change 1796 + PairedAllInlineNewPairs.inline28Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline28Template) (by decide))
    (by decide)

theorem inline28Site_startPC : inline28Site.startPC = UInt256.ofNat 2293 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1796) = UInt256.ofNat 2293
  rw [inline28_instructionPC]

theorem inline29_slice :
    (Artifact.submissionArtifact.instructions.drop 1844).take PairedAllInlineNewPairs.inline29Template.length = PairedAllInlineNewPairs.inline29Template := by
  rfl

theorem inline29_instructionPC :
    Artifact.submissionArtifact.instructionPC 1844 = 2348 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline29Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline29Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline29Template 1844 inline29_slice
    (by
      change 1844 + PairedAllInlineNewPairs.inline29Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline29Template) (by decide))
    (by decide)

theorem inline29Site_startPC : inline29Site.startPC = UInt256.ofNat 2348 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1844) = UInt256.ofNat 2348
  rw [inline29_instructionPC]

theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1893).take PairedAllInlineCoreTrace.inline30Template.length = PairedAllInlineCoreTrace.inline30Template := by
  rfl

theorem inline30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1893 = 2404 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline30Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline30Template 1893 inline30_slice
    (by
      change 1893 + PairedAllInlineCoreTrace.inline30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline30Template) (by decide))
    (by decide)

theorem inline30Site_startPC : inline30Site.startPC = UInt256.ofNat 2404 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1893) = UInt256.ofNat 2404
  rw [inline30_instructionPC]

theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1933).take PairedAllInlineCoreTrace.inline31Template.length = PairedAllInlineCoreTrace.inline31Template := by
  rfl

theorem inline31_instructionPC :
    Artifact.submissionArtifact.instructionPC 1933 = 2449 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline31Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline31Template 1933 inline31_slice
    (by
      change 1933 + PairedAllInlineCoreTrace.inline31Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline31Template) (by decide))
    (by decide)

theorem inline31Site_startPC : inline31Site.startPC = UInt256.ofNat 2449 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1933) = UInt256.ofNat 2449
  rw [inline31_instructionPC]

theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1981).take PairedAllInlineCoreTrace.group32Template.length = PairedAllInlineCoreTrace.group32Template := by
  rfl

theorem group32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1981 = 2504 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group32Template 1981 group32_slice
    (by
      change 1981 + PairedAllInlineCoreTrace.group32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group32Template) (by decide))
    (by decide)

theorem group32Site_startPC : group32Site.startPC = UInt256.ofNat 2504 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1981) = UInt256.ofNat 2504
  rw [group32_instructionPC]

theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1984).take PairedAllInlineCoreTrace.inline32Template.length = PairedAllInlineCoreTrace.inline32Template := by
  rfl

theorem inline32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1984 = 2528 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline32Template 1984 inline32_slice
    (by
      change 1984 + PairedAllInlineCoreTrace.inline32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline32Template) (by decide))
    (by decide)

theorem inline32Site_startPC : inline32Site.startPC = UInt256.ofNat 2528 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1984) = UInt256.ofNat 2528
  rw [inline32_instructionPC]

theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 2025).take PairedAllInlineCoreTrace.inline33Template.length = PairedAllInlineCoreTrace.inline33Template := by
  rfl

theorem inline33_instructionPC :
    Artifact.submissionArtifact.instructionPC 2025 = 2576 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline33Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline33Template 2025 inline33_slice
    (by
      change 2025 + PairedAllInlineCoreTrace.inline33Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline33Template) (by decide))
    (by decide)

theorem inline33Site_startPC : inline33Site.startPC = UInt256.ofNat 2576 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2025) = UInt256.ofNat 2576
  rw [inline33_instructionPC]

theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 2066).take PairedAllInlineCoreTrace.inline34Template.length = PairedAllInlineCoreTrace.inline34Template := by
  rfl

theorem inline34_instructionPC :
    Artifact.submissionArtifact.instructionPC 2066 = 2624 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline34Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline34Template 2066 inline34_slice
    (by
      change 2066 + PairedAllInlineCoreTrace.inline34Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline34Template) (by decide))
    (by decide)

theorem inline34Site_startPC : inline34Site.startPC = UInt256.ofNat 2624 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2066) = UInt256.ofNat 2624
  rw [inline34_instructionPC]

theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 2108).take PairedAllInlineCoreTrace.inline35Template.length = PairedAllInlineCoreTrace.inline35Template := by
  rfl

theorem inline35_instructionPC :
    Artifact.submissionArtifact.instructionPC 2108 = 2672 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline35Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline35Template 2108 inline35_slice
    (by
      change 2108 + PairedAllInlineCoreTrace.inline35Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline35Template) (by decide))
    (by decide)

theorem inline35Site_startPC : inline35Site.startPC = UInt256.ofNat 2672 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2108) = UInt256.ofNat 2672
  rw [inline35_instructionPC]

theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 2150).take PairedAllInlineCoreTrace.inline36Template.length = PairedAllInlineCoreTrace.inline36Template := by
  rfl

theorem inline36_instructionPC :
    Artifact.submissionArtifact.instructionPC 2150 = 2721 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline36Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline36Template 2150 inline36_slice
    (by
      change 2150 + PairedAllInlineCoreTrace.inline36Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline36Template) (by decide))
    (by decide)

theorem inline36Site_startPC : inline36Site.startPC = UInt256.ofNat 2721 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2150) = UInt256.ofNat 2721
  rw [inline36_instructionPC]

theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 2191).take PairedAllInlineCoreTrace.inline37Template.length = PairedAllInlineCoreTrace.inline37Template := by
  rfl

theorem inline37_instructionPC :
    Artifact.submissionArtifact.instructionPC 2191 = 2769 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline37Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline37Template 2191 inline37_slice
    (by
      change 2191 + PairedAllInlineCoreTrace.inline37Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline37Template) (by decide))
    (by decide)

theorem inline37Site_startPC : inline37Site.startPC = UInt256.ofNat 2769 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2191) = UInt256.ofNat 2769
  rw [inline37_instructionPC]

theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 2232).take PairedAllInlineCoreTrace.inline38Template.length = PairedAllInlineCoreTrace.inline38Template := by
  rfl

theorem inline38_instructionPC :
    Artifact.submissionArtifact.instructionPC 2232 = 2817 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline38Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline38Template 2232 inline38_slice
    (by
      change 2232 + PairedAllInlineCoreTrace.inline38Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline38Template) (by decide))
    (by decide)

theorem inline38Site_startPC : inline38Site.startPC = UInt256.ofNat 2817 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2232) = UInt256.ofNat 2817
  rw [inline38_instructionPC]

theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 2273).take PairedAllInlineCoreTrace.inline39Template.length = PairedAllInlineCoreTrace.inline39Template := by
  rfl

theorem inline39_instructionPC :
    Artifact.submissionArtifact.instructionPC 2273 = 2865 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline39Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline39Template 2273 inline39_slice
    (by
      change 2273 + PairedAllInlineCoreTrace.inline39Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline39Template) (by decide))
    (by decide)

theorem inline39Site_startPC : inline39Site.startPC = UInt256.ofNat 2865 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2273) = UInt256.ofNat 2865
  rw [inline39_instructionPC]

theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 2314).take PairedAllInlineCoreTrace.inline40Template.length = PairedAllInlineCoreTrace.inline40Template := by
  rfl

theorem inline40_instructionPC :
    Artifact.submissionArtifact.instructionPC 2314 = 2912 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline40Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline40Template 2314 inline40_slice
    (by
      change 2314 + PairedAllInlineCoreTrace.inline40Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline40Template) (by decide))
    (by decide)

theorem inline40Site_startPC : inline40Site.startPC = UInt256.ofNat 2912 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2314) = UInt256.ofNat 2912
  rw [inline40_instructionPC]

theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2355).take PairedAllInlineCoreTrace.inline41Template.length = PairedAllInlineCoreTrace.inline41Template := by
  rfl

theorem inline41_instructionPC :
    Artifact.submissionArtifact.instructionPC 2355 = 2960 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline41Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline41Template 2355 inline41_slice
    (by
      change 2355 + PairedAllInlineCoreTrace.inline41Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline41Template) (by decide))
    (by decide)

theorem inline41Site_startPC : inline41Site.startPC = UInt256.ofNat 2960 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2355) = UInt256.ofNat 2960
  rw [inline41_instructionPC]

theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2397).take PairedAllInlineCoreTrace.inline42Template.length = PairedAllInlineCoreTrace.inline42Template := by
  rfl

theorem inline42_instructionPC :
    Artifact.submissionArtifact.instructionPC 2397 = 3009 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline42Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline42Template 2397 inline42_slice
    (by
      change 2397 + PairedAllInlineCoreTrace.inline42Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline42Template) (by decide))
    (by decide)

theorem inline42Site_startPC : inline42Site.startPC = UInt256.ofNat 3009 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2397) = UInt256.ofNat 3009
  rw [inline42_instructionPC]

theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2438).take PairedAllInlineCoreTrace.inline43Template.length = PairedAllInlineCoreTrace.inline43Template := by
  rfl

theorem inline43_instructionPC :
    Artifact.submissionArtifact.instructionPC 2438 = 3056 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline43Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline43Template 2438 inline43_slice
    (by
      change 2438 + PairedAllInlineCoreTrace.inline43Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline43Template) (by decide))
    (by decide)

theorem inline43Site_startPC : inline43Site.startPC = UInt256.ofNat 3056 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2438) = UInt256.ofNat 3056
  rw [inline43_instructionPC]

theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2480).take PairedAllInlineCoreTrace.inline44Template.length = PairedAllInlineCoreTrace.inline44Template := by
  rfl

theorem inline44_instructionPC :
    Artifact.submissionArtifact.instructionPC 2480 = 3105 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline44Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline44Template 2480 inline44_slice
    (by
      change 2480 + PairedAllInlineCoreTrace.inline44Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline44Template) (by decide))
    (by decide)

theorem inline44Site_startPC : inline44Site.startPC = UInt256.ofNat 3105 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2480) = UInt256.ofNat 3105
  rw [inline44_instructionPC]

theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2522).take PairedAllInlineCoreTrace.inline45Template.length = PairedAllInlineCoreTrace.inline45Template := by
  rfl

theorem inline45_instructionPC :
    Artifact.submissionArtifact.instructionPC 2522 = 3154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline45Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline45Template 2522 inline45_slice
    (by
      change 2522 + PairedAllInlineCoreTrace.inline45Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline45Template) (by decide))
    (by decide)

theorem inline45Site_startPC : inline45Site.startPC = UInt256.ofNat 3154 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2522) = UInt256.ofNat 3154
  rw [inline45_instructionPC]

theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2564).take PairedAllInlineCoreTrace.inline46Template.length = PairedAllInlineCoreTrace.inline46Template := by
  rfl

theorem inline46_instructionPC :
    Artifact.submissionArtifact.instructionPC 2564 = 3202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline46Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline46Template 2564 inline46_slice
    (by
      change 2564 + PairedAllInlineCoreTrace.inline46Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline46Template) (by decide))
    (by decide)

theorem inline46Site_startPC : inline46Site.startPC = UInt256.ofNat 3202 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2564) = UInt256.ofNat 3202
  rw [inline46_instructionPC]

theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2597).take PairedAllInlineCoreTrace.groupK_consumed47Template.length = PairedAllInlineCoreTrace.groupK_consumed47Template := by
  rfl

theorem inline47_instructionPC :
    Artifact.submissionArtifact.instructionPC 2597 = 3241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.groupK_consumed47Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.groupK_consumed47Template 2597 inline47_slice
    (by
      change 2597 + PairedAllInlineCoreTrace.groupK_consumed47Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.groupK_consumed47Template) (by decide))
    (by decide)

theorem inline47Site_startPC : inline47Site.startPC = UInt256.ofNat 3241 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2597) = UInt256.ofNat 3241
  rw [inline47_instructionPC]

theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2629).take PairedAllInlineCoreTrace.group48Template.length = PairedAllInlineCoreTrace.group48Template := by
  rfl

theorem group48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2629 = 3279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group48Template 2629 group48_slice
    (by
      change 2629 + PairedAllInlineCoreTrace.group48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group48Template) (by decide))
    (by decide)

theorem group48Site_startPC : group48Site.startPC = UInt256.ofNat 3279 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2629) = UInt256.ofNat 3279
  rw [group48_instructionPC]

theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2630).take PairedAllInlineCoreTrace.inline48Template.length = PairedAllInlineCoreTrace.inline48Template := by
  rfl

theorem inline48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2630 = 3300 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline48Template 2630 inline48_slice
    (by
      change 2630 + PairedAllInlineCoreTrace.inline48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline48Template) (by decide))
    (by decide)

theorem inline48Site_startPC : inline48Site.startPC = UInt256.ofNat 3300 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2630) = UInt256.ofNat 3300
  rw [inline48_instructionPC]

theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2679).take PairedAllInlineCoreTrace.inline49Template.length = PairedAllInlineCoreTrace.inline49Template := by
  rfl

theorem inline49_instructionPC :
    Artifact.submissionArtifact.instructionPC 2679 = 3355 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline49Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline49Template 2679 inline49_slice
    (by
      change 2679 + PairedAllInlineCoreTrace.inline49Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline49Template) (by decide))
    (by decide)

theorem inline49Site_startPC : inline49Site.startPC = UInt256.ofNat 3355 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2679) = UInt256.ofNat 3355
  rw [inline49_instructionPC]

theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2727).take PairedAllInlineCoreTrace.inline50Template.length = PairedAllInlineCoreTrace.inline50Template := by
  rfl

theorem inline50_instructionPC :
    Artifact.submissionArtifact.instructionPC 2727 = 3410 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline50Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline50Template 2727 inline50_slice
    (by
      change 2727 + PairedAllInlineCoreTrace.inline50Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline50Template) (by decide))
    (by decide)

theorem inline50Site_startPC : inline50Site.startPC = UInt256.ofNat 3410 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2727) = UInt256.ofNat 3410
  rw [inline50_instructionPC]

theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2775).take PairedAllInlineCoreTrace.inline51Template.length = PairedAllInlineCoreTrace.inline51Template := by
  rfl

theorem inline51_instructionPC :
    Artifact.submissionArtifact.instructionPC 2775 = 3465 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline51Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline51Template 2775 inline51_slice
    (by
      change 2775 + PairedAllInlineCoreTrace.inline51Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline51Template) (by decide))
    (by decide)

theorem inline51Site_startPC : inline51Site.startPC = UInt256.ofNat 3465 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2775) = UInt256.ofNat 3465
  rw [inline51_instructionPC]

theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2823).take PairedAllInlineCoreTrace.inline52Template.length = PairedAllInlineCoreTrace.inline52Template := by
  rfl

theorem inline52_instructionPC :
    Artifact.submissionArtifact.instructionPC 2823 = 3519 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline52Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline52Template 2823 inline52_slice
    (by
      change 2823 + PairedAllInlineCoreTrace.inline52Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline52Template) (by decide))
    (by decide)

theorem inline52Site_startPC : inline52Site.startPC = UInt256.ofNat 3519 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2823) = UInt256.ofNat 3519
  rw [inline52_instructionPC]

theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2863).take PairedAllInlineCoreTrace.inline53Template.length = PairedAllInlineCoreTrace.inline53Template := by
  rfl

theorem inline53_instructionPC :
    Artifact.submissionArtifact.instructionPC 2863 = 3564 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline53Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline53Template 2863 inline53_slice
    (by
      change 2863 + PairedAllInlineCoreTrace.inline53Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline53Template) (by decide))
    (by decide)

theorem inline53Site_startPC : inline53Site.startPC = UInt256.ofNat 3564 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2863) = UInt256.ofNat 3564
  rw [inline53_instructionPC]

theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2911).take PairedAllInlineCoreTrace.inline54Template.length = PairedAllInlineCoreTrace.inline54Template := by
  rfl

theorem inline54_instructionPC :
    Artifact.submissionArtifact.instructionPC 2911 = 3619 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline54Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline54Template 2911 inline54_slice
    (by
      change 2911 + PairedAllInlineCoreTrace.inline54Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline54Template) (by decide))
    (by decide)

theorem inline54Site_startPC : inline54Site.startPC = UInt256.ofNat 3619 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2911) = UInt256.ofNat 3619
  rw [inline54_instructionPC]

theorem inline55_slice :
    (Artifact.submissionArtifact.instructions.drop 2959).take PairedAllInlineCoreTrace.inline55Template.length = PairedAllInlineCoreTrace.inline55Template := by
  rfl

theorem inline55_instructionPC :
    Artifact.submissionArtifact.instructionPC 2959 = 3674 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline55Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline55Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline55Template 2959 inline55_slice
    (by
      change 2959 + PairedAllInlineCoreTrace.inline55Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline55Template) (by decide))
    (by decide)

theorem inline55Site_startPC : inline55Site.startPC = UInt256.ofNat 3674 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2959) = UInt256.ofNat 3674
  rw [inline55_instructionPC]

theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 3008).take PairedAllInlineCoreTrace.inline56Template.length = PairedAllInlineCoreTrace.inline56Template := by
  rfl

theorem inline56_instructionPC :
    Artifact.submissionArtifact.instructionPC 3008 = 3729 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline56Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline56Template 3008 inline56_slice
    (by
      change 3008 + PairedAllInlineCoreTrace.inline56Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline56Template) (by decide))
    (by decide)

theorem inline56Site_startPC : inline56Site.startPC = UInt256.ofNat 3729 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3008) = UInt256.ofNat 3729
  rw [inline56_instructionPC]

theorem inline57_slice :
    (Artifact.submissionArtifact.instructions.drop 3056).take PairedAllInlineCoreTrace.inline57Template.length = PairedAllInlineCoreTrace.inline57Template := by
  rfl

theorem inline57_instructionPC :
    Artifact.submissionArtifact.instructionPC 3056 = 3784 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline57Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline57Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline57Template 3056 inline57_slice
    (by
      change 3056 + PairedAllInlineCoreTrace.inline57Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline57Template) (by decide))
    (by decide)

theorem inline57Site_startPC : inline57Site.startPC = UInt256.ofNat 3784 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3056) = UInt256.ofNat 3784
  rw [inline57_instructionPC]

theorem inline58_slice :
    (Artifact.submissionArtifact.instructions.drop 3104).take PairedAllInlineCoreTrace.inline58Template.length = PairedAllInlineCoreTrace.inline58Template := by
  rfl

theorem inline58_instructionPC :
    Artifact.submissionArtifact.instructionPC 3104 = 3839 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline58Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline58Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline58Template 3104 inline58_slice
    (by
      change 3104 + PairedAllInlineCoreTrace.inline58Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline58Template) (by decide))
    (by decide)

theorem inline58Site_startPC : inline58Site.startPC = UInt256.ofNat 3839 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3104) = UInt256.ofNat 3839
  rw [inline58_instructionPC]

theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 3153).take PairedAllInlineCoreTrace.inline59Template.length = PairedAllInlineCoreTrace.inline59Template := by
  rfl

theorem inline59_instructionPC :
    Artifact.submissionArtifact.instructionPC 3153 = 3895 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline59Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline59Template 3153 inline59_slice
    (by
      change 3153 + PairedAllInlineCoreTrace.inline59Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline59Template) (by decide))
    (by decide)

theorem inline59Site_startPC : inline59Site.startPC = UInt256.ofNat 3895 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3153) = UInt256.ofNat 3895
  rw [inline59_instructionPC]

theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 3202).take PairedAllInlineCoreTrace.inline60Template.length = PairedAllInlineCoreTrace.inline60Template := by
  rfl

theorem inline60_instructionPC :
    Artifact.submissionArtifact.instructionPC 3202 = 3951 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline60Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline60Template 3202 inline60_slice
    (by
      change 3202 + PairedAllInlineCoreTrace.inline60Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline60Template) (by decide))
    (by decide)

theorem inline60Site_startPC : inline60Site.startPC = UInt256.ofNat 3951 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3202) = UInt256.ofNat 3951
  rw [inline60_instructionPC]

theorem inline61_slice :
    (Artifact.submissionArtifact.instructions.drop 3251).take PairedAllInlineCoreTrace.inline61Template.length = PairedAllInlineCoreTrace.inline61Template := by
  rfl

theorem inline61_instructionPC :
    Artifact.submissionArtifact.instructionPC 3251 = 4007 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline61Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline61Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline61Template 3251 inline61_slice
    (by
      change 3251 + PairedAllInlineCoreTrace.inline61Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline61Template) (by decide))
    (by decide)

theorem inline61Site_startPC : inline61Site.startPC = UInt256.ofNat 4007 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3251) = UInt256.ofNat 4007
  rw [inline61_instructionPC]

theorem inline62_slice :
    (Artifact.submissionArtifact.instructions.drop 3299).take PairedAllInlineCoreTrace.inline62Template.length = PairedAllInlineCoreTrace.inline62Template := by
  rfl

theorem inline62_instructionPC :
    Artifact.submissionArtifact.instructionPC 3299 = 4062 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline62Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline62Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline62Template 3299 inline62_slice
    (by
      change 3299 + PairedAllInlineCoreTrace.inline62Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline62Template) (by decide))
    (by decide)

theorem inline62Site_startPC : inline62Site.startPC = UInt256.ofNat 4062 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3299) = UInt256.ofNat 4062
  rw [inline62_instructionPC]

theorem inline63_slice :
    (Artifact.submissionArtifact.instructions.drop 3348).take PairedAllInlineCoreTrace.inline63Template.length = PairedAllInlineCoreTrace.inline63Template := by
  rfl

theorem inline63_instructionPC :
    Artifact.submissionArtifact.instructionPC 3348 = 4118 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline63Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline63Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline63Template 3348 inline63_slice
    (by
      change 3348 + PairedAllInlineCoreTrace.inline63Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline63Template) (by decide))
    (by decide)

theorem inline63Site_startPC : inline63Site.startPC = UInt256.ofNat 4118 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3348) = UInt256.ofNat 4118
  rw [inline63_instructionPC]

theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3396).take PairedAllInlineCoreTrace.group64Template.length = PairedAllInlineCoreTrace.group64Template := by
  rfl

theorem group64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3396 = 4173 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group64Template 3396 group64_slice
    (by
      change 3396 + PairedAllInlineCoreTrace.group64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group64Template) (by decide))
    (by decide)

theorem group64Site_startPC : group64Site.startPC = UInt256.ofNat 4173 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3396) = UInt256.ofNat 4173
  rw [group64_instructionPC]

theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3399).take PairedAllInlineCoreTrace.inline64Template.length = PairedAllInlineCoreTrace.inline64Template := by
  rfl

theorem inline64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3399 = 4180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline64Template 3399 inline64_slice
    (by
      change 3399 + PairedAllInlineCoreTrace.inline64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline64Template) (by decide))
    (by decide)

theorem inline64Site_startPC : inline64Site.startPC = UInt256.ofNat 4180 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3399) = UInt256.ofNat 4180
  rw [inline64_instructionPC]

theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3445).take PairedAllInlineCoreTrace.inline65Template.length = PairedAllInlineCoreTrace.inline65Template := by
  rfl

theorem inline65_instructionPC :
    Artifact.submissionArtifact.instructionPC 3445 = 4233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline65Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline65Template 3445 inline65_slice
    (by
      change 3445 + PairedAllInlineCoreTrace.inline65Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline65Template) (by decide))
    (by decide)

theorem inline65Site_startPC : inline65Site.startPC = UInt256.ofNat 4233 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3445) = UInt256.ofNat 4233
  rw [inline65_instructionPC]

theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3491).take PairedAllInlineCoreTrace.inline66Template.length = PairedAllInlineCoreTrace.inline66Template := by
  rfl

theorem inline66_instructionPC :
    Artifact.submissionArtifact.instructionPC 3491 = 4285 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline66Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline66Template 3491 inline66_slice
    (by
      change 3491 + PairedAllInlineCoreTrace.inline66Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline66Template) (by decide))
    (by decide)

theorem inline66Site_startPC : inline66Site.startPC = UInt256.ofNat 4285 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3491) = UInt256.ofNat 4285
  rw [inline66_instructionPC]

theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3538).take PairedAllInlineCoreTrace.inline67Template.length = PairedAllInlineCoreTrace.inline67Template := by
  rfl

theorem inline67_instructionPC :
    Artifact.submissionArtifact.instructionPC 3538 = 4339 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline67Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline67Template 3538 inline67_slice
    (by
      change 3538 + PairedAllInlineCoreTrace.inline67Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline67Template) (by decide))
    (by decide)

theorem inline67Site_startPC : inline67Site.startPC = UInt256.ofNat 4339 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3538) = UInt256.ofNat 4339
  rw [inline67_instructionPC]

theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3584).take PairedAllInlineCoreTrace.inline68Template.length = PairedAllInlineCoreTrace.inline68Template := by
  rfl

theorem inline68_instructionPC :
    Artifact.submissionArtifact.instructionPC 3584 = 4392 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline68Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline68Template 3584 inline68_slice
    (by
      change 3584 + PairedAllInlineCoreTrace.inline68Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline68Template) (by decide))
    (by decide)

theorem inline68Site_startPC : inline68Site.startPC = UInt256.ofNat 4392 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3584) = UInt256.ofNat 4392
  rw [inline68_instructionPC]

theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3631).take PairedAllInlineCoreTrace.inline69Template.length = PairedAllInlineCoreTrace.inline69Template := by
  rfl

theorem inline69_instructionPC :
    Artifact.submissionArtifact.instructionPC 3631 = 4445 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline69Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline69Template 3631 inline69_slice
    (by
      change 3631 + PairedAllInlineCoreTrace.inline69Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline69Template) (by decide))
    (by decide)

theorem inline69Site_startPC : inline69Site.startPC = UInt256.ofNat 4445 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3631) = UInt256.ofNat 4445
  rw [inline69_instructionPC]

theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3677).take PairedAllInlineCoreTrace.inline70Template.length = PairedAllInlineCoreTrace.inline70Template := by
  rfl

theorem inline70_instructionPC :
    Artifact.submissionArtifact.instructionPC 3677 = 4498 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline70Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline70Template 3677 inline70_slice
    (by
      change 3677 + PairedAllInlineCoreTrace.inline70Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline70Template) (by decide))
    (by decide)

theorem inline70Site_startPC : inline70Site.startPC = UInt256.ofNat 4498 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3677) = UInt256.ofNat 4498
  rw [inline70_instructionPC]

theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3724).take PairedAllInlineCoreTrace.inline71Template.length = PairedAllInlineCoreTrace.inline71Template := by
  rfl

theorem inline71_instructionPC :
    Artifact.submissionArtifact.instructionPC 3724 = 4552 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline71Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline71Template 3724 inline71_slice
    (by
      change 3724 + PairedAllInlineCoreTrace.inline71Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline71Template) (by decide))
    (by decide)

theorem inline71Site_startPC : inline71Site.startPC = UInt256.ofNat 4552 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3724) = UInt256.ofNat 4552
  rw [inline71_instructionPC]

theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3770).take PairedAllInlineCoreTrace.inline72Template.length = PairedAllInlineCoreTrace.inline72Template := by
  rfl

theorem inline72_instructionPC :
    Artifact.submissionArtifact.instructionPC 3770 = 4605 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline72Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline72Template 3770 inline72_slice
    (by
      change 3770 + PairedAllInlineCoreTrace.inline72Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline72Template) (by decide))
    (by decide)

theorem inline72Site_startPC : inline72Site.startPC = UInt256.ofNat 4605 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3770) = UInt256.ofNat 4605
  rw [inline72_instructionPC]

theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3817).take PairedAllInlineCoreTrace.inline73Template.length = PairedAllInlineCoreTrace.inline73Template := by
  rfl

theorem inline73_instructionPC :
    Artifact.submissionArtifact.instructionPC 3817 = 4659 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline73Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline73Template 3817 inline73_slice
    (by
      change 3817 + PairedAllInlineCoreTrace.inline73Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline73Template) (by decide))
    (by decide)

theorem inline73Site_startPC : inline73Site.startPC = UInt256.ofNat 4659 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3817) = UInt256.ofNat 4659
  rw [inline73_instructionPC]

theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3864).take PairedAllInlineCoreTrace.inline74Template.length = PairedAllInlineCoreTrace.inline74Template := by
  rfl

theorem inline74_instructionPC :
    Artifact.submissionArtifact.instructionPC 3864 = 4712 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline74Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline74Template 3864 inline74_slice
    (by
      change 3864 + PairedAllInlineCoreTrace.inline74Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline74Template) (by decide))
    (by decide)

theorem inline74Site_startPC : inline74Site.startPC = UInt256.ofNat 4712 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3864) = UInt256.ofNat 4712
  rw [inline74_instructionPC]

theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3910).take PairedAllInlineCoreTrace.inline75Template.length = PairedAllInlineCoreTrace.inline75Template := by
  rfl

theorem inline75_instructionPC :
    Artifact.submissionArtifact.instructionPC 3910 = 4765 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline75Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline75Template 3910 inline75_slice
    (by
      change 3910 + PairedAllInlineCoreTrace.inline75Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline75Template) (by decide))
    (by decide)

theorem inline75Site_startPC : inline75Site.startPC = UInt256.ofNat 4765 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3910) = UInt256.ofNat 4765
  rw [inline75_instructionPC]

theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3956).take PairedAllInlineCoreTrace.inline76Template.length = PairedAllInlineCoreTrace.inline76Template := by
  rfl

theorem inline76_instructionPC :
    Artifact.submissionArtifact.instructionPC 3956 = 4818 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline76Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline76Template 3956 inline76_slice
    (by
      change 3956 + PairedAllInlineCoreTrace.inline76Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline76Template) (by decide))
    (by decide)

theorem inline76Site_startPC : inline76Site.startPC = UInt256.ofNat 4818 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3956) = UInt256.ofNat 4818
  rw [inline76_instructionPC]

theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 4003).take PairedAllInlineCoreTrace.inline77Template.length = PairedAllInlineCoreTrace.inline77Template := by
  rfl

theorem inline77_instructionPC :
    Artifact.submissionArtifact.instructionPC 4003 = 4871 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline77Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline77Template 4003 inline77_slice
    (by
      change 4003 + PairedAllInlineCoreTrace.inline77Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline77Template) (by decide))
    (by decide)

theorem inline77Site_startPC : inline77Site.startPC = UInt256.ofNat 4871 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4003) = UInt256.ofNat 4871
  rw [inline77_instructionPC]

theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 4050).take PairedAllInlineCoreTrace.inline78Template.length = PairedAllInlineCoreTrace.inline78Template := by
  rfl

theorem inline78_instructionPC :
    Artifact.submissionArtifact.instructionPC 4050 = 4925 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline78Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline78Template 4050 inline78_slice
    (by
      change 4050 + PairedAllInlineCoreTrace.inline78Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline78Template) (by decide))
    (by decide)

theorem inline78Site_startPC : inline78Site.startPC = UInt256.ofNat 4925 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4050) = UInt256.ofNat 4925
  rw [inline78_instructionPC]

theorem inline79_slice :
    (Artifact.submissionArtifact.instructions.drop 4097).take PairedAllInlineCoreTrace.inline79Template.length = PairedAllInlineCoreTrace.inline79Template := by
  rfl

theorem inline79_instructionPC :
    Artifact.submissionArtifact.instructionPC 4097 = 4979 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline79Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline79Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline79Template 4097 inline79_slice
    (by
      change 4097 + PairedAllInlineCoreTrace.inline79Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline79Template) (by decide))
    (by decide)

theorem inline79Site_startPC : inline79Site.startPC = UInt256.ofNat 4979 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4097) = UInt256.ofNat 4979
  rw [inline79_instructionPC]

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
      {s with pc := UInt256.ofNat 5032, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (coreCryptoResult words left right) rho} :=
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
#print axioms wholeSites
#print axioms gasSteps_core_normalized

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreSites


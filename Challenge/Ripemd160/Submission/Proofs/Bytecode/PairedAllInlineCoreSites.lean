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
    (Artifact.submissionArtifact.instructions.drop 499).take PairedAllInlineCoreTrace.group0Template.length = PairedAllInlineCoreTrace.group0Template := by
  rfl

theorem group0_instructionPC :
    Artifact.submissionArtifact.instructionPC 499 = 822 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group0Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group0Template 499 group0_slice
    (by
      change 499 + PairedAllInlineCoreTrace.group0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group0Template) (by decide))
    (by decide)

theorem group0Site_startPC : group0Site.startPC = UInt256.ofNat 822 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 499) = UInt256.ofNat 822
  rw [group0_instructionPC]

theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 502).take PairedSynthCoreTrace.inline0Template.length = PairedSynthCoreTrace.inline0Template := by
  rfl

theorem inline0_instructionPC :
    Artifact.submissionArtifact.instructionPC 502 = 830 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline0Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline0Template 502 inline0_slice
    (by
      change 502 + PairedSynthCoreTrace.inline0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline0Template) (by decide))
    (by decide)

theorem inline0Site_startPC : inline0Site.startPC = UInt256.ofNat 830 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 502) = UInt256.ofNat 830
  rw [inline0_instructionPC]

theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 546).take PairedSynthCoreTrace.inline1Template.length = PairedSynthCoreTrace.inline1Template := by
  rfl

theorem inline1_instructionPC :
    Artifact.submissionArtifact.instructionPC 546 = 880 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline1Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline1Template 546 inline1_slice
    (by
      change 546 + PairedSynthCoreTrace.inline1Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline1Template) (by decide))
    (by decide)

theorem inline1Site_startPC : inline1Site.startPC = UInt256.ofNat 880 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 546) = UInt256.ofNat 880
  rw [inline1_instructionPC]

theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 590).take PairedSynthCoreTrace.inline2Template.length = PairedSynthCoreTrace.inline2Template := by
  rfl

theorem inline2_instructionPC :
    Artifact.submissionArtifact.instructionPC 590 = 930 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline2Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline2Template 590 inline2_slice
    (by
      change 590 + PairedSynthCoreTrace.inline2Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline2Template) (by decide))
    (by decide)

theorem inline2Site_startPC : inline2Site.startPC = UInt256.ofNat 930 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 590) = UInt256.ofNat 930
  rw [inline2_instructionPC]

theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 634).take PairedSynthCoreTrace.inline3Template.length = PairedSynthCoreTrace.inline3Template := by
  rfl

theorem inline3_instructionPC :
    Artifact.submissionArtifact.instructionPC 634 = 981 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline3Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline3Template 634 inline3_slice
    (by
      change 634 + PairedSynthCoreTrace.inline3Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline3Template) (by decide))
    (by decide)

theorem inline3Site_startPC : inline3Site.startPC = UInt256.ofNat 981 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 634) = UInt256.ofNat 981
  rw [inline3_instructionPC]

theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 676).take PairedSynthCoreTrace.inline4Template.length = PairedSynthCoreTrace.inline4Template := by
  rfl

theorem inline4_instructionPC :
    Artifact.submissionArtifact.instructionPC 676 = 1028 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline4Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline4Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline4Template 676 inline4_slice
    (by
      change 676 + PairedSynthCoreTrace.inline4Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline4Template) (by decide))
    (by decide)

theorem inline4Site_startPC : inline4Site.startPC = UInt256.ofNat 1028 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 676) = UInt256.ofNat 1028
  rw [inline4_instructionPC]

theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 720).take PairedSynthCoreTrace.inline5Template.length = PairedSynthCoreTrace.inline5Template := by
  rfl

theorem inline5_instructionPC :
    Artifact.submissionArtifact.instructionPC 720 = 1079 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline5Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline5Template 720 inline5_slice
    (by
      change 720 + PairedSynthCoreTrace.inline5Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline5Template) (by decide))
    (by decide)

theorem inline5Site_startPC : inline5Site.startPC = UInt256.ofNat 1079 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 720) = UInt256.ofNat 1079
  rw [inline5_instructionPC]

theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 764).take PairedSynthCoreTrace.inline6Template.length = PairedSynthCoreTrace.inline6Template := by
  rfl

theorem inline6_instructionPC :
    Artifact.submissionArtifact.instructionPC 764 = 1130 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline6Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline6Template 764 inline6_slice
    (by
      change 764 + PairedSynthCoreTrace.inline6Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline6Template) (by decide))
    (by decide)

theorem inline6Site_startPC : inline6Site.startPC = UInt256.ofNat 1130 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 764) = UInt256.ofNat 1130
  rw [inline6_instructionPC]

theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 808).take PairedSynthCoreTrace.inline7Template.length = PairedSynthCoreTrace.inline7Template := by
  rfl

theorem inline7_instructionPC :
    Artifact.submissionArtifact.instructionPC 808 = 1181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline7Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline7Template 808 inline7_slice
    (by
      change 808 + PairedSynthCoreTrace.inline7Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline7Template) (by decide))
    (by decide)

theorem inline7Site_startPC : inline7Site.startPC = UInt256.ofNat 1181 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 808) = UInt256.ofNat 1181
  rw [inline7_instructionPC]

theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 852).take PairedSynthCoreTrace.inline8Template.length = PairedSynthCoreTrace.inline8Template := by
  rfl

theorem inline8_instructionPC :
    Artifact.submissionArtifact.instructionPC 852 = 1232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline8Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline8Template 852 inline8_slice
    (by
      change 852 + PairedSynthCoreTrace.inline8Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline8Template) (by decide))
    (by decide)

theorem inline8Site_startPC : inline8Site.startPC = UInt256.ofNat 1232 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 852) = UInt256.ofNat 1232
  rw [inline8_instructionPC]

theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 896).take PairedSynthCoreTrace.inline9Template.length = PairedSynthCoreTrace.inline9Template := by
  rfl

theorem inline9_instructionPC :
    Artifact.submissionArtifact.instructionPC 896 = 1283 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline9Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline9Template 896 inline9_slice
    (by
      change 896 + PairedSynthCoreTrace.inline9Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline9Template) (by decide))
    (by decide)

theorem inline9Site_startPC : inline9Site.startPC = UInt256.ofNat 1283 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 896) = UInt256.ofNat 1283
  rw [inline9_instructionPC]

theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 940).take PairedSynthCoreTrace.inline10Template.length = PairedSynthCoreTrace.inline10Template := by
  rfl

theorem inline10_instructionPC :
    Artifact.submissionArtifact.instructionPC 940 = 1334 := by
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

theorem inline10Site_startPC : inline10Site.startPC = UInt256.ofNat 1334 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 940) = UInt256.ofNat 1334
  rw [inline10_instructionPC]

theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 984).take PairedSynthCoreTrace.inline11Template.length = PairedSynthCoreTrace.inline11Template := by
  rfl

theorem inline11_instructionPC :
    Artifact.submissionArtifact.instructionPC 984 = 1385 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline11Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline11Template 984 inline11_slice
    (by
      change 984 + PairedSynthCoreTrace.inline11Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline11Template) (by decide))
    (by decide)

theorem inline11Site_startPC : inline11Site.startPC = UInt256.ofNat 1385 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 984) = UInt256.ofNat 1385
  rw [inline11_instructionPC]

theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1028).take PairedSynthCoreTrace.inline12Template.length = PairedSynthCoreTrace.inline12Template := by
  rfl

theorem inline12_instructionPC :
    Artifact.submissionArtifact.instructionPC 1028 = 1436 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline12Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline12Template 1028 inline12_slice
    (by
      change 1028 + PairedSynthCoreTrace.inline12Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline12Template) (by decide))
    (by decide)

theorem inline12Site_startPC : inline12Site.startPC = UInt256.ofNat 1436 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1028) = UInt256.ofNat 1436
  rw [inline12_instructionPC]

theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1072).take PairedSynthCoreTrace.inline13Template.length = PairedSynthCoreTrace.inline13Template := by
  rfl

theorem inline13_instructionPC :
    Artifact.submissionArtifact.instructionPC 1072 = 1486 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline13Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline13Template 1072 inline13_slice
    (by
      change 1072 + PairedSynthCoreTrace.inline13Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline13Template) (by decide))
    (by decide)

theorem inline13Site_startPC : inline13Site.startPC = UInt256.ofNat 1486 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1072) = UInt256.ofNat 1486
  rw [inline13_instructionPC]

theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1116).take PairedSynthCoreTrace.inline14Template.length = PairedSynthCoreTrace.inline14Template := by
  rfl

theorem inline14_instructionPC :
    Artifact.submissionArtifact.instructionPC 1116 = 1537 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline14Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline14Template 1116 inline14_slice
    (by
      change 1116 + PairedSynthCoreTrace.inline14Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline14Template) (by decide))
    (by decide)

theorem inline14Site_startPC : inline14Site.startPC = UInt256.ofNat 1537 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1116) = UInt256.ofNat 1537
  rw [inline14_instructionPC]

theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1160).take PairedSynthCoreTrace.inline15Template.length = PairedSynthCoreTrace.inline15Template := by
  rfl

theorem inline15_instructionPC :
    Artifact.submissionArtifact.instructionPC 1160 = 1588 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedSynthCoreTrace.inline15Template :=
  StackSiteBuilder.ofSlice PairedSynthCoreTrace.inline15Template 1160 inline15_slice
    (by
      change 1160 + PairedSynthCoreTrace.inline15Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedSynthCoreTrace.inline15Template) (by decide))
    (by decide)

theorem inline15Site_startPC : inline15Site.startPC = UInt256.ofNat 1588 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1160) = UInt256.ofNat 1588
  rw [inline15_instructionPC]

theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1204).take PairedAllInlineCoreTrace.group16Template.length = PairedAllInlineCoreTrace.group16Template := by
  rfl

theorem group16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1204 = 1639 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group16Template 1204 group16_slice
    (by
      change 1204 + PairedAllInlineCoreTrace.group16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group16Template) (by decide))
    (by decide)

theorem group16Site_startPC : group16Site.startPC = UInt256.ofNat 1639 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1204) = UInt256.ofNat 1639
  rw [group16_instructionPC]

theorem inline16_slice :
    (Artifact.submissionArtifact.instructions.drop 1207).take PairedAllInlineNewPairs.inline16Template.length = PairedAllInlineNewPairs.inline16Template := by
  rfl

theorem inline16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1207 = 1662 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline16Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline16Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline16Template 1207 inline16_slice
    (by
      change 1207 + PairedAllInlineNewPairs.inline16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline16Template) (by decide))
    (by decide)

theorem inline16Site_startPC : inline16Site.startPC = UInt256.ofNat 1662 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1207) = UInt256.ofNat 1662
  rw [inline16_instructionPC]

theorem inline17_slice :
    (Artifact.submissionArtifact.instructions.drop 1253).take PairedAllInlineNewPairs.inline17Template.length = PairedAllInlineNewPairs.inline17Template := by
  rfl

theorem inline17_instructionPC :
    Artifact.submissionArtifact.instructionPC 1253 = 1715 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline17Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline17Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline17Template 1253 inline17_slice
    (by
      change 1253 + PairedAllInlineNewPairs.inline17Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline17Template) (by decide))
    (by decide)

theorem inline17Site_startPC : inline17Site.startPC = UInt256.ofNat 1715 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1253) = UInt256.ofNat 1715
  rw [inline17_instructionPC]

theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1299).take PairedAllInlineCoreTrace.inline18Template.length = PairedAllInlineCoreTrace.inline18Template := by
  rfl

theorem inline18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1299 = 1768 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline18Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline18Template 1299 inline18_slice
    (by
      change 1299 + PairedAllInlineCoreTrace.inline18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline18Template) (by decide))
    (by decide)

theorem inline18Site_startPC : inline18Site.startPC = UInt256.ofNat 1768 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1299) = UInt256.ofNat 1768
  rw [inline18_instructionPC]

theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1345).take PairedAllInlineCoreTrace.inline19Template.length = PairedAllInlineCoreTrace.inline19Template := by
  rfl

theorem inline19_instructionPC :
    Artifact.submissionArtifact.instructionPC 1345 = 1821 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline19Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline19Template 1345 inline19_slice
    (by
      change 1345 + PairedAllInlineCoreTrace.inline19Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline19Template) (by decide))
    (by decide)

theorem inline19Site_startPC : inline19Site.startPC = UInt256.ofNat 1821 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1345) = UInt256.ofNat 1821
  rw [inline19_instructionPC]

theorem inline20_slice :
    (Artifact.submissionArtifact.instructions.drop 1391).take PairedAllInlineCoreTrace.inline20Template.length = PairedAllInlineCoreTrace.inline20Template := by
  rfl

theorem inline20_instructionPC :
    Artifact.submissionArtifact.instructionPC 1391 = 1873 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline20Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline20Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline20Template 1391 inline20_slice
    (by
      change 1391 + PairedAllInlineCoreTrace.inline20Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline20Template) (by decide))
    (by decide)

theorem inline20Site_startPC : inline20Site.startPC = UInt256.ofNat 1873 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1391) = UInt256.ofNat 1873
  rw [inline20_instructionPC]

theorem inline21_slice :
    (Artifact.submissionArtifact.instructions.drop 1435).take PairedAllInlineCoreTrace.inline21Template.length = PairedAllInlineCoreTrace.inline21Template := by
  rfl

theorem inline21_instructionPC :
    Artifact.submissionArtifact.instructionPC 1435 = 1922 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline21Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline21Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline21Template 1435 inline21_slice
    (by
      change 1435 + PairedAllInlineCoreTrace.inline21Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline21Template) (by decide))
    (by decide)

theorem inline21Site_startPC : inline21Site.startPC = UInt256.ofNat 1922 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1435) = UInt256.ofNat 1922
  rw [inline21_instructionPC]

theorem inline22_slice :
    (Artifact.submissionArtifact.instructions.drop 1479).take PairedAllInlineCoreTrace.inline22Template.length = PairedAllInlineCoreTrace.inline22Template := by
  rfl

theorem inline22_instructionPC :
    Artifact.submissionArtifact.instructionPC 1479 = 1972 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline22Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline22Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline22Template 1479 inline22_slice
    (by
      change 1479 + PairedAllInlineCoreTrace.inline22Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline22Template) (by decide))
    (by decide)

theorem inline22Site_startPC : inline22Site.startPC = UInt256.ofNat 1972 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1479) = UInt256.ofNat 1972
  rw [inline22_instructionPC]

theorem inline23_slice :
    (Artifact.submissionArtifact.instructions.drop 1525).take PairedAllInlineCoreTrace.inline23Template.length = PairedAllInlineCoreTrace.inline23Template := by
  rfl

theorem inline23_instructionPC :
    Artifact.submissionArtifact.instructionPC 1525 = 2025 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline23Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline23Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline23Template 1525 inline23_slice
    (by
      change 1525 + PairedAllInlineCoreTrace.inline23Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline23Template) (by decide))
    (by decide)

theorem inline23Site_startPC : inline23Site.startPC = UInt256.ofNat 2025 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1525) = UInt256.ofNat 2025
  rw [inline23_instructionPC]

theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1571).take PairedAllInlineCoreTrace.inline24Template.length = PairedAllInlineCoreTrace.inline24Template := by
  rfl

theorem inline24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1571 = 2078 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline24Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline24Template 1571 inline24_slice
    (by
      change 1571 + PairedAllInlineCoreTrace.inline24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline24Template) (by decide))
    (by decide)

theorem inline24Site_startPC : inline24Site.startPC = UInt256.ofNat 2078 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1571) = UInt256.ofNat 2078
  rw [inline24_instructionPC]

theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1611).take PairedAllInlineCoreTrace.inline25Template.length = PairedAllInlineCoreTrace.inline25Template := by
  rfl

theorem inline25_instructionPC :
    Artifact.submissionArtifact.instructionPC 1611 = 2124 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline25Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline25Template 1611 inline25_slice
    (by
      change 1611 + PairedAllInlineCoreTrace.inline25Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline25Template) (by decide))
    (by decide)

theorem inline25Site_startPC : inline25Site.startPC = UInt256.ofNat 2124 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1611) = UInt256.ofNat 2124
  rw [inline25_instructionPC]

theorem inline26_slice :
    (Artifact.submissionArtifact.instructions.drop 1657).take PairedAllInlineCoreTrace.inline26Template.length = PairedAllInlineCoreTrace.inline26Template := by
  rfl

theorem inline26_instructionPC :
    Artifact.submissionArtifact.instructionPC 1657 = 2176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline26Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline26Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline26Template 1657 inline26_slice
    (by
      change 1657 + PairedAllInlineCoreTrace.inline26Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline26Template) (by decide))
    (by decide)

theorem inline26Site_startPC : inline26Site.startPC = UInt256.ofNat 2176 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1657) = UInt256.ofNat 2176
  rw [inline26_instructionPC]

theorem inline27_slice :
    (Artifact.submissionArtifact.instructions.drop 1703).take PairedAllInlineCoreTrace.inline27Template.length = PairedAllInlineCoreTrace.inline27Template := by
  rfl

theorem inline27_instructionPC :
    Artifact.submissionArtifact.instructionPC 1703 = 2229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline27Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline27Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline27Template 1703 inline27_slice
    (by
      change 1703 + PairedAllInlineCoreTrace.inline27Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline27Template) (by decide))
    (by decide)

theorem inline27Site_startPC : inline27Site.startPC = UInt256.ofNat 2229 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1703) = UInt256.ofNat 2229
  rw [inline27_instructionPC]

theorem inline28_slice :
    (Artifact.submissionArtifact.instructions.drop 1749).take PairedAllInlineNewPairs.inline28Template.length = PairedAllInlineNewPairs.inline28Template := by
  rfl

theorem inline28_instructionPC :
    Artifact.submissionArtifact.instructionPC 1749 = 2282 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline28Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline28Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline28Template 1749 inline28_slice
    (by
      change 1749 + PairedAllInlineNewPairs.inline28Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline28Template) (by decide))
    (by decide)

theorem inline28Site_startPC : inline28Site.startPC = UInt256.ofNat 2282 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1749) = UInt256.ofNat 2282
  rw [inline28_instructionPC]

theorem inline29_slice :
    (Artifact.submissionArtifact.instructions.drop 1795).take PairedAllInlineNewPairs.inline29Template.length = PairedAllInlineNewPairs.inline29Template := by
  rfl

theorem inline29_instructionPC :
    Artifact.submissionArtifact.instructionPC 1795 = 2335 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline29Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineNewPairs.inline29Template :=
  StackSiteBuilder.ofSlice PairedAllInlineNewPairs.inline29Template 1795 inline29_slice
    (by
      change 1795 + PairedAllInlineNewPairs.inline29Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineNewPairs.inline29Template) (by decide))
    (by decide)

theorem inline29Site_startPC : inline29Site.startPC = UInt256.ofNat 2335 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1795) = UInt256.ofNat 2335
  rw [inline29_instructionPC]

theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1841).take PairedAllInlineCoreTrace.inline30Template.length = PairedAllInlineCoreTrace.inline30Template := by
  rfl

theorem inline30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1841 = 2388 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline30Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline30Template 1841 inline30_slice
    (by
      change 1841 + PairedAllInlineCoreTrace.inline30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline30Template) (by decide))
    (by decide)

theorem inline30Site_startPC : inline30Site.startPC = UInt256.ofNat 2388 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1841) = UInt256.ofNat 2388
  rw [inline30_instructionPC]

theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1881).take PairedAllInlineCoreTrace.inline31Template.length = PairedAllInlineCoreTrace.inline31Template := by
  rfl

theorem inline31_instructionPC :
    Artifact.submissionArtifact.instructionPC 1881 = 2433 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline31Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline31Template 1881 inline31_slice
    (by
      change 1881 + PairedAllInlineCoreTrace.inline31Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline31Template) (by decide))
    (by decide)

theorem inline31Site_startPC : inline31Site.startPC = UInt256.ofNat 2433 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1881) = UInt256.ofNat 2433
  rw [inline31_instructionPC]

theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1925).take PairedAllInlineCoreTrace.group32Template.length = PairedAllInlineCoreTrace.group32Template := by
  rfl

theorem group32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1925 = 2483 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group32Template 1925 group32_slice
    (by
      change 1925 + PairedAllInlineCoreTrace.group32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group32Template) (by decide))
    (by decide)

theorem group32Site_startPC : group32Site.startPC = UInt256.ofNat 2483 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1925) = UInt256.ofNat 2483
  rw [group32_instructionPC]

theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1928).take PairedAllInlineCoreTrace.inline32Template.length = PairedAllInlineCoreTrace.inline32Template := by
  rfl

theorem inline32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1928 = 2507 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline32Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline32Template 1928 inline32_slice
    (by
      change 1928 + PairedAllInlineCoreTrace.inline32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline32Template) (by decide))
    (by decide)

theorem inline32Site_startPC : inline32Site.startPC = UInt256.ofNat 2507 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1928) = UInt256.ofNat 2507
  rw [inline32_instructionPC]

theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 1967).take PairedAllInlineCoreTrace.inline33Template.length = PairedAllInlineCoreTrace.inline33Template := by
  rfl

theorem inline33_instructionPC :
    Artifact.submissionArtifact.instructionPC 1967 = 2553 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline33Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline33Template 1967 inline33_slice
    (by
      change 1967 + PairedAllInlineCoreTrace.inline33Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline33Template) (by decide))
    (by decide)

theorem inline33Site_startPC : inline33Site.startPC = UInt256.ofNat 2553 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1967) = UInt256.ofNat 2553
  rw [inline33_instructionPC]

theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 2006).take PairedAllInlineCoreTrace.inline34Template.length = PairedAllInlineCoreTrace.inline34Template := by
  rfl

theorem inline34_instructionPC :
    Artifact.submissionArtifact.instructionPC 2006 = 2599 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline34Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline34Template 2006 inline34_slice
    (by
      change 2006 + PairedAllInlineCoreTrace.inline34Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline34Template) (by decide))
    (by decide)

theorem inline34Site_startPC : inline34Site.startPC = UInt256.ofNat 2599 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2006) = UInt256.ofNat 2599
  rw [inline34_instructionPC]

theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 2045).take PairedAllInlineCoreTrace.inline35Template.length = PairedAllInlineCoreTrace.inline35Template := by
  rfl

theorem inline35_instructionPC :
    Artifact.submissionArtifact.instructionPC 2045 = 2645 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline35Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline35Template 2045 inline35_slice
    (by
      change 2045 + PairedAllInlineCoreTrace.inline35Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline35Template) (by decide))
    (by decide)

theorem inline35Site_startPC : inline35Site.startPC = UInt256.ofNat 2645 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2045) = UInt256.ofNat 2645
  rw [inline35_instructionPC]

theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 2084).take PairedAllInlineCoreTrace.inline36Template.length = PairedAllInlineCoreTrace.inline36Template := by
  rfl

theorem inline36_instructionPC :
    Artifact.submissionArtifact.instructionPC 2084 = 2691 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline36Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline36Template 2084 inline36_slice
    (by
      change 2084 + PairedAllInlineCoreTrace.inline36Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline36Template) (by decide))
    (by decide)

theorem inline36Site_startPC : inline36Site.startPC = UInt256.ofNat 2691 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2084) = UInt256.ofNat 2691
  rw [inline36_instructionPC]

theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 2123).take PairedAllInlineCoreTrace.inline37Template.length = PairedAllInlineCoreTrace.inline37Template := by
  rfl

theorem inline37_instructionPC :
    Artifact.submissionArtifact.instructionPC 2123 = 2737 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline37Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline37Template 2123 inline37_slice
    (by
      change 2123 + PairedAllInlineCoreTrace.inline37Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline37Template) (by decide))
    (by decide)

theorem inline37Site_startPC : inline37Site.startPC = UInt256.ofNat 2737 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2123) = UInt256.ofNat 2737
  rw [inline37_instructionPC]

theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 2162).take PairedAllInlineCoreTrace.inline38Template.length = PairedAllInlineCoreTrace.inline38Template := by
  rfl

theorem inline38_instructionPC :
    Artifact.submissionArtifact.instructionPC 2162 = 2783 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline38Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline38Template 2162 inline38_slice
    (by
      change 2162 + PairedAllInlineCoreTrace.inline38Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline38Template) (by decide))
    (by decide)

theorem inline38Site_startPC : inline38Site.startPC = UInt256.ofNat 2783 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2162) = UInt256.ofNat 2783
  rw [inline38_instructionPC]

theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 2201).take PairedAllInlineCoreTrace.inline39Template.length = PairedAllInlineCoreTrace.inline39Template := by
  rfl

theorem inline39_instructionPC :
    Artifact.submissionArtifact.instructionPC 2201 = 2829 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline39Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline39Template 2201 inline39_slice
    (by
      change 2201 + PairedAllInlineCoreTrace.inline39Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline39Template) (by decide))
    (by decide)

theorem inline39Site_startPC : inline39Site.startPC = UInt256.ofNat 2829 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2201) = UInt256.ofNat 2829
  rw [inline39_instructionPC]

theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 2238).take PairedAllInlineCoreTrace.inline40Template.length = PairedAllInlineCoreTrace.inline40Template := by
  rfl

theorem inline40_instructionPC :
    Artifact.submissionArtifact.instructionPC 2238 = 2871 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline40Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline40Template 2238 inline40_slice
    (by
      change 2238 + PairedAllInlineCoreTrace.inline40Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline40Template) (by decide))
    (by decide)

theorem inline40Site_startPC : inline40Site.startPC = UInt256.ofNat 2871 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2238) = UInt256.ofNat 2871
  rw [inline40_instructionPC]

theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2277).take PairedAllInlineCoreTrace.inline41Template.length = PairedAllInlineCoreTrace.inline41Template := by
  rfl

theorem inline41_instructionPC :
    Artifact.submissionArtifact.instructionPC 2277 = 2917 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline41Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline41Template 2277 inline41_slice
    (by
      change 2277 + PairedAllInlineCoreTrace.inline41Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline41Template) (by decide))
    (by decide)

theorem inline41Site_startPC : inline41Site.startPC = UInt256.ofNat 2917 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2277) = UInt256.ofNat 2917
  rw [inline41_instructionPC]

theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2316).take PairedAllInlineCoreTrace.inline42Template.length = PairedAllInlineCoreTrace.inline42Template := by
  rfl

theorem inline42_instructionPC :
    Artifact.submissionArtifact.instructionPC 2316 = 2963 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline42Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline42Template 2316 inline42_slice
    (by
      change 2316 + PairedAllInlineCoreTrace.inline42Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline42Template) (by decide))
    (by decide)

theorem inline42Site_startPC : inline42Site.startPC = UInt256.ofNat 2963 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2316) = UInt256.ofNat 2963
  rw [inline42_instructionPC]

theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2355).take PairedAllInlineCoreTrace.inline43Template.length = PairedAllInlineCoreTrace.inline43Template := by
  rfl

theorem inline43_instructionPC :
    Artifact.submissionArtifact.instructionPC 2355 = 3008 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline43Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline43Template 2355 inline43_slice
    (by
      change 2355 + PairedAllInlineCoreTrace.inline43Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline43Template) (by decide))
    (by decide)

theorem inline43Site_startPC : inline43Site.startPC = UInt256.ofNat 3008 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2355) = UInt256.ofNat 3008
  rw [inline43_instructionPC]

theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2394).take PairedAllInlineCoreTrace.inline44Template.length = PairedAllInlineCoreTrace.inline44Template := by
  rfl

theorem inline44_instructionPC :
    Artifact.submissionArtifact.instructionPC 2394 = 3054 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline44Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline44Template 2394 inline44_slice
    (by
      change 2394 + PairedAllInlineCoreTrace.inline44Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline44Template) (by decide))
    (by decide)

theorem inline44Site_startPC : inline44Site.startPC = UInt256.ofNat 3054 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2394) = UInt256.ofNat 3054
  rw [inline44_instructionPC]

theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2433).take PairedAllInlineCoreTrace.inline45Template.length = PairedAllInlineCoreTrace.inline45Template := by
  rfl

theorem inline45_instructionPC :
    Artifact.submissionArtifact.instructionPC 2433 = 3100 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline45Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline45Template 2433 inline45_slice
    (by
      change 2433 + PairedAllInlineCoreTrace.inline45Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline45Template) (by decide))
    (by decide)

theorem inline45Site_startPC : inline45Site.startPC = UInt256.ofNat 3100 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2433) = UInt256.ofNat 3100
  rw [inline45_instructionPC]

theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2470).take PairedAllInlineCoreTrace.inline46Template.length = PairedAllInlineCoreTrace.inline46Template := by
  rfl

theorem inline46_instructionPC :
    Artifact.submissionArtifact.instructionPC 2470 = 3142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline46Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline46Template 2470 inline46_slice
    (by
      change 2470 + PairedAllInlineCoreTrace.inline46Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline46Template) (by decide))
    (by decide)

theorem inline46Site_startPC : inline46Site.startPC = UInt256.ofNat 3142 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2470) = UInt256.ofNat 3142
  rw [inline46_instructionPC]

theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2503).take PairedAllInlineCoreTrace.inline47Template.length = PairedAllInlineCoreTrace.inline47Template := by
  rfl

theorem inline47_instructionPC :
    Artifact.submissionArtifact.instructionPC 2503 = 3181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline47Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline47Template 2503 inline47_slice
    (by
      change 2503 + PairedAllInlineCoreTrace.inline47Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline47Template) (by decide))
    (by decide)

theorem inline47Site_startPC : inline47Site.startPC = UInt256.ofNat 3181 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2503) = UInt256.ofNat 3181
  rw [inline47_instructionPC]

theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2536).take PairedAllInlineCoreTrace.group48Template.length = PairedAllInlineCoreTrace.group48Template := by
  rfl

theorem group48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2536 = 3220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group48Template 2536 group48_slice
    (by
      change 2536 + PairedAllInlineCoreTrace.group48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group48Template) (by decide))
    (by decide)

theorem group48Site_startPC : group48Site.startPC = UInt256.ofNat 3220 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2536) = UInt256.ofNat 3220
  rw [group48_instructionPC]

theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2539).take PairedAllInlineCoreTrace.inline48Template.length = PairedAllInlineCoreTrace.inline48Template := by
  rfl

theorem inline48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2539 = 3243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline48Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline48Template 2539 inline48_slice
    (by
      change 2539 + PairedAllInlineCoreTrace.inline48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline48Template) (by decide))
    (by decide)

theorem inline48Site_startPC : inline48Site.startPC = UInt256.ofNat 3243 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2539) = UInt256.ofNat 3243
  rw [inline48_instructionPC]

theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2585).take PairedAllInlineCoreTrace.inline49Template.length = PairedAllInlineCoreTrace.inline49Template := by
  rfl

theorem inline49_instructionPC :
    Artifact.submissionArtifact.instructionPC 2585 = 3295 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline49Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline49Template 2585 inline49_slice
    (by
      change 2585 + PairedAllInlineCoreTrace.inline49Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline49Template) (by decide))
    (by decide)

theorem inline49Site_startPC : inline49Site.startPC = UInt256.ofNat 3295 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2585) = UInt256.ofNat 3295
  rw [inline49_instructionPC]

theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2631).take PairedAllInlineCoreTrace.inline50Template.length = PairedAllInlineCoreTrace.inline50Template := by
  rfl

theorem inline50_instructionPC :
    Artifact.submissionArtifact.instructionPC 2631 = 3348 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline50Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline50Template 2631 inline50_slice
    (by
      change 2631 + PairedAllInlineCoreTrace.inline50Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline50Template) (by decide))
    (by decide)

theorem inline50Site_startPC : inline50Site.startPC = UInt256.ofNat 3348 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2631) = UInt256.ofNat 3348
  rw [inline50_instructionPC]

theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2677).take PairedAllInlineCoreTrace.inline51Template.length = PairedAllInlineCoreTrace.inline51Template := by
  rfl

theorem inline51_instructionPC :
    Artifact.submissionArtifact.instructionPC 2677 = 3401 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline51Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline51Template 2677 inline51_slice
    (by
      change 2677 + PairedAllInlineCoreTrace.inline51Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline51Template) (by decide))
    (by decide)

theorem inline51Site_startPC : inline51Site.startPC = UInt256.ofNat 3401 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2677) = UInt256.ofNat 3401
  rw [inline51_instructionPC]

theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2723).take PairedAllInlineCoreTrace.inline52Template.length = PairedAllInlineCoreTrace.inline52Template := by
  rfl

theorem inline52_instructionPC :
    Artifact.submissionArtifact.instructionPC 2723 = 3453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline52Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline52Template 2723 inline52_slice
    (by
      change 2723 + PairedAllInlineCoreTrace.inline52Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline52Template) (by decide))
    (by decide)

theorem inline52Site_startPC : inline52Site.startPC = UInt256.ofNat 3453 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2723) = UInt256.ofNat 3453
  rw [inline52_instructionPC]

theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2763).take PairedAllInlineCoreTrace.inline53Template.length = PairedAllInlineCoreTrace.inline53Template := by
  rfl

theorem inline53_instructionPC :
    Artifact.submissionArtifact.instructionPC 2763 = 3498 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline53Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline53Template 2763 inline53_slice
    (by
      change 2763 + PairedAllInlineCoreTrace.inline53Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline53Template) (by decide))
    (by decide)

theorem inline53Site_startPC : inline53Site.startPC = UInt256.ofNat 3498 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2763) = UInt256.ofNat 3498
  rw [inline53_instructionPC]

theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2807).take PairedAllInlineCoreTrace.inline54Template.length = PairedAllInlineCoreTrace.inline54Template := by
  rfl

theorem inline54_instructionPC :
    Artifact.submissionArtifact.instructionPC 2807 = 3548 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline54Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline54Template 2807 inline54_slice
    (by
      change 2807 + PairedAllInlineCoreTrace.inline54Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline54Template) (by decide))
    (by decide)

theorem inline54Site_startPC : inline54Site.startPC = UInt256.ofNat 3548 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2807) = UInt256.ofNat 3548
  rw [inline54_instructionPC]

theorem inline55_slice :
    (Artifact.submissionArtifact.instructions.drop 2853).take PairedAllInlineCoreTrace.inline55Template.length = PairedAllInlineCoreTrace.inline55Template := by
  rfl

theorem inline55_instructionPC :
    Artifact.submissionArtifact.instructionPC 2853 = 3601 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline55Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline55Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline55Template 2853 inline55_slice
    (by
      change 2853 + PairedAllInlineCoreTrace.inline55Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline55Template) (by decide))
    (by decide)

theorem inline55Site_startPC : inline55Site.startPC = UInt256.ofNat 3601 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2853) = UInt256.ofNat 3601
  rw [inline55_instructionPC]

theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 2899).take PairedAllInlineCoreTrace.inline56Template.length = PairedAllInlineCoreTrace.inline56Template := by
  rfl

theorem inline56_instructionPC :
    Artifact.submissionArtifact.instructionPC 2899 = 3653 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline56Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline56Template 2899 inline56_slice
    (by
      change 2899 + PairedAllInlineCoreTrace.inline56Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline56Template) (by decide))
    (by decide)

theorem inline56Site_startPC : inline56Site.startPC = UInt256.ofNat 3653 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2899) = UInt256.ofNat 3653
  rw [inline56_instructionPC]

theorem inline57_slice :
    (Artifact.submissionArtifact.instructions.drop 2945).take PairedAllInlineCoreTrace.inline57Template.length = PairedAllInlineCoreTrace.inline57Template := by
  rfl

theorem inline57_instructionPC :
    Artifact.submissionArtifact.instructionPC 2945 = 3706 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline57Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline57Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline57Template 2945 inline57_slice
    (by
      change 2945 + PairedAllInlineCoreTrace.inline57Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline57Template) (by decide))
    (by decide)

theorem inline57Site_startPC : inline57Site.startPC = UInt256.ofNat 3706 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2945) = UInt256.ofNat 3706
  rw [inline57_instructionPC]

theorem inline58_slice :
    (Artifact.submissionArtifact.instructions.drop 2991).take PairedAllInlineCoreTrace.inline58Template.length = PairedAllInlineCoreTrace.inline58Template := by
  rfl

theorem inline58_instructionPC :
    Artifact.submissionArtifact.instructionPC 2991 = 3759 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline58Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline58Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline58Template 2991 inline58_slice
    (by
      change 2991 + PairedAllInlineCoreTrace.inline58Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline58Template) (by decide))
    (by decide)

theorem inline58Site_startPC : inline58Site.startPC = UInt256.ofNat 3759 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2991) = UInt256.ofNat 3759
  rw [inline58_instructionPC]

theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 3037).take PairedAllInlineCoreTrace.inline59Template.length = PairedAllInlineCoreTrace.inline59Template := by
  rfl

theorem inline59_instructionPC :
    Artifact.submissionArtifact.instructionPC 3037 = 3812 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline59Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline59Template 3037 inline59_slice
    (by
      change 3037 + PairedAllInlineCoreTrace.inline59Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline59Template) (by decide))
    (by decide)

theorem inline59Site_startPC : inline59Site.startPC = UInt256.ofNat 3812 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3037) = UInt256.ofNat 3812
  rw [inline59_instructionPC]

theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 3083).take PairedAllInlineCoreTrace.inline60Template.length = PairedAllInlineCoreTrace.inline60Template := by
  rfl

theorem inline60_instructionPC :
    Artifact.submissionArtifact.instructionPC 3083 = 3865 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline60Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline60Template 3083 inline60_slice
    (by
      change 3083 + PairedAllInlineCoreTrace.inline60Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline60Template) (by decide))
    (by decide)

theorem inline60Site_startPC : inline60Site.startPC = UInt256.ofNat 3865 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3083) = UInt256.ofNat 3865
  rw [inline60_instructionPC]

theorem inline61_slice :
    (Artifact.submissionArtifact.instructions.drop 3129).take PairedAllInlineCoreTrace.inline61Template.length = PairedAllInlineCoreTrace.inline61Template := by
  rfl

theorem inline61_instructionPC :
    Artifact.submissionArtifact.instructionPC 3129 = 3918 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline61Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline61Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline61Template 3129 inline61_slice
    (by
      change 3129 + PairedAllInlineCoreTrace.inline61Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline61Template) (by decide))
    (by decide)

theorem inline61Site_startPC : inline61Site.startPC = UInt256.ofNat 3918 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3129) = UInt256.ofNat 3918
  rw [inline61_instructionPC]

theorem inline62_slice :
    (Artifact.submissionArtifact.instructions.drop 3173).take PairedAllInlineCoreTrace.inline62Template.length = PairedAllInlineCoreTrace.inline62Template := by
  rfl

theorem inline62_instructionPC :
    Artifact.submissionArtifact.instructionPC 3173 = 3968 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline62Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline62Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline62Template 3173 inline62_slice
    (by
      change 3173 + PairedAllInlineCoreTrace.inline62Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline62Template) (by decide))
    (by decide)

theorem inline62Site_startPC : inline62Site.startPC = UInt256.ofNat 3968 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3173) = UInt256.ofNat 3968
  rw [inline62_instructionPC]

theorem inline63_slice :
    (Artifact.submissionArtifact.instructions.drop 3219).take PairedAllInlineCoreTrace.inline63Template.length = PairedAllInlineCoreTrace.inline63Template := by
  rfl

theorem inline63_instructionPC :
    Artifact.submissionArtifact.instructionPC 3219 = 4022 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline63Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline63Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline63Template 3219 inline63_slice
    (by
      change 3219 + PairedAllInlineCoreTrace.inline63Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline63Template) (by decide))
    (by decide)

theorem inline63Site_startPC : inline63Site.startPC = UInt256.ofNat 4022 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3219) = UInt256.ofNat 4022
  rw [inline63_instructionPC]

theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3265).take PairedAllInlineCoreTrace.group64Template.length = PairedAllInlineCoreTrace.group64Template := by
  rfl

theorem group64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3265 = 4075 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.group64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.group64Template 3265 group64_slice
    (by
      change 3265 + PairedAllInlineCoreTrace.group64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.group64Template) (by decide))
    (by decide)

theorem group64Site_startPC : group64Site.startPC = UInt256.ofNat 4075 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3265) = UInt256.ofNat 4075
  rw [group64_instructionPC]

theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3268).take PairedAllInlineCoreTrace.inline64Template.length = PairedAllInlineCoreTrace.inline64Template := by
  rfl

theorem inline64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3268 = 4082 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline64Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline64Template 3268 inline64_slice
    (by
      change 3268 + PairedAllInlineCoreTrace.inline64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline64Template) (by decide))
    (by decide)

theorem inline64Site_startPC : inline64Site.startPC = UInt256.ofNat 4082 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3268) = UInt256.ofNat 4082
  rw [inline64_instructionPC]

theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3310).take PairedAllInlineCoreTrace.inline65Template.length = PairedAllInlineCoreTrace.inline65Template := by
  rfl

theorem inline65_instructionPC :
    Artifact.submissionArtifact.instructionPC 3310 = 4130 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline65Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline65Template 3310 inline65_slice
    (by
      change 3310 + PairedAllInlineCoreTrace.inline65Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline65Template) (by decide))
    (by decide)

theorem inline65Site_startPC : inline65Site.startPC = UInt256.ofNat 4130 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3310) = UInt256.ofNat 4130
  rw [inline65_instructionPC]

theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3354).take PairedAllInlineCoreTrace.inline66Template.length = PairedAllInlineCoreTrace.inline66Template := by
  rfl

theorem inline66_instructionPC :
    Artifact.submissionArtifact.instructionPC 3354 = 4181 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline66Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline66Template 3354 inline66_slice
    (by
      change 3354 + PairedAllInlineCoreTrace.inline66Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline66Template) (by decide))
    (by decide)

theorem inline66Site_startPC : inline66Site.startPC = UInt256.ofNat 4181 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3354) = UInt256.ofNat 4181
  rw [inline66_instructionPC]

theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3398).take PairedAllInlineCoreTrace.inline67Template.length = PairedAllInlineCoreTrace.inline67Template := by
  rfl

theorem inline67_instructionPC :
    Artifact.submissionArtifact.instructionPC 3398 = 4232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline67Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline67Template 3398 inline67_slice
    (by
      change 3398 + PairedAllInlineCoreTrace.inline67Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline67Template) (by decide))
    (by decide)

theorem inline67Site_startPC : inline67Site.startPC = UInt256.ofNat 4232 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3398) = UInt256.ofNat 4232
  rw [inline67_instructionPC]

theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3442).take PairedAllInlineCoreTrace.inline68Template.length = PairedAllInlineCoreTrace.inline68Template := by
  rfl

theorem inline68_instructionPC :
    Artifact.submissionArtifact.instructionPC 3442 = 4283 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline68Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline68Template 3442 inline68_slice
    (by
      change 3442 + PairedAllInlineCoreTrace.inline68Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline68Template) (by decide))
    (by decide)

theorem inline68Site_startPC : inline68Site.startPC = UInt256.ofNat 4283 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3442) = UInt256.ofNat 4283
  rw [inline68_instructionPC]

theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3486).take PairedAllInlineCoreTrace.inline69Template.length = PairedAllInlineCoreTrace.inline69Template := by
  rfl

theorem inline69_instructionPC :
    Artifact.submissionArtifact.instructionPC 3486 = 4333 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline69Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline69Template 3486 inline69_slice
    (by
      change 3486 + PairedAllInlineCoreTrace.inline69Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline69Template) (by decide))
    (by decide)

theorem inline69Site_startPC : inline69Site.startPC = UInt256.ofNat 4333 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3486) = UInt256.ofNat 4333
  rw [inline69_instructionPC]

theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3530).take PairedAllInlineCoreTrace.inline70Template.length = PairedAllInlineCoreTrace.inline70Template := by
  rfl

theorem inline70_instructionPC :
    Artifact.submissionArtifact.instructionPC 3530 = 4384 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline70Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline70Template 3530 inline70_slice
    (by
      change 3530 + PairedAllInlineCoreTrace.inline70Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline70Template) (by decide))
    (by decide)

theorem inline70Site_startPC : inline70Site.startPC = UInt256.ofNat 4384 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3530) = UInt256.ofNat 4384
  rw [inline70_instructionPC]

theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3572).take PairedAllInlineCoreTrace.inline71Template.length = PairedAllInlineCoreTrace.inline71Template := by
  rfl

theorem inline71_instructionPC :
    Artifact.submissionArtifact.instructionPC 3572 = 4432 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline71Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline71Template 3572 inline71_slice
    (by
      change 3572 + PairedAllInlineCoreTrace.inline71Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline71Template) (by decide))
    (by decide)

theorem inline71Site_startPC : inline71Site.startPC = UInt256.ofNat 4432 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3572) = UInt256.ofNat 4432
  rw [inline71_instructionPC]

theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3616).take PairedAllInlineCoreTrace.inline72Template.length = PairedAllInlineCoreTrace.inline72Template := by
  rfl

theorem inline72_instructionPC :
    Artifact.submissionArtifact.instructionPC 3616 = 4483 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline72Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline72Template 3616 inline72_slice
    (by
      change 3616 + PairedAllInlineCoreTrace.inline72Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline72Template) (by decide))
    (by decide)

theorem inline72Site_startPC : inline72Site.startPC = UInt256.ofNat 4483 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3616) = UInt256.ofNat 4483
  rw [inline72_instructionPC]

theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3660).take PairedAllInlineCoreTrace.inline73Template.length = PairedAllInlineCoreTrace.inline73Template := by
  rfl

theorem inline73_instructionPC :
    Artifact.submissionArtifact.instructionPC 3660 = 4534 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline73Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline73Template 3660 inline73_slice
    (by
      change 3660 + PairedAllInlineCoreTrace.inline73Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline73Template) (by decide))
    (by decide)

theorem inline73Site_startPC : inline73Site.startPC = UInt256.ofNat 4534 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3660) = UInt256.ofNat 4534
  rw [inline73_instructionPC]

theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3702).take PairedAllInlineCoreTrace.inline74Template.length = PairedAllInlineCoreTrace.inline74Template := by
  rfl

theorem inline74_instructionPC :
    Artifact.submissionArtifact.instructionPC 3702 = 4581 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline74Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline74Template 3702 inline74_slice
    (by
      change 3702 + PairedAllInlineCoreTrace.inline74Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline74Template) (by decide))
    (by decide)

theorem inline74Site_startPC : inline74Site.startPC = UInt256.ofNat 4581 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3702) = UInt256.ofNat 4581
  rw [inline74_instructionPC]

theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3746).take PairedAllInlineCoreTrace.inline75Template.length = PairedAllInlineCoreTrace.inline75Template := by
  rfl

theorem inline75_instructionPC :
    Artifact.submissionArtifact.instructionPC 3746 = 4632 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline75Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline75Template 3746 inline75_slice
    (by
      change 3746 + PairedAllInlineCoreTrace.inline75Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline75Template) (by decide))
    (by decide)

theorem inline75Site_startPC : inline75Site.startPC = UInt256.ofNat 4632 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3746) = UInt256.ofNat 4632
  rw [inline75_instructionPC]

theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3790).take PairedAllInlineCoreTrace.inline76Template.length = PairedAllInlineCoreTrace.inline76Template := by
  rfl

theorem inline76_instructionPC :
    Artifact.submissionArtifact.instructionPC 3790 = 4684 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline76Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline76Template 3790 inline76_slice
    (by
      change 3790 + PairedAllInlineCoreTrace.inline76Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline76Template) (by decide))
    (by decide)

theorem inline76Site_startPC : inline76Site.startPC = UInt256.ofNat 4684 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3790) = UInt256.ofNat 4684
  rw [inline76_instructionPC]

theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 3834).take PairedAllInlineCoreTrace.inline77Template.length = PairedAllInlineCoreTrace.inline77Template := by
  rfl

theorem inline77_instructionPC :
    Artifact.submissionArtifact.instructionPC 3834 = 4734 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline77Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline77Template 3834 inline77_slice
    (by
      change 3834 + PairedAllInlineCoreTrace.inline77Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline77Template) (by decide))
    (by decide)

theorem inline77Site_startPC : inline77Site.startPC = UInt256.ofNat 4734 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3834) = UInt256.ofNat 4734
  rw [inline77_instructionPC]

theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3878).take PairedAllInlineCoreTrace.inline78Template.length = PairedAllInlineCoreTrace.inline78Template := by
  rfl

theorem inline78_instructionPC :
    Artifact.submissionArtifact.instructionPC 3878 = 4785 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineCoreTrace.inline78Template :=
  StackSiteBuilder.ofSlice PairedAllInlineCoreTrace.inline78Template 3878 inline78_slice
    (by
      change 3878 + PairedAllInlineCoreTrace.inline78Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineCoreTrace.inline78Template) (by decide))
    (by decide)

theorem inline78Site_startPC : inline78Site.startPC = UInt256.ofNat 4785 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3878) = UInt256.ofNat 4785
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
    GasSteps {s with pc := UInt256.ofNat 822, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] f rho}
      {s with
        pc := UInt256.ofNat 4836
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

import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCoreSites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate PairedHelperBooleanTrace

/-- Actual instruction windows for the frozen 5349-byte generic paired compressor. -/

theorem group0_slice :
    (Artifact.submissionArtifact.instructions.drop 464).take group0Template.length = group0Template := by
  rfl

theorem group0_instructionPC :
    Artifact.submissionArtifact.instructionPC 464 = 797 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka group0Template :=
  StackSiteBuilder.ofSlice group0Template 462 group0_slice
    (by
      change 462 + group0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := group0Template) (by decide))
    (by decide)

theorem group0Site_startPC : group0Site.startPC = UInt256.ofNat 998 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 464) = UInt256.ofNat 797
  rw [group0_instructionPC]


theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 465).take inline0Template.length = inline0Template := by
  rfl

theorem inline0_instructionPC :
    Artifact.submissionArtifact.instructionPC 465 = 802 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline0Template :=
  StackSiteBuilder.ofSlice inline0Template 463 inline0_slice
    (by
      change 463 + inline0Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline0Template) (by decide))
    (by decide)

theorem inline0Site_startPC : inline0Site.startPC = UInt256.ofNat 1019 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 465) = UInt256.ofNat 802
  rw [inline0_instructionPC]


theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 513).take inline1Template.length = inline1Template := by
  rfl

theorem inline1_instructionPC :
    Artifact.submissionArtifact.instructionPC 513 = 857 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline1Template :=
  StackSiteBuilder.ofSlice inline1Template 511 inline1_slice
    (by
      change 511 + inline1Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline1Template) (by decide))
    (by decide)

theorem inline1Site_startPC : inline1Site.startPC = UInt256.ofNat 1073 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 513) = UInt256.ofNat 857
  rw [inline1_instructionPC]


theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 561).take inline2Template.length = inline2Template := by
  rfl

theorem inline2_instructionPC :
    Artifact.submissionArtifact.instructionPC 561 = 911 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline2Template :=
  StackSiteBuilder.ofSlice inline2Template 559 inline2_slice
    (by
      change 559 + inline2Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline2Template) (by decide))
    (by decide)

theorem inline2Site_startPC : inline2Site.startPC = UInt256.ofNat 1127 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 561) = UInt256.ofNat 911
  rw [inline2_instructionPC]


theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 609).take inline3Template.length = inline3Template := by
  rfl

theorem inline3_instructionPC :
    Artifact.submissionArtifact.instructionPC 609 = 966 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline3Template :=
  StackSiteBuilder.ofSlice inline3Template 607 inline3_slice
    (by
      change 607 + inline3Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline3Template) (by decide))
    (by decide)

theorem inline3Site_startPC : inline3Site.startPC = UInt256.ofNat 1148 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 609) = UInt256.ofNat 966
  rw [inline3_instructionPC]


theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 657).take inline4Template.length = inline4Template := by
  rfl

theorem inline4_instructionPC :
    Artifact.submissionArtifact.instructionPC 657 = 1020 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline4Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline4Template :=
  StackSiteBuilder.ofSlice inline4Template 655 inline4_slice
    (by
      change 655 + inline4Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline4Template) (by decide))
    (by decide)

theorem inline4Site_startPC : inline4Site.startPC = UInt256.ofNat 1236 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 657) = UInt256.ofNat 1020
  rw [inline4_instructionPC]


theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 705).take inline5Template.length = inline5Template := by
  rfl

theorem inline5_instructionPC :
    Artifact.submissionArtifact.instructionPC 705 = 1075 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline5Template :=
  StackSiteBuilder.ofSlice inline5Template 703 inline5_slice
    (by
      change 703 + inline5Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline5Template) (by decide))
    (by decide)

theorem inline5Site_startPC : inline5Site.startPC = UInt256.ofNat 1291 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 705) = UInt256.ofNat 1075
  rw [inline5_instructionPC]


theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 753).take inline6Template.length = inline6Template := by
  rfl

theorem inline6_instructionPC :
    Artifact.submissionArtifact.instructionPC 753 = 1130 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline6Template :=
  StackSiteBuilder.ofSlice inline6Template 751 inline6_slice
    (by
      change 751 + inline6Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline6Template) (by decide))
    (by decide)

theorem inline6Site_startPC : inline6Site.startPC = UInt256.ofNat 1346 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 753) = UInt256.ofNat 1130
  rw [inline6_instructionPC]


theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 801).take inline7Template.length = inline7Template := by
  rfl

theorem inline7_instructionPC :
    Artifact.submissionArtifact.instructionPC 801 = 1185 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline7Template :=
  StackSiteBuilder.ofSlice inline7Template 799 inline7_slice
    (by
      change 799 + inline7Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline7Template) (by decide))
    (by decide)

theorem inline7Site_startPC : inline7Site.startPC = UInt256.ofNat 1401 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 801) = UInt256.ofNat 1185
  rw [inline7_instructionPC]


theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 849).take inline8Template.length = inline8Template := by
  rfl

theorem inline8_instructionPC :
    Artifact.submissionArtifact.instructionPC 849 = 1240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline8Template :=
  StackSiteBuilder.ofSlice inline8Template 847 inline8_slice
    (by
      change 847 + inline8Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline8Template) (by decide))
    (by decide)

theorem inline8Site_startPC : inline8Site.startPC = UInt256.ofNat 1452 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 849) = UInt256.ofNat 1240
  rw [inline8_instructionPC]


theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 897).take inline9Template.length = inline9Template := by
  rfl

theorem inline9_instructionPC :
    Artifact.submissionArtifact.instructionPC 897 = 1295 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline9Template :=
  StackSiteBuilder.ofSlice inline9Template 895 inline9_slice
    (by
      change 895 + inline9Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline9Template) (by decide))
    (by decide)

theorem inline9Site_startPC : inline9Site.startPC = UInt256.ofNat 1511 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 897) = UInt256.ofNat 1295
  rw [inline9_instructionPC]


theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 945).take inline10Template.length = inline10Template := by
  rfl

theorem inline10_instructionPC :
    Artifact.submissionArtifact.instructionPC 945 = 1352 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline10Template :=
  StackSiteBuilder.ofSlice inline10Template 943 inline10_slice
    (by
      change 943 + inline10Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline10Template) (by decide))
    (by decide)

theorem inline10Site_startPC : inline10Site.startPC = UInt256.ofNat 1562 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 945) = UInt256.ofNat 1352
  rw [inline10_instructionPC]


theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 993).take inline11Template.length = inline11Template := by
  rfl

theorem inline11_instructionPC :
    Artifact.submissionArtifact.instructionPC 993 = 1409 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline11Template :=
  StackSiteBuilder.ofSlice inline11Template 991 inline11_slice
    (by
      change 991 + inline11Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline11Template) (by decide))
    (by decide)

theorem inline11Site_startPC : inline11Site.startPC = UInt256.ofNat 1617 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 993) = UInt256.ofNat 1409
  rw [inline11_instructionPC]


theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1041).take inline12Template.length = inline12Template := by
  rfl

theorem inline12_instructionPC :
    Artifact.submissionArtifact.instructionPC 1041 = 1463 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline12Template :=
  StackSiteBuilder.ofSlice inline12Template 1039 inline12_slice
    (by
      change 1039 + inline12Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline12Template) (by decide))
    (by decide)

theorem inline12Site_startPC : inline12Site.startPC = UInt256.ofNat 1642 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1041) = UInt256.ofNat 1463
  rw [inline12_instructionPC]


theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1089).take inline13Template.length = inline13Template := by
  rfl

theorem inline13_instructionPC :
    Artifact.submissionArtifact.instructionPC 1089 = 1518 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline13Template :=
  StackSiteBuilder.ofSlice inline13Template 1087 inline13_slice
    (by
      change 1087 + inline13Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline13Template) (by decide))
    (by decide)

theorem inline13Site_startPC : inline13Site.startPC = UInt256.ofNat 1696 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1089) = UInt256.ofNat 1518
  rw [inline13_instructionPC]


theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1137).take inline14Template.length = inline14Template := by
  rfl

theorem inline14_instructionPC :
    Artifact.submissionArtifact.instructionPC 1137 = 1573 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline14Template :=
  StackSiteBuilder.ofSlice inline14Template 1135 inline14_slice
    (by
      change 1135 + inline14Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline14Template) (by decide))
    (by decide)

theorem inline14Site_startPC : inline14Site.startPC = UInt256.ofNat 1785 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1137) = UInt256.ofNat 1573
  rw [inline14_instructionPC]


theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1185).take inline15Template.length = inline15Template := by
  rfl

theorem inline15_instructionPC :
    Artifact.submissionArtifact.instructionPC 1185 = 1628 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline15Template :=
  StackSiteBuilder.ofSlice inline15Template 1183 inline15_slice
    (by
      change 1183 + inline15Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline15Template) (by decide))
    (by decide)

theorem inline15Site_startPC : inline15Site.startPC = UInt256.ofNat 1840 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1185) = UInt256.ofNat 1628
  rw [inline15_instructionPC]


theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1233).take group16Template.length = group16Template := by
  rfl

theorem group16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1233 = 1692 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka group16Template :=
  StackSiteBuilder.ofSlice group16Template 1231 group16_slice
    (by
      change 1231 + group16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := group16Template) (by decide))
    (by decide)

theorem group16Site_startPC : group16Site.startPC = UInt256.ofNat 1895 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1233) = UInt256.ofNat 1692
  rw [group16_instructionPC]


theorem call16_slice :
    (Artifact.submissionArtifact.instructions.drop 1236).take call16Template.length = call16Template := by
  rfl

theorem call16_instructionPC :
    Artifact.submissionArtifact.instructionPC 1236 = 1695 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call16Site : GenericRoundSite Artifact.submissionArtifact .Osaka call16Template :=
  StackSiteBuilder.ofSlice call16Template 1234 call16_slice
    (by
      change 1234 + call16Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := call16Template) (by decide))
    (by decide)

theorem call16Site_startPC : call16Site.startPC = UInt256.ofNat 1918 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1236) = UInt256.ofNat 1695
  rw [call16_instructionPC]


theorem return18_slice :
    (Artifact.submissionArtifact.instructions.drop 1260).take return18Template.length = return18Template := by
  rfl

theorem return18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1260 = 1722 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return18Site : GenericRoundSite Artifact.submissionArtifact .Osaka return18Template :=
  StackSiteBuilder.ofSlice return18Template 1258 return18_slice
    (by
      change 1258 + return18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := return18Template) (by decide))
    (by decide)

theorem return18Site_startPC : return18Site.startPC = UInt256.ofNat 1958 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1260) = UInt256.ofNat 1722
  rw [return18_instructionPC]


theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1261).take inline18Template.length = inline18Template := by
  rfl

theorem inline18_instructionPC :
    Artifact.submissionArtifact.instructionPC 1261 = 1723 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline18Template :=
  StackSiteBuilder.ofSlice inline18Template 1259 inline18_slice
    (by
      change 1259 + inline18Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline18Template) (by decide))
    (by decide)

theorem inline18Site_startPC : inline18Site.startPC = UInt256.ofNat 1959 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1261) = UInt256.ofNat 1723
  rw [inline18_instructionPC]


theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1314).take inline19Template.length = inline19Template := by
  rfl

theorem inline19_instructionPC :
    Artifact.submissionArtifact.instructionPC 1314 = 1783 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline19Template :=
  StackSiteBuilder.ofSlice inline19Template 1312 inline19_slice
    (by
      change 1312 + inline19Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline19Template) (by decide))
    (by decide)

theorem inline19Site_startPC : inline19Site.startPC = UInt256.ofNat 2019 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1314) = UInt256.ofNat 1783
  rw [inline19_instructionPC]


theorem call20_slice :
    (Artifact.submissionArtifact.instructions.drop 1368).take call20Template.length = call20Template := by
  rfl

theorem call20_instructionPC :
    Artifact.submissionArtifact.instructionPC 1368 = 1844 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call20Site : GenericRoundSite Artifact.submissionArtifact .Osaka call20Template :=
  StackSiteBuilder.ofSlice call20Template 1366 call20_slice
    (by
      change 1366 + call20Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := call20Template) (by decide))
    (by decide)

theorem call20Site_startPC : call20Site.startPC = UInt256.ofNat 2079 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1368) = UInt256.ofNat 1844
  rw [call20_instructionPC]


theorem call22_slice :
    (Artifact.submissionArtifact.instructions.drop 1389).take call22Template.length = call22Template := by
  rfl

theorem call22_instructionPC :
    Artifact.submissionArtifact.instructionPC 1389 = 1869 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call22Site : GenericRoundSite Artifact.submissionArtifact .Osaka call22Template :=
  StackSiteBuilder.ofSlice call22Template 1387 call22_slice
    (by
      change 1387 + call22Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := call22Template) (by decide))
    (by decide)

theorem call22Site_startPC : call22Site.startPC = UInt256.ofNat 2115 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1389) = UInt256.ofNat 1869
  rw [call22_instructionPC]


theorem return24_slice :
    (Artifact.submissionArtifact.instructions.drop 1412).take return24Template.length = return24Template := by
  rfl

theorem return24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1412 = 1894 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return24Site : GenericRoundSite Artifact.submissionArtifact .Osaka return24Template :=
  StackSiteBuilder.ofSlice return24Template 1410 return24_slice
    (by
      change 1410 + return24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := return24Template) (by decide))
    (by decide)

theorem return24Site_startPC : return24Site.startPC = UInt256.ofNat 2154 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1412) = UInt256.ofNat 1894
  rw [return24_instructionPC]


theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1413).take inline24Template.length = inline24Template := by
  rfl

theorem inline24_instructionPC :
    Artifact.submissionArtifact.instructionPC 1413 = 1895 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline24Template :=
  StackSiteBuilder.ofSlice inline24Template 1411 inline24_slice
    (by
      change 1411 + inline24Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline24Template) (by decide))
    (by decide)

theorem inline24Site_startPC : inline24Site.startPC = UInt256.ofNat 2155 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1413) = UInt256.ofNat 1895
  rw [inline24_instructionPC]


theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1457).take inline25Template.length = inline25Template := by
  rfl

theorem inline25_instructionPC :
    Artifact.submissionArtifact.instructionPC 1457 = 1945 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline25Template :=
  StackSiteBuilder.ofSlice inline25Template 1455 inline25_slice
    (by
      change 1455 + inline25Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline25Template) (by decide))
    (by decide)

theorem inline25Site_startPC : inline25Site.startPC = UInt256.ofNat 2205 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1457) = UInt256.ofNat 1945
  rw [inline25_instructionPC]


theorem call26_slice :
    (Artifact.submissionArtifact.instructions.drop 1511).take call26Template.length = call26Template := by
  rfl

theorem call26_instructionPC :
    Artifact.submissionArtifact.instructionPC 1511 = 2006 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call26Site : GenericRoundSite Artifact.submissionArtifact .Osaka call26Template :=
  StackSiteBuilder.ofSlice call26Template 1509 call26_slice
    (by
      change 1509 + call26Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := call26Template) (by decide))
    (by decide)

theorem call26Site_startPC : call26Site.startPC = UInt256.ofNat 2265 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1511) = UInt256.ofNat 2006
  rw [call26_instructionPC]


theorem call28_slice :
    (Artifact.submissionArtifact.instructions.drop 1532).take call28Template.length = call28Template := by
  rfl

theorem call28_instructionPC :
    Artifact.submissionArtifact.instructionPC 1532 = 2031 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def call28Site : GenericRoundSite Artifact.submissionArtifact .Osaka call28Template :=
  StackSiteBuilder.ofSlice call28Template 1530 call28_slice
    (by
      change 1530 + call28Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := call28Template) (by decide))
    (by decide)

theorem call28Site_startPC : call28Site.startPC = UInt256.ofNat 2298 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1532) = UInt256.ofNat 2031
  rw [call28_instructionPC]


theorem return30_slice :
    (Artifact.submissionArtifact.instructions.drop 1555).take return30Template.length = return30Template := by
  rfl

theorem return30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1555 = 2057 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def return30Site : GenericRoundSite Artifact.submissionArtifact .Osaka return30Template :=
  StackSiteBuilder.ofSlice return30Template 1553 return30_slice
    (by
      change 1553 + return30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := return30Template) (by decide))
    (by decide)

theorem return30Site_startPC : return30Site.startPC = UInt256.ofNat 2337 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1555) = UInt256.ofNat 2057
  rw [return30_instructionPC]


theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1556).take inline30Template.length = inline30Template := by
  rfl

theorem inline30_instructionPC :
    Artifact.submissionArtifact.instructionPC 1556 = 2058 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline30Template :=
  StackSiteBuilder.ofSlice inline30Template 1554 inline30_slice
    (by
      change 1554 + inline30Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline30Template) (by decide))
    (by decide)

theorem inline30Site_startPC : inline30Site.startPC = UInt256.ofNat 2338 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1556) = UInt256.ofNat 2058
  rw [inline30_instructionPC]


theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1600).take inline31Template.length = inline31Template := by
  rfl

theorem inline31_instructionPC :
    Artifact.submissionArtifact.instructionPC 1600 = 2109 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline31Template :=
  StackSiteBuilder.ofSlice inline31Template 1598 inline31_slice
    (by
      change 1598 + inline31Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline31Template) (by decide))
    (by decide)

theorem inline31Site_startPC : inline31Site.startPC = UInt256.ofNat 2391 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1600) = UInt256.ofNat 2109
  rw [inline31_instructionPC]


theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1654).take group32Template.length = group32Template := by
  rfl

theorem group32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1654 = 2169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka group32Template :=
  StackSiteBuilder.ofSlice group32Template 1652 group32_slice
    (by
      change 1652 + group32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := group32Template) (by decide))
    (by decide)

theorem group32Site_startPC : group32Site.startPC = UInt256.ofNat 2448 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1654) = UInt256.ofNat 2169
  rw [group32_instructionPC]


theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1657).take inline32Template.length = inline32Template := by
  rfl

theorem inline32_instructionPC :
    Artifact.submissionArtifact.instructionPC 1657 = 2172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline32Template :=
  StackSiteBuilder.ofSlice inline32Template 1655 inline32_slice
    (by
      change 1655 + inline32Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline32Template) (by decide))
    (by decide)

theorem inline32Site_startPC : inline32Site.startPC = UInt256.ofNat 2475 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1657) = UInt256.ofNat 2172
  rw [inline32_instructionPC]


theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 1700).take inline33Template.length = inline33Template := by
  rfl

theorem inline33_instructionPC :
    Artifact.submissionArtifact.instructionPC 1700 = 2221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline33Template :=
  StackSiteBuilder.ofSlice inline33Template 1698 inline33_slice
    (by
      change 1698 + inline33Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline33Template) (by decide))
    (by decide)

theorem inline33Site_startPC : inline33Site.startPC = UInt256.ofNat 2525 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1700) = UInt256.ofNat 2221
  rw [inline33_instructionPC]


theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 1743).take inline34Template.length = inline34Template := by
  rfl

theorem inline34_instructionPC :
    Artifact.submissionArtifact.instructionPC 1743 = 2271 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline34Template :=
  StackSiteBuilder.ofSlice inline34Template 1741 inline34_slice
    (by
      change 1741 + inline34Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline34Template) (by decide))
    (by decide)

theorem inline34Site_startPC : inline34Site.startPC = UInt256.ofNat 2537 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1743) = UInt256.ofNat 2271
  rw [inline34_instructionPC]


theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 1786).take inline35Template.length = inline35Template := by
  rfl

theorem inline35_instructionPC :
    Artifact.submissionArtifact.instructionPC 1786 = 2321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline35Template :=
  StackSiteBuilder.ofSlice inline35Template 1784 inline35_slice
    (by
      change 1784 + inline35Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline35Template) (by decide))
    (by decide)

theorem inline35Site_startPC : inline35Site.startPC = UInt256.ofNat 2590 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1786) = UInt256.ofNat 2321
  rw [inline35_instructionPC]


theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 1829).take inline36Template.length = inline36Template := by
  rfl

theorem inline36_instructionPC :
    Artifact.submissionArtifact.instructionPC 1829 = 2370 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline36Template :=
  StackSiteBuilder.ofSlice inline36Template 1827 inline36_slice
    (by
      change 1827 + inline36Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline36Template) (by decide))
    (by decide)

theorem inline36Site_startPC : inline36Site.startPC = UInt256.ofNat 2674 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1829) = UInt256.ofNat 2370
  rw [inline36_instructionPC]


theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 1872).take inline37Template.length = inline37Template := by
  rfl

theorem inline37_instructionPC :
    Artifact.submissionArtifact.instructionPC 1872 = 2420 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline37Template :=
  StackSiteBuilder.ofSlice inline37Template 1870 inline37_slice
    (by
      change 1870 + inline37Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline37Template) (by decide))
    (by decide)

theorem inline37Site_startPC : inline37Site.startPC = UInt256.ofNat 2690 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1872) = UInt256.ofNat 2420
  rw [inline37_instructionPC]


theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 1915).take inline38Template.length = inline38Template := by
  rfl

theorem inline38_instructionPC :
    Artifact.submissionArtifact.instructionPC 1915 = 2468 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline38Template :=
  StackSiteBuilder.ofSlice inline38Template 1913 inline38_slice
    (by
      change 1913 + inline38Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline38Template) (by decide))
    (by decide)

theorem inline38Site_startPC : inline38Site.startPC = UInt256.ofNat 2770 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1915) = UInt256.ofNat 2468
  rw [inline38_instructionPC]


theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 1958).take inline39Template.length = inline39Template := by
  rfl

theorem inline39_instructionPC :
    Artifact.submissionArtifact.instructionPC 1958 = 2518 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline39Template :=
  StackSiteBuilder.ofSlice inline39Template 1956 inline39_slice
    (by
      change 1956 + inline39Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline39Template) (by decide))
    (by decide)

theorem inline39Site_startPC : inline39Site.startPC = UInt256.ofNat 2824 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1958) = UInt256.ofNat 2518
  rw [inline39_instructionPC]


theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 2001).take inline40Template.length = inline40Template := by
  rfl

theorem inline40_instructionPC :
    Artifact.submissionArtifact.instructionPC 2001 = 2589 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline40Template :=
  StackSiteBuilder.ofSlice inline40Template 1999 inline40_slice
    (by
      change 1999 + inline40Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline40Template) (by decide))
    (by decide)

theorem inline40Site_startPC : inline40Site.startPC = UInt256.ofNat 2873 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2001) = UInt256.ofNat 2589
  rw [inline40_instructionPC]


theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2044).take inline41Template.length = inline41Template := by
  rfl

theorem inline41_instructionPC :
    Artifact.submissionArtifact.instructionPC 2044 = 2639 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline41Template :=
  StackSiteBuilder.ofSlice inline41Template 2042 inline41_slice
    (by
      change 2042 + inline41Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline41Template) (by decide))
    (by decide)

theorem inline41Site_startPC : inline41Site.startPC = UInt256.ofNat 2923 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2044) = UInt256.ofNat 2639
  rw [inline41_instructionPC]


theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2087).take inline42Template.length = inline42Template := by
  rfl

theorem inline42_instructionPC :
    Artifact.submissionArtifact.instructionPC 2087 = 2688 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline42Template :=
  StackSiteBuilder.ofSlice inline42Template 2085 inline42_slice
    (by
      change 2085 + inline42Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline42Template) (by decide))
    (by decide)

theorem inline42Site_startPC : inline42Site.startPC = UInt256.ofNat 2973 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2087) = UInt256.ofNat 2688
  rw [inline42_instructionPC]


theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2130).take inline43Template.length = inline43Template := by
  rfl

theorem inline43_instructionPC :
    Artifact.submissionArtifact.instructionPC 2130 = 2738 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline43Template :=
  StackSiteBuilder.ofSlice inline43Template 2128 inline43_slice
    (by
      change 2128 + inline43Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline43Template) (by decide))
    (by decide)

theorem inline43Site_startPC : inline43Site.startPC = UInt256.ofNat 3022 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2130) = UInt256.ofNat 2738
  rw [inline43_instructionPC]


theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2173).take inline44Template.length = inline44Template := by
  rfl

theorem inline44_instructionPC :
    Artifact.submissionArtifact.instructionPC 2173 = 2788 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline44Template :=
  StackSiteBuilder.ofSlice inline44Template 2171 inline44_slice
    (by
      change 2171 + inline44Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline44Template) (by decide))
    (by decide)

theorem inline44Site_startPC : inline44Site.startPC = UInt256.ofNat 3072 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2173) = UInt256.ofNat 2788
  rw [inline44_instructionPC]


theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2216).take inline45Template.length = inline45Template := by
  rfl

theorem inline45_instructionPC :
    Artifact.submissionArtifact.instructionPC 2216 = 2838 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline45Template :=
  StackSiteBuilder.ofSlice inline45Template 2214 inline45_slice
    (by
      change 2214 + inline45Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline45Template) (by decide))
    (by decide)

theorem inline45Site_startPC : inline45Site.startPC = UInt256.ofNat 3122 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2216) = UInt256.ofNat 2838
  rw [inline45_instructionPC]


theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2259).take inline46Template.length = inline46Template := by
  rfl

theorem inline46_instructionPC :
    Artifact.submissionArtifact.instructionPC 2259 = 2888 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline46Template :=
  StackSiteBuilder.ofSlice inline46Template 2257 inline46_slice
    (by
      change 2257 + inline46Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline46Template) (by decide))
    (by decide)

theorem inline46Site_startPC : inline46Site.startPC = UInt256.ofNat 3171 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2259) = UInt256.ofNat 2888
  rw [inline46_instructionPC]


theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2293).take inline47Template.length = inline47Template := by
  rfl

theorem inline47_instructionPC :
    Artifact.submissionArtifact.instructionPC 2293 = 2928 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline47Template :=
  StackSiteBuilder.ofSlice inline47Template 2291 inline47_slice
    (by
      change 2291 + inline47Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline47Template) (by decide))
    (by decide)

theorem inline47Site_startPC : inline47Site.startPC = UInt256.ofNat 3207 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2293) = UInt256.ofNat 2928
  rw [inline47_instructionPC]


theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2327).take group48Template.length = group48Template := by
  rfl

theorem group48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2327 = 2968 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka group48Template :=
  StackSiteBuilder.ofSlice group48Template 2325 group48_slice
    (by
      change 2325 + group48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := group48Template) (by decide))
    (by decide)

theorem group48Site_startPC : group48Site.startPC = UInt256.ofNat 3251 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2327) = UInt256.ofNat 2968
  rw [group48_instructionPC]


theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2330).take inline48Template.length = inline48Template := by
  rfl

theorem inline48_instructionPC :
    Artifact.submissionArtifact.instructionPC 2330 = 2972 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline48Template :=
  StackSiteBuilder.ofSlice inline48Template 2328 inline48_slice
    (by
      change 2328 + inline48Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline48Template) (by decide))
    (by decide)

theorem inline48Site_startPC : inline48Site.startPC = UInt256.ofNat 3274 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2330) = UInt256.ofNat 2972
  rw [inline48_instructionPC]


theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2384).take inline49Template.length = inline49Template := by
  rfl

theorem inline49_instructionPC :
    Artifact.submissionArtifact.instructionPC 2384 = 3034 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline49Template :=
  StackSiteBuilder.ofSlice inline49Template 2382 inline49_slice
    (by
      change 2382 + inline49Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline49Template) (by decide))
    (by decide)

theorem inline49Site_startPC : inline49Site.startPC = UInt256.ofNat 3300 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2384) = UInt256.ofNat 3034
  rw [inline49_instructionPC]


theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2438).take inline50Template.length = inline50Template := by
  rfl

theorem inline50_instructionPC :
    Artifact.submissionArtifact.instructionPC 2438 = 3096 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline50Template :=
  StackSiteBuilder.ofSlice inline50Template 2436 inline50_slice
    (by
      change 2436 + inline50Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline50Template) (by decide))
    (by decide)

theorem inline50Site_startPC : inline50Site.startPC = UInt256.ofNat 3395 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2438) = UInt256.ofNat 3096
  rw [inline50_instructionPC]


theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2492).take inline51Template.length = inline51Template := by
  rfl

theorem inline51_instructionPC :
    Artifact.submissionArtifact.instructionPC 2492 = 3160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline51Template :=
  StackSiteBuilder.ofSlice inline51Template 2490 inline51_slice
    (by
      change 2490 + inline51Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline51Template) (by decide))
    (by decide)

theorem inline51Site_startPC : inline51Site.startPC = UInt256.ofNat 3456 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2492) = UInt256.ofNat 3160
  rw [inline51_instructionPC]


theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2546).take inline52Template.length = inline52Template := by
  rfl

theorem inline52_instructionPC :
    Artifact.submissionArtifact.instructionPC 2546 = 3221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline52Template :=
  StackSiteBuilder.ofSlice inline52Template 2544 inline52_slice
    (by
      change 2544 + inline52Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline52Template) (by decide))
    (by decide)

theorem inline52Site_startPC : inline52Site.startPC = UInt256.ofNat 3516 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2546) = UInt256.ofNat 3221
  rw [inline52_instructionPC]


theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2591).take inline53Template.length = inline53Template := by
  rfl

theorem inline53_instructionPC :
    Artifact.submissionArtifact.instructionPC 2591 = 3273 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline53Template :=
  StackSiteBuilder.ofSlice inline53Template 2589 inline53_slice
    (by
      change 2589 + inline53Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline53Template) (by decide))
    (by decide)

theorem inline53Site_startPC : inline53Site.startPC = UInt256.ofNat 3562 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2591) = UInt256.ofNat 3273
  rw [inline53_instructionPC]


theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2645).take inline54Template.length = inline54Template := by
  rfl

theorem inline54_instructionPC :
    Artifact.submissionArtifact.instructionPC 2645 = 3356 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline54Template :=
  StackSiteBuilder.ofSlice inline54Template 2643 inline54_slice
    (by
      change 2643 + inline54Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline54Template) (by decide))
    (by decide)

theorem inline54Site_startPC : inline54Site.startPC = UInt256.ofNat 3627 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2645) = UInt256.ofNat 3356
  rw [inline54_instructionPC]


theorem inline55_slice :
    (Artifact.submissionArtifact.instructions.drop 2699).take inline55Template.length = inline55Template := by
  rfl

theorem inline55_instructionPC :
    Artifact.submissionArtifact.instructionPC 2699 = 3418 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline55Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline55Template :=
  StackSiteBuilder.ofSlice inline55Template 2697 inline55_slice
    (by
      change 2697 + inline55Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline55Template) (by decide))
    (by decide)

theorem inline55Site_startPC : inline55Site.startPC = UInt256.ofNat 3688 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2699) = UInt256.ofNat 3418
  rw [inline55_instructionPC]


theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 2753).take inline56Template.length = inline56Template := by
  rfl

theorem inline56_instructionPC :
    Artifact.submissionArtifact.instructionPC 2753 = 3480 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline56Template :=
  StackSiteBuilder.ofSlice inline56Template 2751 inline56_slice
    (by
      change 2751 + inline56Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline56Template) (by decide))
    (by decide)

theorem inline56Site_startPC : inline56Site.startPC = UInt256.ofNat 3714 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2753) = UInt256.ofNat 3480
  rw [inline56_instructionPC]


theorem inline57_slice :
    (Artifact.submissionArtifact.instructions.drop 2807).take inline57Template.length = inline57Template := by
  rfl

theorem inline57_instructionPC :
    Artifact.submissionArtifact.instructionPC 2807 = 3540 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline57Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline57Template :=
  StackSiteBuilder.ofSlice inline57Template 2805 inline57_slice
    (by
      change 2805 + inline57Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline57Template) (by decide))
    (by decide)

theorem inline57Site_startPC : inline57Site.startPC = UInt256.ofNat 3809 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2807) = UInt256.ofNat 3540
  rw [inline57_instructionPC]


theorem inline58_slice :
    (Artifact.submissionArtifact.instructions.drop 2861).take inline58Template.length = inline58Template := by
  rfl

theorem inline58_instructionPC :
    Artifact.submissionArtifact.instructionPC 2861 = 3600 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline58Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline58Template :=
  StackSiteBuilder.ofSlice inline58Template 2859 inline58_slice
    (by
      change 2859 + inline58Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline58Template) (by decide))
    (by decide)

theorem inline58Site_startPC : inline58Site.startPC = UInt256.ofNat 3870 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2861) = UInt256.ofNat 3600
  rw [inline58_instructionPC]


theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 2915).take inline59Template.length = inline59Template := by
  rfl

theorem inline59_instructionPC :
    Artifact.submissionArtifact.instructionPC 2915 = 3661 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline59Template :=
  StackSiteBuilder.ofSlice inline59Template 2913 inline59_slice
    (by
      change 2913 + inline59Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline59Template) (by decide))
    (by decide)

theorem inline59Site_startPC : inline59Site.startPC = UInt256.ofNat 3931 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2915) = UInt256.ofNat 3661
  rw [inline59_instructionPC]


theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 2969).take inline60Template.length = inline60Template := by
  rfl

theorem inline60_instructionPC :
    Artifact.submissionArtifact.instructionPC 2969 = 3725 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline60Template :=
  StackSiteBuilder.ofSlice inline60Template 2967 inline60_slice
    (by
      change 2967 + inline60Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline60Template) (by decide))
    (by decide)

theorem inline60Site_startPC : inline60Site.startPC = UInt256.ofNat 3992 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2969) = UInt256.ofNat 3725
  rw [inline60_instructionPC]


theorem inline61_slice :
    (Artifact.submissionArtifact.instructions.drop 3023).take inline61Template.length = inline61Template := by
  rfl

theorem inline61_instructionPC :
    Artifact.submissionArtifact.instructionPC 3023 = 3786 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline61Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline61Template :=
  StackSiteBuilder.ofSlice inline61Template 3021 inline61_slice
    (by
      change 3021 + inline61Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline61Template) (by decide))
    (by decide)

theorem inline61Site_startPC : inline61Site.startPC = UInt256.ofNat 4053 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3023) = UInt256.ofNat 3786
  rw [inline61_instructionPC]


theorem inline62_slice :
    (Artifact.submissionArtifact.instructions.drop 3077).take inline62Template.length = inline62Template := by
  rfl

theorem inline62_instructionPC :
    Artifact.submissionArtifact.instructionPC 3077 = 3849 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline62Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline62Template :=
  StackSiteBuilder.ofSlice inline62Template 3075 inline62_slice
    (by
      change 3075 + inline62Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline62Template) (by decide))
    (by decide)

theorem inline62Site_startPC : inline62Site.startPC = UInt256.ofNat 4114 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3077) = UInt256.ofNat 3849
  rw [inline62_instructionPC]


theorem inline63_slice :
    (Artifact.submissionArtifact.instructions.drop 3131).take inline63Template.length = inline63Template := by
  rfl

theorem inline63_instructionPC :
    Artifact.submissionArtifact.instructionPC 3131 = 3910 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline63Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline63Template :=
  StackSiteBuilder.ofSlice inline63Template 3129 inline63_slice
    (by
      change 3129 + inline63Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline63Template) (by decide))
    (by decide)

theorem inline63Site_startPC : inline63Site.startPC = UInt256.ofNat 4175 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3131) = UInt256.ofNat 3910
  rw [inline63_instructionPC]


theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3185).take group64Template.length = group64Template := by
  rfl

theorem group64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3185 = 3971 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka group64Template :=
  StackSiteBuilder.ofSlice group64Template 3183 group64_slice
    (by
      change 3183 + group64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := group64Template) (by decide))
    (by decide)

theorem group64Site_startPC : group64Site.startPC = UInt256.ofNat 4202 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3185) = UInt256.ofNat 3971
  rw [group64_instructionPC]


theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3188).take inline64Template.length = inline64Template := by
  rfl

theorem inline64_instructionPC :
    Artifact.submissionArtifact.instructionPC 3188 = 3974 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline64Template :=
  StackSiteBuilder.ofSlice inline64Template 3186 inline64_slice
    (by
      change 3186 + inline64Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline64Template) (by decide))
    (by decide)

theorem inline64Site_startPC : inline64Site.startPC = UInt256.ofNat 4243 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3188) = UInt256.ofNat 3974
  rw [inline64_instructionPC]


theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3236).take inline65Template.length = inline65Template := by
  rfl

theorem inline65_instructionPC :
    Artifact.submissionArtifact.instructionPC 3236 = 4029 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline65Template :=
  StackSiteBuilder.ofSlice inline65Template 3234 inline65_slice
    (by
      change 3234 + inline65Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline65Template) (by decide))
    (by decide)

theorem inline65Site_startPC : inline65Site.startPC = UInt256.ofNat 4298 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3236) = UInt256.ofNat 4029
  rw [inline65_instructionPC]


theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3284).take inline66Template.length = inline66Template := by
  rfl

theorem inline66_instructionPC :
    Artifact.submissionArtifact.instructionPC 3284 = 4084 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline66Template :=
  StackSiteBuilder.ofSlice inline66Template 3282 inline66_slice
    (by
      change 3282 + inline66Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline66Template) (by decide))
    (by decide)

theorem inline66Site_startPC : inline66Site.startPC = UInt256.ofNat 4352 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3284) = UInt256.ofNat 4084
  rw [inline66_instructionPC]


theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3332).take inline67Template.length = inline67Template := by
  rfl

theorem inline67_instructionPC :
    Artifact.submissionArtifact.instructionPC 3332 = 4139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline67Template :=
  StackSiteBuilder.ofSlice inline67Template 3330 inline67_slice
    (by
      change 3330 + inline67Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline67Template) (by decide))
    (by decide)

theorem inline67Site_startPC : inline67Site.startPC = UInt256.ofNat 4373 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3332) = UInt256.ofNat 4139
  rw [inline67_instructionPC]


theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3380).take inline68Template.length = inline68Template := by
  rfl

theorem inline68_instructionPC :
    Artifact.submissionArtifact.instructionPC 3380 = 4194 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline68Template :=
  StackSiteBuilder.ofSlice inline68Template 3378 inline68_slice
    (by
      change 3378 + inline68Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline68Template) (by decide))
    (by decide)

theorem inline68Site_startPC : inline68Site.startPC = UInt256.ofNat 4462 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3380) = UInt256.ofNat 4194
  rw [inline68_instructionPC]


theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3428).take inline69Template.length = inline69Template := by
  rfl

theorem inline69_instructionPC :
    Artifact.submissionArtifact.instructionPC 3428 = 4253 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline69Template :=
  StackSiteBuilder.ofSlice inline69Template 3426 inline69_slice
    (by
      change 3426 + inline69Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline69Template) (by decide))
    (by decide)

theorem inline69Site_startPC : inline69Site.startPC = UInt256.ofNat 4516 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3428) = UInt256.ofNat 4253
  rw [inline69_instructionPC]


theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3476).take inline70Template.length = inline70Template := by
  rfl

theorem inline70_instructionPC :
    Artifact.submissionArtifact.instructionPC 3476 = 4307 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline70Template :=
  StackSiteBuilder.ofSlice inline70Template 3474 inline70_slice
    (by
      change 3474 + inline70Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline70Template) (by decide))
    (by decide)

theorem inline70Site_startPC : inline70Site.startPC = UInt256.ofNat 4537 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3476) = UInt256.ofNat 4307
  rw [inline70_instructionPC]


theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3524).take inline71Template.length = inline71Template := by
  rfl

theorem inline71_instructionPC :
    Artifact.submissionArtifact.instructionPC 3524 = 4362 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline71Template :=
  StackSiteBuilder.ofSlice inline71Template 3522 inline71_slice
    (by
      change 3522 + inline71Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline71Template) (by decide))
    (by decide)

theorem inline71Site_startPC : inline71Site.startPC = UInt256.ofNat 4626 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3524) = UInt256.ofNat 4362
  rw [inline71_instructionPC]


theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3572).take inline72Template.length = inline72Template := by
  rfl

theorem inline72_instructionPC :
    Artifact.submissionArtifact.instructionPC 3572 = 4418 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline72Template :=
  StackSiteBuilder.ofSlice inline72Template 3570 inline72_slice
    (by
      change 3570 + inline72Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline72Template) (by decide))
    (by decide)

theorem inline72Site_startPC : inline72Site.startPC = UInt256.ofNat 4681 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3572) = UInt256.ofNat 4418
  rw [inline72_instructionPC]


theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3620).take inline73Template.length = inline73Template := by
  rfl

theorem inline73_instructionPC :
    Artifact.submissionArtifact.instructionPC 3620 = 4472 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline73Template :=
  StackSiteBuilder.ofSlice inline73Template 3618 inline73_slice
    (by
      change 3618 + inline73Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline73Template) (by decide))
    (by decide)

theorem inline73Site_startPC : inline73Site.startPC = UInt256.ofNat 4732 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3620) = UInt256.ofNat 4472
  rw [inline73_instructionPC]


theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3668).take inline74Template.length = inline74Template := by
  rfl

theorem inline74_instructionPC :
    Artifact.submissionArtifact.instructionPC 3668 = 4527 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline74Template :=
  StackSiteBuilder.ofSlice inline74Template 3666 inline74_slice
    (by
      change 3666 + inline74Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline74Template) (by decide))
    (by decide)

theorem inline74Site_startPC : inline74Site.startPC = UInt256.ofNat 4790 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3668) = UInt256.ofNat 4527
  rw [inline74_instructionPC]


theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3716).take inline75Template.length = inline75Template := by
  rfl

theorem inline75_instructionPC :
    Artifact.submissionArtifact.instructionPC 3716 = 4582 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline75Template :=
  StackSiteBuilder.ofSlice inline75Template 3714 inline75_slice
    (by
      change 3714 + inline75Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline75Template) (by decide))
    (by decide)

theorem inline75Site_startPC : inline75Site.startPC = UInt256.ofNat 4845 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3716) = UInt256.ofNat 4582
  rw [inline75_instructionPC]


theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3764).take inline76Template.length = inline76Template := by
  rfl

theorem inline76_instructionPC :
    Artifact.submissionArtifact.instructionPC 3764 = 4637 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline76Template :=
  StackSiteBuilder.ofSlice inline76Template 3762 inline76_slice
    (by
      change 3762 + inline76Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline76Template) (by decide))
    (by decide)

theorem inline76Site_startPC : inline76Site.startPC = UInt256.ofNat 4900 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3764) = UInt256.ofNat 4637
  rw [inline76_instructionPC]


theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 3812).take inline77Template.length = inline77Template := by
  rfl

theorem inline77_instructionPC :
    Artifact.submissionArtifact.instructionPC 3812 = 4692 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline77Template :=
  StackSiteBuilder.ofSlice inline77Template 3810 inline77_slice
    (by
      change 3810 + inline77Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline77Template) (by decide))
    (by decide)

theorem inline77Site_startPC : inline77Site.startPC = UInt256.ofNat 4954 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3812) = UInt256.ofNat 4692
  rw [inline77_instructionPC]


theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3860).take inline78Template.length = inline78Template := by
  rfl

theorem inline78_instructionPC :
    Artifact.submissionArtifact.instructionPC 3860 = 4746 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline78Template :=
  StackSiteBuilder.ofSlice inline78Template 3858 inline78_slice
    (by
      change 3858 + inline78Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline78Template) (by decide))
    (by decide)

theorem inline78Site_startPC : inline78Site.startPC = UInt256.ofNat 5009 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3860) = UInt256.ofNat 4746
  rw [inline78_instructionPC]


theorem inline79_slice :
    (Artifact.submissionArtifact.instructions.drop 3908).take inline79Template.length = inline79Template := by
  rfl

theorem inline79_instructionPC :
    Artifact.submissionArtifact.instructionPC 3908 = 4801 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def inline79Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline79Template :=
  StackSiteBuilder.ofSlice inline79Template 3906 inline79_slice
    (by
      change 3906 + inline79Template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := inline79Template) (by decide))
    (by decide)

theorem inline79Site_startPC : inline79Site.startPC = UInt256.ofNat 5064 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3908) = UInt256.ofNat 4801
  rw [inline79_instructionPC]


theorem coreExit_slice :
    (Artifact.submissionArtifact.instructions.drop 3956).take coreExitTemplate.length = coreExitTemplate := by
  rfl

theorem coreExit_instructionPC :
    Artifact.submissionArtifact.instructionPC 3956 = 4856 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def coreExitSite : GenericRoundSite Artifact.submissionArtifact .Osaka coreExitTemplate :=
  StackSiteBuilder.ofSlice coreExitTemplate 3954 coreExit_slice
    (by
      change 3954 + coreExitTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := coreExitTemplate) (by decide))
    (by decide)

theorem coreExitSite_startPC : coreExitSite.startPC = UInt256.ofNat 5119 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3956) = UInt256.ofNat 4856
  rw [coreExit_instructionPC]


theorem helper_slice :
    (Artifact.submissionArtifact.instructions.drop 4028).take fullTemplate.length = fullTemplate := by
  rfl

theorem helper_instructionPC :
    Artifact.submissionArtifact.instructionPC 4028 = 4940 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def helperSite : GenericRoundSite Artifact.submissionArtifact .Osaka fullTemplate :=
  StackSiteBuilder.ofSlice fullTemplate 4026 helper_slice
    (by
      change 4026 + fullTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := fullTemplate) (by decide))
    (by decide)

theorem helperSite_startPC : helperSite.startPC = UInt256.ofNat 5202 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4028) = UInt256.ofNat 4940
  rw [helper_instructionPC]

def wholeSites : WholeCoreSites Artifact.submissionArtifact .Osaka where
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

theorem validJumpDest_5168 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 5168 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4028 (by rfl)
  rw [helper_instructionPC] at h
  exact h

theorem validJumpDest_1920 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 1920 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1260 (by rfl)
  rw [return18_instructionPC] at h
  exact h

theorem validJumpDest_2077 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2077 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1389 (by rfl)
  rw [call22_instructionPC] at h
  exact h

theorem validJumpDest_2116 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2116 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1412 (by rfl)
  rw [return24_instructionPC] at h
  exact h

theorem validJumpDest_2264 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2264 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1532 (by rfl)
  rw [call28_instructionPC] at h
  exact h

theorem validJumpDest_2303 :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 2303 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 1555 (by rfl)
  rw [return30_instructionPC] at h
  exact h

theorem coreJumpValid (s : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) : CoreJumpValid s := by
  intro dest hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [hcode]
  · exact validJumpDest_5168
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
    GasSteps {s with pc := UInt256.ofNat 998, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho}
      {s with pc := UInt256.ofNat 5083, stack := coreStack [.d, .b, .c, .upper, .e, .factor, .pair, .a, .lower] (coreCryptoResult words left right) rho} :=
  gasSteps_wholeCore_normalized wholeSites s words left right rho hstack hrun hactive
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
#print axioms validJumpDest_5168
#print axioms validJumpDest_1920
#print axioms validJumpDest_2077
#print axioms validJumpDest_2116
#print axioms validJumpDest_2264
#print axioms validJumpDest_2303
#print axioms coreJumpValid
#print axioms gasSteps_core_normalized

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCoreSites

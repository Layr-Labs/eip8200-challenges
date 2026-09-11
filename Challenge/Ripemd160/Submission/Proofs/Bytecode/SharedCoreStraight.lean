import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCoreStraight
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace PairedLaneWordGroupTwoHoist
open PairedAllInlineCoreTrace PairedAllInlineNewPairs
theorem group0_pcAfter : pcAfter (UInt256.ofNat 727) PairedAllInlineCoreTrace.group0Template = UInt256.ofNat 735 := by rfl
def group0Physical : PairedAllInlineCoreTrace.CoreBlock 727 735 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group0Template
  eval := PairedAllInlineCoreTrace.group0Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group0Template s (UInt256.ofNat 727) f.frame rho hstack hrun
    rw [group0_pcAfter] at h
    exact h

theorem group0_slice :
    (Artifact.submissionArtifact.instructions.drop 472).take group0Physical.code.length = group0Physical.code := by rfl
def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka group0Physical.code :=
  StackSiteBuilder.ofSlice group0Physical.code 472 group0_slice
    (by change 472 + group0Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group0Physical.code) (by decide))
    (by decide)
theorem group0_pc : group0Site.startPC = UInt256.ofNat 735 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 472) = UInt256.ofNat 727
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group0_advances : ∀ instruction ∈ group0Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group0Gas : PairedAllInlineCoreTrace.CoreGasBlock group0Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group0Physical group0Site group0_pc group0_advances
theorem inline0_pcAfter : pcAfter (UInt256.ofNat 735) PairedSynthCoreTrace.inline0Template = UInt256.ofNat 785 := by rfl
def inline0Physical : PairedAllInlineCoreTrace.CoreBlock 735 785 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline0Template
  eval := PairedAllInlineCoreTrace.inline0Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline0Template_word s (UInt256.ofNat 735) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline0_pcAfter] at h
    exact h

theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 475).take inline0Physical.code.length = inline0Physical.code := by rfl
def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline0Physical.code :=
  StackSiteBuilder.ofSlice inline0Physical.code 475 inline0_slice
    (by change 475 + inline0Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline0Physical.code) (by decide))
    (by decide)
theorem inline0_pc : inline0Site.startPC = UInt256.ofNat 743 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 475) = UInt256.ofNat 735
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline0_advances : ∀ instruction ∈ inline0Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline0Gas : PairedAllInlineCoreTrace.CoreGasBlock inline0Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline0Physical inline0Site inline0_pc inline0_advances
theorem inline1_pcAfter : pcAfter (UInt256.ofNat 785) PairedSynthCoreTrace.inline1Template = UInt256.ofNat 835 := by rfl
def inline1Physical : PairedAllInlineCoreTrace.CoreBlock 785 835 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline1Template
  eval := PairedAllInlineCoreTrace.inline1Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline1Template_word s (UInt256.ofNat 785) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline1_pcAfter] at h
    exact h

theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 519).take inline1Physical.code.length = inline1Physical.code := by rfl
def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline1Physical.code :=
  StackSiteBuilder.ofSlice inline1Physical.code 519 inline1_slice
    (by change 519 + inline1Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline1Physical.code) (by decide))
    (by decide)
theorem inline1_pc : inline1Site.startPC = UInt256.ofNat 793 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 519) = UInt256.ofNat 785
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline1_advances : ∀ instruction ∈ inline1Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline1Gas : PairedAllInlineCoreTrace.CoreGasBlock inline1Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline1Physical inline1Site inline1_pc inline1_advances
theorem inline2_pcAfter : pcAfter (UInt256.ofNat 835) PairedSynthCoreTrace.inline2Template = UInt256.ofNat 886 := by rfl
def inline2Physical : PairedAllInlineCoreTrace.CoreBlock 835 886 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline2Template
  eval := PairedAllInlineCoreTrace.inline2Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline2Template_word s (UInt256.ofNat 835) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline2_pcAfter] at h
    exact h

theorem inline2_slice :
    (Artifact.submissionArtifact.instructions.drop 563).take inline2Physical.code.length = inline2Physical.code := by rfl
def inline2Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline2Physical.code :=
  StackSiteBuilder.ofSlice inline2Physical.code 563 inline2_slice
    (by change 563 + inline2Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline2Physical.code) (by decide))
    (by decide)
theorem inline2_pc : inline2Site.startPC = UInt256.ofNat 843 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 563) = UInt256.ofNat 835
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline2_advances : ∀ instruction ∈ inline2Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline2Gas : PairedAllInlineCoreTrace.CoreGasBlock inline2Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline2Physical inline2Site inline2_pc inline2_advances
theorem inline3_pcAfter : pcAfter (UInt256.ofNat 886) PairedSynthCoreTrace.inline3Template = UInt256.ofNat 933 := by rfl
def inline3Physical : PairedAllInlineCoreTrace.CoreBlock 886 933 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline3Template
  eval := PairedAllInlineCoreTrace.inline3Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline3Template_word s (UInt256.ofNat 886) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline3_pcAfter] at h
    exact h

theorem inline3_slice :
    (Artifact.submissionArtifact.instructions.drop 607).take inline3Physical.code.length = inline3Physical.code := by rfl
def inline3Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline3Physical.code :=
  StackSiteBuilder.ofSlice inline3Physical.code 607 inline3_slice
    (by change 607 + inline3Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline3Physical.code) (by decide))
    (by decide)
theorem inline3_pc : inline3Site.startPC = UInt256.ofNat 894 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 607) = UInt256.ofNat 886
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline3_advances : ∀ instruction ∈ inline3Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline3Gas : PairedAllInlineCoreTrace.CoreGasBlock inline3Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline3Physical inline3Site inline3_pc inline3_advances
theorem inline4_pcAfter : pcAfter (UInt256.ofNat 933) PairedSynthCoreTrace.inline4Template = UInt256.ofNat 984 := by rfl
def inline4Physical : PairedAllInlineCoreTrace.CoreBlock 933 984 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline4Template
  eval := PairedAllInlineCoreTrace.inline4Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline4Template_word s (UInt256.ofNat 933) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline4_pcAfter] at h
    exact h

theorem inline4_slice :
    (Artifact.submissionArtifact.instructions.drop 649).take inline4Physical.code.length = inline4Physical.code := by rfl
def inline4Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline4Physical.code :=
  StackSiteBuilder.ofSlice inline4Physical.code 649 inline4_slice
    (by change 649 + inline4Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline4Physical.code) (by decide))
    (by decide)
theorem inline4_pc : inline4Site.startPC = UInt256.ofNat 941 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 649) = UInt256.ofNat 933
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline4_advances : ∀ instruction ∈ inline4Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline4Gas : PairedAllInlineCoreTrace.CoreGasBlock inline4Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline4Physical inline4Site inline4_pc inline4_advances
theorem inline5_pcAfter : pcAfter (UInt256.ofNat 984) PairedSynthCoreTrace.inline5Template = UInt256.ofNat 1035 := by rfl
def inline5Physical : PairedAllInlineCoreTrace.CoreBlock 984 1035 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline5Template
  eval := PairedAllInlineCoreTrace.inline5Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline5Template_word s (UInt256.ofNat 984) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline5_pcAfter] at h
    exact h

theorem inline5_slice :
    (Artifact.submissionArtifact.instructions.drop 693).take inline5Physical.code.length = inline5Physical.code := by rfl
def inline5Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline5Physical.code :=
  StackSiteBuilder.ofSlice inline5Physical.code 693 inline5_slice
    (by change 693 + inline5Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline5Physical.code) (by decide))
    (by decide)
theorem inline5_pc : inline5Site.startPC = UInt256.ofNat 992 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 693) = UInt256.ofNat 984
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline5_advances : ∀ instruction ∈ inline5Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline5Gas : PairedAllInlineCoreTrace.CoreGasBlock inline5Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline5Physical inline5Site inline5_pc inline5_advances
theorem inline6_pcAfter : pcAfter (UInt256.ofNat 1035) PairedSynthCoreTrace.inline6Template = UInt256.ofNat 1086 := by rfl
def inline6Physical : PairedAllInlineCoreTrace.CoreBlock 1035 1086 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline6Template
  eval := PairedAllInlineCoreTrace.inline6Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline6Template_word s (UInt256.ofNat 1035) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline6_pcAfter] at h
    exact h

theorem inline6_slice :
    (Artifact.submissionArtifact.instructions.drop 737).take inline6Physical.code.length = inline6Physical.code := by rfl
def inline6Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline6Physical.code :=
  StackSiteBuilder.ofSlice inline6Physical.code 737 inline6_slice
    (by change 737 + inline6Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline6Physical.code) (by decide))
    (by decide)
theorem inline6_pc : inline6Site.startPC = UInt256.ofNat 1043 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 737) = UInt256.ofNat 1035
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline6_advances : ∀ instruction ∈ inline6Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline6Gas : PairedAllInlineCoreTrace.CoreGasBlock inline6Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline6Physical inline6Site inline6_pc inline6_advances
theorem inline7_pcAfter : pcAfter (UInt256.ofNat 1086) PairedSynthCoreTrace.inline7Template = UInt256.ofNat 1137 := by rfl
def inline7Physical : PairedAllInlineCoreTrace.CoreBlock 1086 1137 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline7Template
  eval := PairedAllInlineCoreTrace.inline7Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline7Template_word s (UInt256.ofNat 1086) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline7_pcAfter] at h
    exact h

theorem inline7_slice :
    (Artifact.submissionArtifact.instructions.drop 781).take inline7Physical.code.length = inline7Physical.code := by rfl
def inline7Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline7Physical.code :=
  StackSiteBuilder.ofSlice inline7Physical.code 781 inline7_slice
    (by change 781 + inline7Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline7Physical.code) (by decide))
    (by decide)
theorem inline7_pc : inline7Site.startPC = UInt256.ofNat 1094 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 781) = UInt256.ofNat 1086
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline7_advances : ∀ instruction ∈ inline7Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline7Gas : PairedAllInlineCoreTrace.CoreGasBlock inline7Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline7Physical inline7Site inline7_pc inline7_advances
theorem inline8_pcAfter : pcAfter (UInt256.ofNat 1137) PairedSynthCoreTrace.inline8Template = UInt256.ofNat 1188 := by rfl
def inline8Physical : PairedAllInlineCoreTrace.CoreBlock 1137 1188 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline8Template
  eval := PairedAllInlineCoreTrace.inline8Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline8Template_word s (UInt256.ofNat 1137) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline8_pcAfter] at h
    exact h

theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 825).take inline8Physical.code.length = inline8Physical.code := by rfl
def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline8Physical.code :=
  StackSiteBuilder.ofSlice inline8Physical.code 825 inline8_slice
    (by change 825 + inline8Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline8Physical.code) (by decide))
    (by decide)
theorem inline8_pc : inline8Site.startPC = UInt256.ofNat 1145 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 825) = UInt256.ofNat 1137
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline8_advances : ∀ instruction ∈ inline8Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline8Gas : PairedAllInlineCoreTrace.CoreGasBlock inline8Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline8Physical inline8Site inline8_pc inline8_advances
theorem inline9_pcAfter : pcAfter (UInt256.ofNat 1188) PairedSynthCoreTrace.inline9Template = UInt256.ofNat 1239 := by rfl
def inline9Physical : PairedAllInlineCoreTrace.CoreBlock 1188 1239 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline9Template
  eval := PairedAllInlineCoreTrace.inline9Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline9Template_word s (UInt256.ofNat 1188) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline9_pcAfter] at h
    exact h

theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 869).take inline9Physical.code.length = inline9Physical.code := by rfl
def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline9Physical.code :=
  StackSiteBuilder.ofSlice inline9Physical.code 869 inline9_slice
    (by change 869 + inline9Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline9Physical.code) (by decide))
    (by decide)
theorem inline9_pc : inline9Site.startPC = UInt256.ofNat 1196 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 869) = UInt256.ofNat 1188
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline9_advances : ∀ instruction ∈ inline9Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline9Gas : PairedAllInlineCoreTrace.CoreGasBlock inline9Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline9Physical inline9Site inline9_pc inline9_advances
theorem inline10_pcAfter : pcAfter (UInt256.ofNat 1239) PairedSynthCoreTrace.inline10Template = UInt256.ofNat 1290 := by rfl
def inline10Physical : PairedAllInlineCoreTrace.CoreBlock 1239 1290 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline10Template
  eval := PairedAllInlineCoreTrace.inline10Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline10Template_word s (UInt256.ofNat 1239) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline10_pcAfter] at h
    exact h

theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 913).take inline10Physical.code.length = inline10Physical.code := by rfl
def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline10Physical.code :=
  StackSiteBuilder.ofSlice inline10Physical.code 913 inline10_slice
    (by change 913 + inline10Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline10Physical.code) (by decide))
    (by decide)
theorem inline10_pc : inline10Site.startPC = UInt256.ofNat 1247 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 913) = UInt256.ofNat 1239
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline10_advances : ∀ instruction ∈ inline10Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline10Gas : PairedAllInlineCoreTrace.CoreGasBlock inline10Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline10Physical inline10Site inline10_pc inline10_advances
theorem inline11_pcAfter : pcAfter (UInt256.ofNat 1290) PairedSynthCoreTrace.inline11Template = UInt256.ofNat 1341 := by rfl
def inline11Physical : PairedAllInlineCoreTrace.CoreBlock 1290 1341 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline11Template
  eval := PairedAllInlineCoreTrace.inline11Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline11Template_word s (UInt256.ofNat 1290) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline11_pcAfter] at h
    exact h

theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 957).take inline11Physical.code.length = inline11Physical.code := by rfl
def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline11Physical.code :=
  StackSiteBuilder.ofSlice inline11Physical.code 957 inline11_slice
    (by change 957 + inline11Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline11Physical.code) (by decide))
    (by decide)
theorem inline11_pc : inline11Site.startPC = UInt256.ofNat 1298 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 957) = UInt256.ofNat 1290
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline11_advances : ∀ instruction ∈ inline11Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline11Gas : PairedAllInlineCoreTrace.CoreGasBlock inline11Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline11Physical inline11Site inline11_pc inline11_advances
theorem inline12_pcAfter : pcAfter (UInt256.ofNat 1341) PairedSynthCoreTrace.inline12Template = UInt256.ofNat 1391 := by rfl
def inline12Physical : PairedAllInlineCoreTrace.CoreBlock 1341 1391 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline12Template
  eval := PairedAllInlineCoreTrace.inline12Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline12Template_word s (UInt256.ofNat 1341) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline12_pcAfter] at h
    exact h

theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1001).take inline12Physical.code.length = inline12Physical.code := by rfl
def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline12Physical.code :=
  StackSiteBuilder.ofSlice inline12Physical.code 1001 inline12_slice
    (by change 1001 + inline12Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline12Physical.code) (by decide))
    (by decide)
theorem inline12_pc : inline12Site.startPC = UInt256.ofNat 1349 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1001) = UInt256.ofNat 1341
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline12_advances : ∀ instruction ∈ inline12Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline12Gas : PairedAllInlineCoreTrace.CoreGasBlock inline12Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline12Physical inline12Site inline12_pc inline12_advances
theorem inline13_pcAfter : pcAfter (UInt256.ofNat 1391) PairedSynthCoreTrace.inline13Template = UInt256.ofNat 1442 := by rfl
def inline13Physical : PairedAllInlineCoreTrace.CoreBlock 1391 1442 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline13Template
  eval := PairedAllInlineCoreTrace.inline13Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline13Template_word s (UInt256.ofNat 1391) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline13_pcAfter] at h
    exact h

theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1045).take inline13Physical.code.length = inline13Physical.code := by rfl
def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline13Physical.code :=
  StackSiteBuilder.ofSlice inline13Physical.code 1045 inline13_slice
    (by change 1045 + inline13Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline13Physical.code) (by decide))
    (by decide)
theorem inline13_pc : inline13Site.startPC = UInt256.ofNat 1399 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1045) = UInt256.ofNat 1391
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline13_advances : ∀ instruction ∈ inline13Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline13Gas : PairedAllInlineCoreTrace.CoreGasBlock inline13Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline13Physical inline13Site inline13_pc inline13_advances
theorem inline14_pcAfter : pcAfter (UInt256.ofNat 1442) PairedSynthCoreTrace.inline14Template = UInt256.ofNat 1493 := by rfl
def inline14Physical : PairedAllInlineCoreTrace.CoreBlock 1442 1493 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline14Template
  eval := PairedAllInlineCoreTrace.inline14Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline14Template_word s (UInt256.ofNat 1442) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline14_pcAfter] at h
    exact h

theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1089).take inline14Physical.code.length = inline14Physical.code := by rfl
def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline14Physical.code :=
  StackSiteBuilder.ofSlice inline14Physical.code 1089 inline14_slice
    (by change 1089 + inline14Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline14Physical.code) (by decide))
    (by decide)
theorem inline14_pc : inline14Site.startPC = UInt256.ofNat 1450 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1089) = UInt256.ofNat 1442
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline14_advances : ∀ instruction ∈ inline14Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline14Gas : PairedAllInlineCoreTrace.CoreGasBlock inline14Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline14Physical inline14Site inline14_pc inline14_advances
theorem inline15_pcAfter : pcAfter (UInt256.ofNat 1493) PairedSynthCoreTrace.inline15Template = UInt256.ofNat 1544 := by rfl
def inline15Physical : PairedAllInlineCoreTrace.CoreBlock 1493 1544 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline15Template
  eval := PairedAllInlineCoreTrace.inline15Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline15Template_word s (UInt256.ofNat 1493) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline15_pcAfter] at h
    exact h

theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1133).take inline15Physical.code.length = inline15Physical.code := by rfl
def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline15Physical.code :=
  StackSiteBuilder.ofSlice inline15Physical.code 1133 inline15_slice
    (by change 1133 + inline15Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline15Physical.code) (by decide))
    (by decide)
theorem inline15_pc : inline15Site.startPC = UInt256.ofNat 1501 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1133) = UInt256.ofNat 1493
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline15_advances : ∀ instruction ∈ inline15Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline15Gas : PairedAllInlineCoreTrace.CoreGasBlock inline15Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline15Physical inline15Site inline15_pc inline15_advances
theorem group16_pcAfter : pcAfter (UInt256.ofNat 1544) PairedAllInlineCoreTrace.group16Template = UInt256.ofNat 1567 := by rfl
def group16Physical : PairedAllInlineCoreTrace.CoreBlock 1544 1567 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group16Template
  eval := PairedAllInlineCoreTrace.group16Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group16Template s (UInt256.ofNat 1544) f.frame rho hstack hrun
    rw [group16_pcAfter] at h
    exact h

theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1177).take group16Physical.code.length = group16Physical.code := by rfl
def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka group16Physical.code :=
  StackSiteBuilder.ofSlice group16Physical.code 1177 group16_slice
    (by change 1177 + group16Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group16Physical.code) (by decide))
    (by decide)
theorem group16_pc : group16Site.startPC = UInt256.ofNat 1552 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1177) = UInt256.ofNat 1544
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group16_advances : ∀ instruction ∈ group16Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group16Gas : PairedAllInlineCoreTrace.CoreGasBlock group16Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group16Physical group16Site group16_pc group16_advances
theorem inline16_pcAfter : pcAfter (UInt256.ofNat 1567) PairedAllInlineNewPairs.inline16Template = UInt256.ofNat 1620 := by rfl
def inline16Physical : PairedAllInlineCoreTrace.CoreBlock 1567 1620 [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline16Template
  eval := PairedAllInlineCoreTrace.inline16Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline16Template_word s (UInt256.ofNat 1567) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline16_pcAfter] at h
    exact h

theorem inline16_slice :
    (Artifact.submissionArtifact.instructions.drop 1180).take inline16Physical.code.length = inline16Physical.code := by rfl
def inline16Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline16Physical.code :=
  StackSiteBuilder.ofSlice inline16Physical.code 1180 inline16_slice
    (by change 1180 + inline16Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline16Physical.code) (by decide))
    (by decide)
theorem inline16_pc : inline16Site.startPC = UInt256.ofNat 1575 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1180) = UInt256.ofNat 1567
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline16_advances : ∀ instruction ∈ inline16Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline16Gas : PairedAllInlineCoreTrace.CoreGasBlock inline16Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline16Physical inline16Site inline16_pc inline16_advances
theorem inline17_pcAfter : pcAfter (UInt256.ofNat 1620) PairedAllInlineNewPairs.inline17Template = UInt256.ofNat 1673 := by rfl
def inline17Physical : PairedAllInlineCoreTrace.CoreBlock 1620 1673 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline17Template
  eval := PairedAllInlineCoreTrace.inline17Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline17Template_word s (UInt256.ofNat 1620) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline17_pcAfter] at h
    exact h

theorem inline17_slice :
    (Artifact.submissionArtifact.instructions.drop 1226).take inline17Physical.code.length = inline17Physical.code := by rfl
def inline17Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline17Physical.code :=
  StackSiteBuilder.ofSlice inline17Physical.code 1226 inline17_slice
    (by change 1226 + inline17Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline17Physical.code) (by decide))
    (by decide)
theorem inline17_pc : inline17Site.startPC = UInt256.ofNat 1628 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1226) = UInt256.ofNat 1620
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline17_advances : ∀ instruction ∈ inline17Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline17Gas : PairedAllInlineCoreTrace.CoreGasBlock inline17Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline17Physical inline17Site inline17_pc inline17_advances
theorem inline18_pcAfter : pcAfter (UInt256.ofNat 1673) PairedAllInlineCoreTrace.inline18Template = UInt256.ofNat 1726 := by rfl
def inline18Physical : PairedAllInlineCoreTrace.CoreBlock 1673 1726 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline18Template
  eval := PairedAllInlineCoreTrace.inline18Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline18Template_word s (UInt256.ofNat 1673) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline18_pcAfter] at h
    exact h

theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1272).take inline18Physical.code.length = inline18Physical.code := by rfl
def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline18Physical.code :=
  StackSiteBuilder.ofSlice inline18Physical.code 1272 inline18_slice
    (by change 1272 + inline18Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline18Physical.code) (by decide))
    (by decide)
theorem inline18_pc : inline18Site.startPC = UInt256.ofNat 1681 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1272) = UInt256.ofNat 1673
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline18_advances : ∀ instruction ∈ inline18Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline18Gas : PairedAllInlineCoreTrace.CoreGasBlock inline18Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline18Physical inline18Site inline18_pc inline18_advances
theorem inline19_pcAfter : pcAfter (UInt256.ofNat 1726) PairedAllInlineCoreTrace.inline19Template = UInt256.ofNat 1778 := by rfl
def inline19Physical : PairedAllInlineCoreTrace.CoreBlock 1726 1778 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline19Template
  eval := PairedAllInlineCoreTrace.inline19Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline19Template_word s (UInt256.ofNat 1726) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline19_pcAfter] at h
    exact h

theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1318).take inline19Physical.code.length = inline19Physical.code := by rfl
def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline19Physical.code :=
  StackSiteBuilder.ofSlice inline19Physical.code 1318 inline19_slice
    (by change 1318 + inline19Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline19Physical.code) (by decide))
    (by decide)
theorem inline19_pc : inline19Site.startPC = UInt256.ofNat 1734 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1318) = UInt256.ofNat 1726
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline19_advances : ∀ instruction ∈ inline19Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline19Gas : PairedAllInlineCoreTrace.CoreGasBlock inline19Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline19Physical inline19Site inline19_pc inline19_advances
theorem inline20_pcAfter : pcAfter (UInt256.ofNat 1778) PairedAllInlineCoreTrace.inline20Template = UInt256.ofNat 1827 := by rfl
def inline20Physical : PairedAllInlineCoreTrace.CoreBlock 1778 1827 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline20Template
  eval := PairedAllInlineCoreTrace.inline20Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline20Template_word s (UInt256.ofNat 1778) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline20_pcAfter] at h
    exact h

theorem inline20_slice :
    (Artifact.submissionArtifact.instructions.drop 1364).take inline20Physical.code.length = inline20Physical.code := by rfl
def inline20Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline20Physical.code :=
  StackSiteBuilder.ofSlice inline20Physical.code 1364 inline20_slice
    (by change 1364 + inline20Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline20Physical.code) (by decide))
    (by decide)
theorem inline20_pc : inline20Site.startPC = UInt256.ofNat 1786 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1364) = UInt256.ofNat 1778
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline20_advances : ∀ instruction ∈ inline20Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline20Gas : PairedAllInlineCoreTrace.CoreGasBlock inline20Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline20Physical inline20Site inline20_pc inline20_advances
theorem inline21_pcAfter : pcAfter (UInt256.ofNat 1827) PairedAllInlineCoreTrace.inline21Template = UInt256.ofNat 1877 := by rfl
def inline21Physical : PairedAllInlineCoreTrace.CoreBlock 1827 1877 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline21Template
  eval := PairedAllInlineCoreTrace.inline21Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline21Template_word s (UInt256.ofNat 1827) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline21_pcAfter] at h
    exact h

theorem inline21_slice :
    (Artifact.submissionArtifact.instructions.drop 1408).take inline21Physical.code.length = inline21Physical.code := by rfl
def inline21Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline21Physical.code :=
  StackSiteBuilder.ofSlice inline21Physical.code 1408 inline21_slice
    (by change 1408 + inline21Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline21Physical.code) (by decide))
    (by decide)
theorem inline21_pc : inline21Site.startPC = UInt256.ofNat 1835 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1408) = UInt256.ofNat 1827
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline21_advances : ∀ instruction ∈ inline21Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline21Gas : PairedAllInlineCoreTrace.CoreGasBlock inline21Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline21Physical inline21Site inline21_pc inline21_advances
theorem inline22_pcAfter : pcAfter (UInt256.ofNat 1877) PairedAllInlineCoreTrace.inline22Template = UInt256.ofNat 1930 := by rfl
def inline22Physical : PairedAllInlineCoreTrace.CoreBlock 1877 1930 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline22Template
  eval := PairedAllInlineCoreTrace.inline22Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline22Template_word s (UInt256.ofNat 1877) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline22_pcAfter] at h
    exact h

theorem inline22_slice :
    (Artifact.submissionArtifact.instructions.drop 1452).take inline22Physical.code.length = inline22Physical.code := by rfl
def inline22Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline22Physical.code :=
  StackSiteBuilder.ofSlice inline22Physical.code 1452 inline22_slice
    (by change 1452 + inline22Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline22Physical.code) (by decide))
    (by decide)
theorem inline22_pc : inline22Site.startPC = UInt256.ofNat 1885 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1452) = UInt256.ofNat 1877
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline22_advances : ∀ instruction ∈ inline22Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline22Gas : PairedAllInlineCoreTrace.CoreGasBlock inline22Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline22Physical inline22Site inline22_pc inline22_advances
theorem inline23_pcAfter : pcAfter (UInt256.ofNat 1930) PairedAllInlineCoreTrace.inline23Template = UInt256.ofNat 1983 := by rfl
def inline23Physical : PairedAllInlineCoreTrace.CoreBlock 1930 1983 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline23Template
  eval := PairedAllInlineCoreTrace.inline23Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline23Template_word s (UInt256.ofNat 1930) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline23_pcAfter] at h
    exact h

theorem inline23_slice :
    (Artifact.submissionArtifact.instructions.drop 1498).take inline23Physical.code.length = inline23Physical.code := by rfl
def inline23Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline23Physical.code :=
  StackSiteBuilder.ofSlice inline23Physical.code 1498 inline23_slice
    (by change 1498 + inline23Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline23Physical.code) (by decide))
    (by decide)
theorem inline23_pc : inline23Site.startPC = UInt256.ofNat 1938 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1498) = UInt256.ofNat 1930
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline23_advances : ∀ instruction ∈ inline23Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline23Gas : PairedAllInlineCoreTrace.CoreGasBlock inline23Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline23Physical inline23Site inline23_pc inline23_advances
theorem inline24_pcAfter : pcAfter (UInt256.ofNat 1983) PairedAllInlineCoreTrace.inline24Template = UInt256.ofNat 2029 := by rfl
def inline24Physical : PairedAllInlineCoreTrace.CoreBlock 1983 2029 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline24Template
  eval := PairedAllInlineCoreTrace.inline24Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline24Template_word s (UInt256.ofNat 1983) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline24_pcAfter] at h
    exact h

theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1544).take inline24Physical.code.length = inline24Physical.code := by rfl
def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline24Physical.code :=
  StackSiteBuilder.ofSlice inline24Physical.code 1544 inline24_slice
    (by change 1544 + inline24Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline24Physical.code) (by decide))
    (by decide)
theorem inline24_pc : inline24Site.startPC = UInt256.ofNat 1991 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1544) = UInt256.ofNat 1983
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline24_advances : ∀ instruction ∈ inline24Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline24Gas : PairedAllInlineCoreTrace.CoreGasBlock inline24Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline24Physical inline24Site inline24_pc inline24_advances
theorem inline25_pcAfter : pcAfter (UInt256.ofNat 2029) PairedAllInlineCoreTrace.inline25Template = UInt256.ofNat 2081 := by rfl
def inline25Physical : PairedAllInlineCoreTrace.CoreBlock 2029 2081 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline25Template
  eval := PairedAllInlineCoreTrace.inline25Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline25Template_word s (UInt256.ofNat 2029) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline25_pcAfter] at h
    exact h

theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1584).take inline25Physical.code.length = inline25Physical.code := by rfl
def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline25Physical.code :=
  StackSiteBuilder.ofSlice inline25Physical.code 1584 inline25_slice
    (by change 1584 + inline25Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline25Physical.code) (by decide))
    (by decide)
theorem inline25_pc : inline25Site.startPC = UInt256.ofNat 2037 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1584) = UInt256.ofNat 2029
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline25_advances : ∀ instruction ∈ inline25Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline25Gas : PairedAllInlineCoreTrace.CoreGasBlock inline25Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline25Physical inline25Site inline25_pc inline25_advances
theorem inline26_pcAfter : pcAfter (UInt256.ofNat 2081) PairedAllInlineCoreTrace.inline26Template = UInt256.ofNat 2134 := by rfl
def inline26Physical : PairedAllInlineCoreTrace.CoreBlock 2081 2134 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline26Template
  eval := PairedAllInlineCoreTrace.inline26Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline26Template_word s (UInt256.ofNat 2081) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline26_pcAfter] at h
    exact h

theorem inline26_slice :
    (Artifact.submissionArtifact.instructions.drop 1630).take inline26Physical.code.length = inline26Physical.code := by rfl
def inline26Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline26Physical.code :=
  StackSiteBuilder.ofSlice inline26Physical.code 1630 inline26_slice
    (by change 1630 + inline26Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline26Physical.code) (by decide))
    (by decide)
theorem inline26_pc : inline26Site.startPC = UInt256.ofNat 2089 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1630) = UInt256.ofNat 2081
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline26_advances : ∀ instruction ∈ inline26Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline26Gas : PairedAllInlineCoreTrace.CoreGasBlock inline26Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline26Physical inline26Site inline26_pc inline26_advances
theorem inline27_pcAfter : pcAfter (UInt256.ofNat 2134) PairedAllInlineCoreTrace.inline27Template = UInt256.ofNat 2187 := by rfl
def inline27Physical : PairedAllInlineCoreTrace.CoreBlock 2134 2187 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline27Template
  eval := PairedAllInlineCoreTrace.inline27Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline27Template_word s (UInt256.ofNat 2134) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline27_pcAfter] at h
    exact h

theorem inline27_slice :
    (Artifact.submissionArtifact.instructions.drop 1676).take inline27Physical.code.length = inline27Physical.code := by rfl
def inline27Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline27Physical.code :=
  StackSiteBuilder.ofSlice inline27Physical.code 1676 inline27_slice
    (by change 1676 + inline27Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline27Physical.code) (by decide))
    (by decide)
theorem inline27_pc : inline27Site.startPC = UInt256.ofNat 2142 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1676) = UInt256.ofNat 2134
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline27_advances : ∀ instruction ∈ inline27Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline27Gas : PairedAllInlineCoreTrace.CoreGasBlock inline27Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline27Physical inline27Site inline27_pc inline27_advances
theorem inline28_pcAfter : pcAfter (UInt256.ofNat 2187) PairedAllInlineNewPairs.inline28Template = UInt256.ofNat 2240 := by rfl
def inline28Physical : PairedAllInlineCoreTrace.CoreBlock 2187 2240 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline28Template
  eval := PairedAllInlineCoreTrace.inline28Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline28Template_word s (UInt256.ofNat 2187) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline28_pcAfter] at h
    exact h

theorem inline28_slice :
    (Artifact.submissionArtifact.instructions.drop 1722).take inline28Physical.code.length = inline28Physical.code := by rfl
def inline28Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline28Physical.code :=
  StackSiteBuilder.ofSlice inline28Physical.code 1722 inline28_slice
    (by change 1722 + inline28Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline28Physical.code) (by decide))
    (by decide)
theorem inline28_pc : inline28Site.startPC = UInt256.ofNat 2195 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1722) = UInt256.ofNat 2187
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline28_advances : ∀ instruction ∈ inline28Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline28Gas : PairedAllInlineCoreTrace.CoreGasBlock inline28Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline28Physical inline28Site inline28_pc inline28_advances
theorem inline29_pcAfter : pcAfter (UInt256.ofNat 2240) PairedAllInlineNewPairs.inline29Template = UInt256.ofNat 2293 := by rfl
def inline29Physical : PairedAllInlineCoreTrace.CoreBlock 2240 2293 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline29Template
  eval := PairedAllInlineCoreTrace.inline29Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline29Template_word s (UInt256.ofNat 2240) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline29_pcAfter] at h
    exact h

theorem inline29_slice :
    (Artifact.submissionArtifact.instructions.drop 1768).take inline29Physical.code.length = inline29Physical.code := by rfl
def inline29Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline29Physical.code :=
  StackSiteBuilder.ofSlice inline29Physical.code 1768 inline29_slice
    (by change 1768 + inline29Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline29Physical.code) (by decide))
    (by decide)
theorem inline29_pc : inline29Site.startPC = UInt256.ofNat 2248 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1768) = UInt256.ofNat 2240
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline29_advances : ∀ instruction ∈ inline29Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline29Gas : PairedAllInlineCoreTrace.CoreGasBlock inline29Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline29Physical inline29Site inline29_pc inline29_advances
theorem inline30_pcAfter : pcAfter (UInt256.ofNat 2293) PairedAllInlineCoreTrace.inline30Template = UInt256.ofNat 2338 := by rfl
def inline30Physical : PairedAllInlineCoreTrace.CoreBlock 2293 2338 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline30Template
  eval := PairedAllInlineCoreTrace.inline30Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline30Template_word s (UInt256.ofNat 2293) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline30_pcAfter] at h
    exact h

theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1814).take inline30Physical.code.length = inline30Physical.code := by rfl
def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline30Physical.code :=
  StackSiteBuilder.ofSlice inline30Physical.code 1814 inline30_slice
    (by change 1814 + inline30Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline30Physical.code) (by decide))
    (by decide)
theorem inline30_pc : inline30Site.startPC = UInt256.ofNat 2301 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1814) = UInt256.ofNat 2293
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline30_advances : ∀ instruction ∈ inline30Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline30Gas : PairedAllInlineCoreTrace.CoreGasBlock inline30Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline30Physical inline30Site inline30_pc inline30_advances
theorem inline31_pcAfter : pcAfter (UInt256.ofNat 2338) PairedAllInlineCoreTrace.inline31Template = UInt256.ofNat 2388 := by rfl
def inline31Physical : PairedAllInlineCoreTrace.CoreBlock 2338 2388 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline31Template
  eval := PairedAllInlineCoreTrace.inline31Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline31Template_word s (UInt256.ofNat 2338) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline31_pcAfter] at h
    exact h

theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1854).take inline31Physical.code.length = inline31Physical.code := by rfl
def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline31Physical.code :=
  StackSiteBuilder.ofSlice inline31Physical.code 1854 inline31_slice
    (by change 1854 + inline31Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline31Physical.code) (by decide))
    (by decide)
theorem inline31_pc : inline31Site.startPC = UInt256.ofNat 2346 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1854) = UInt256.ofNat 2338
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline31_advances : ∀ instruction ∈ inline31Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline31Gas : PairedAllInlineCoreTrace.CoreGasBlock inline31Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline31Physical inline31Site inline31_pc inline31_advances
theorem group32_pcAfter : pcAfter (UInt256.ofNat 2388) PairedAllInlineCoreTrace.group32Template = UInt256.ofNat 2412 := by rfl
def group32Physical : PairedAllInlineCoreTrace.CoreBlock 2388 2412 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group32Template
  eval := PairedAllInlineCoreTrace.group32Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group32Template s (UInt256.ofNat 2388) f.frame rho hstack hrun
    rw [group32_pcAfter] at h
    exact h

theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1898).take group32Physical.code.length = group32Physical.code := by rfl
def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka group32Physical.code :=
  StackSiteBuilder.ofSlice group32Physical.code 1898 group32_slice
    (by change 1898 + group32Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group32Physical.code) (by decide))
    (by decide)
theorem group32_pc : group32Site.startPC = UInt256.ofNat 2396 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1898) = UInt256.ofNat 2388
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group32_advances : ∀ instruction ∈ group32Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group32Gas : PairedAllInlineCoreTrace.CoreGasBlock group32Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group32Physical group32Site group32_pc group32_advances
theorem inline32_pcAfter : pcAfter (UInt256.ofNat 2412) PairedAllInlineCoreTrace.inline32Template = UInt256.ofNat 2458 := by rfl
def inline32Physical : PairedAllInlineCoreTrace.CoreBlock 2412 2458 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline32Template
  eval := PairedAllInlineCoreTrace.inline32Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline32Template_word s (UInt256.ofNat 2412) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline32_pcAfter] at h
    exact h

theorem inline32_slice :
    (Artifact.submissionArtifact.instructions.drop 1901).take inline32Physical.code.length = inline32Physical.code := by rfl
def inline32Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline32Physical.code :=
  StackSiteBuilder.ofSlice inline32Physical.code 1901 inline32_slice
    (by change 1901 + inline32Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline32Physical.code) (by decide))
    (by decide)
theorem inline32_pc : inline32Site.startPC = UInt256.ofNat 2420 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1901) = UInt256.ofNat 2412
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline32_advances : ∀ instruction ∈ inline32Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline32Gas : PairedAllInlineCoreTrace.CoreGasBlock inline32Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline32Physical inline32Site inline32_pc inline32_advances
theorem inline33_pcAfter : pcAfter (UInt256.ofNat 2458) PairedAllInlineCoreTrace.inline33Template = UInt256.ofNat 2504 := by rfl
def inline33Physical : PairedAllInlineCoreTrace.CoreBlock 2458 2504 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline33Template
  eval := PairedAllInlineCoreTrace.inline33Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline33Template_word s (UInt256.ofNat 2458) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline33_pcAfter] at h
    exact h

theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 1940).take inline33Physical.code.length = inline33Physical.code := by rfl
def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline33Physical.code :=
  StackSiteBuilder.ofSlice inline33Physical.code 1940 inline33_slice
    (by change 1940 + inline33Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline33Physical.code) (by decide))
    (by decide)
theorem inline33_pc : inline33Site.startPC = UInt256.ofNat 2466 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1940) = UInt256.ofNat 2458
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline33_advances : ∀ instruction ∈ inline33Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline33Gas : PairedAllInlineCoreTrace.CoreGasBlock inline33Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline33Physical inline33Site inline33_pc inline33_advances
theorem inline34_pcAfter : pcAfter (UInt256.ofNat 2504) PairedAllInlineCoreTrace.inline34Template = UInt256.ofNat 2550 := by rfl
def inline34Physical : PairedAllInlineCoreTrace.CoreBlock 2504 2550 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline34Template
  eval := PairedAllInlineCoreTrace.inline34Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline34Template_word s (UInt256.ofNat 2504) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline34_pcAfter] at h
    exact h

theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 1979).take inline34Physical.code.length = inline34Physical.code := by rfl
def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline34Physical.code :=
  StackSiteBuilder.ofSlice inline34Physical.code 1979 inline34_slice
    (by change 1979 + inline34Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline34Physical.code) (by decide))
    (by decide)
theorem inline34_pc : inline34Site.startPC = UInt256.ofNat 2512 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1979) = UInt256.ofNat 2504
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline34_advances : ∀ instruction ∈ inline34Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline34Gas : PairedAllInlineCoreTrace.CoreGasBlock inline34Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline34Physical inline34Site inline34_pc inline34_advances
theorem inline35_pcAfter : pcAfter (UInt256.ofNat 2550) PairedAllInlineCoreTrace.inline35Template = UInt256.ofNat 2596 := by rfl
def inline35Physical : PairedAllInlineCoreTrace.CoreBlock 2550 2596 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline35Template
  eval := PairedAllInlineCoreTrace.inline35Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline35Template_word s (UInt256.ofNat 2550) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline35_pcAfter] at h
    exact h

theorem inline35_slice :
    (Artifact.submissionArtifact.instructions.drop 2018).take inline35Physical.code.length = inline35Physical.code := by rfl
def inline35Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline35Physical.code :=
  StackSiteBuilder.ofSlice inline35Physical.code 2018 inline35_slice
    (by change 2018 + inline35Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline35Physical.code) (by decide))
    (by decide)
theorem inline35_pc : inline35Site.startPC = UInt256.ofNat 2558 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2018) = UInt256.ofNat 2550
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline35_advances : ∀ instruction ∈ inline35Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline35Gas : PairedAllInlineCoreTrace.CoreGasBlock inline35Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline35Physical inline35Site inline35_pc inline35_advances
theorem inline36_pcAfter : pcAfter (UInt256.ofNat 2596) PairedAllInlineCoreTrace.inline36Template = UInt256.ofNat 2642 := by rfl
def inline36Physical : PairedAllInlineCoreTrace.CoreBlock 2596 2642 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline36Template
  eval := PairedAllInlineCoreTrace.inline36Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline36Template_word s (UInt256.ofNat 2596) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline36_pcAfter] at h
    exact h

theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 2057).take inline36Physical.code.length = inline36Physical.code := by rfl
def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline36Physical.code :=
  StackSiteBuilder.ofSlice inline36Physical.code 2057 inline36_slice
    (by change 2057 + inline36Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline36Physical.code) (by decide))
    (by decide)
theorem inline36_pc : inline36Site.startPC = UInt256.ofNat 2604 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2057) = UInt256.ofNat 2596
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline36_advances : ∀ instruction ∈ inline36Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline36Gas : PairedAllInlineCoreTrace.CoreGasBlock inline36Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline36Physical inline36Site inline36_pc inline36_advances
theorem inline37_pcAfter : pcAfter (UInt256.ofNat 2642) PairedAllInlineCoreTrace.inline37Template = UInt256.ofNat 2688 := by rfl
def inline37Physical : PairedAllInlineCoreTrace.CoreBlock 2642 2688 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline37Template
  eval := PairedAllInlineCoreTrace.inline37Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline37Template_word s (UInt256.ofNat 2642) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline37_pcAfter] at h
    exact h

theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 2096).take inline37Physical.code.length = inline37Physical.code := by rfl
def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline37Physical.code :=
  StackSiteBuilder.ofSlice inline37Physical.code 2096 inline37_slice
    (by change 2096 + inline37Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline37Physical.code) (by decide))
    (by decide)
theorem inline37_pc : inline37Site.startPC = UInt256.ofNat 2650 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2096) = UInt256.ofNat 2642
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline37_advances : ∀ instruction ∈ inline37Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline37Gas : PairedAllInlineCoreTrace.CoreGasBlock inline37Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline37Physical inline37Site inline37_pc inline37_advances
theorem inline38_pcAfter : pcAfter (UInt256.ofNat 2688) PairedAllInlineCoreTrace.inline38Template = UInt256.ofNat 2734 := by rfl
def inline38Physical : PairedAllInlineCoreTrace.CoreBlock 2688 2734 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline38Template
  eval := PairedAllInlineCoreTrace.inline38Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline38Template_word s (UInt256.ofNat 2688) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline38_pcAfter] at h
    exact h

theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 2135).take inline38Physical.code.length = inline38Physical.code := by rfl
def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline38Physical.code :=
  StackSiteBuilder.ofSlice inline38Physical.code 2135 inline38_slice
    (by change 2135 + inline38Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline38Physical.code) (by decide))
    (by decide)
theorem inline38_pc : inline38Site.startPC = UInt256.ofNat 2696 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2135) = UInt256.ofNat 2688
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline38_advances : ∀ instruction ∈ inline38Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline38Gas : PairedAllInlineCoreTrace.CoreGasBlock inline38Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline38Physical inline38Site inline38_pc inline38_advances
theorem inline39_pcAfter : pcAfter (UInt256.ofNat 2734) PairedAllInlineCoreTrace.inline39Template = UInt256.ofNat 2776 := by rfl
def inline39Physical : PairedAllInlineCoreTrace.CoreBlock 2734 2776 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline39Template
  eval := PairedAllInlineCoreTrace.inline39Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline39Template_word s (UInt256.ofNat 2734) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline39_pcAfter] at h
    exact h

theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 2174).take inline39Physical.code.length = inline39Physical.code := by rfl
def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline39Physical.code :=
  StackSiteBuilder.ofSlice inline39Physical.code 2174 inline39_slice
    (by change 2174 + inline39Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline39Physical.code) (by decide))
    (by decide)
theorem inline39_pc : inline39Site.startPC = UInt256.ofNat 2742 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2174) = UInt256.ofNat 2734
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline39_advances : ∀ instruction ∈ inline39Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline39Gas : PairedAllInlineCoreTrace.CoreGasBlock inline39Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline39Physical inline39Site inline39_pc inline39_advances
theorem inline40_pcAfter : pcAfter (UInt256.ofNat 2776) PairedAllInlineCoreTrace.inline40Template = UInt256.ofNat 2822 := by rfl
def inline40Physical : PairedAllInlineCoreTrace.CoreBlock 2776 2822 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline40Template
  eval := PairedAllInlineCoreTrace.inline40Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline40Template_word s (UInt256.ofNat 2776) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline40_pcAfter] at h
    exact h

theorem inline40_slice :
    (Artifact.submissionArtifact.instructions.drop 2211).take inline40Physical.code.length = inline40Physical.code := by rfl
def inline40Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline40Physical.code :=
  StackSiteBuilder.ofSlice inline40Physical.code 2211 inline40_slice
    (by change 2211 + inline40Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline40Physical.code) (by decide))
    (by decide)
theorem inline40_pc : inline40Site.startPC = UInt256.ofNat 2784 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2211) = UInt256.ofNat 2776
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline40_advances : ∀ instruction ∈ inline40Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline40Gas : PairedAllInlineCoreTrace.CoreGasBlock inline40Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline40Physical inline40Site inline40_pc inline40_advances
theorem inline41_pcAfter : pcAfter (UInt256.ofNat 2822) PairedAllInlineCoreTrace.inline41Template = UInt256.ofNat 2868 := by rfl
def inline41Physical : PairedAllInlineCoreTrace.CoreBlock 2822 2868 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline41Template
  eval := PairedAllInlineCoreTrace.inline41Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline41Template_word s (UInt256.ofNat 2822) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline41_pcAfter] at h
    exact h

theorem inline41_slice :
    (Artifact.submissionArtifact.instructions.drop 2250).take inline41Physical.code.length = inline41Physical.code := by rfl
def inline41Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline41Physical.code :=
  StackSiteBuilder.ofSlice inline41Physical.code 2250 inline41_slice
    (by change 2250 + inline41Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline41Physical.code) (by decide))
    (by decide)
theorem inline41_pc : inline41Site.startPC = UInt256.ofNat 2830 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2250) = UInt256.ofNat 2822
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline41_advances : ∀ instruction ∈ inline41Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline41Gas : PairedAllInlineCoreTrace.CoreGasBlock inline41Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline41Physical inline41Site inline41_pc inline41_advances
theorem inline42_pcAfter : pcAfter (UInt256.ofNat 2868) PairedAllInlineCoreTrace.inline42Template = UInt256.ofNat 2913 := by rfl
def inline42Physical : PairedAllInlineCoreTrace.CoreBlock 2868 2913 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline42Template
  eval := PairedAllInlineCoreTrace.inline42Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline42Template_word s (UInt256.ofNat 2868) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline42_pcAfter] at h
    exact h

theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2289).take inline42Physical.code.length = inline42Physical.code := by rfl
def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline42Physical.code :=
  StackSiteBuilder.ofSlice inline42Physical.code 2289 inline42_slice
    (by change 2289 + inline42Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline42Physical.code) (by decide))
    (by decide)
theorem inline42_pc : inline42Site.startPC = UInt256.ofNat 2876 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2289) = UInt256.ofNat 2868
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline42_advances : ∀ instruction ∈ inline42Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline42Gas : PairedAllInlineCoreTrace.CoreGasBlock inline42Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline42Physical inline42Site inline42_pc inline42_advances
theorem inline43_pcAfter : pcAfter (UInt256.ofNat 2913) PairedAllInlineCoreTrace.inline43Template = UInt256.ofNat 2959 := by rfl
def inline43Physical : PairedAllInlineCoreTrace.CoreBlock 2913 2959 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline43Template
  eval := PairedAllInlineCoreTrace.inline43Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline43Template_word s (UInt256.ofNat 2913) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline43_pcAfter] at h
    exact h

theorem inline43_slice :
    (Artifact.submissionArtifact.instructions.drop 2328).take inline43Physical.code.length = inline43Physical.code := by rfl
def inline43Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline43Physical.code :=
  StackSiteBuilder.ofSlice inline43Physical.code 2328 inline43_slice
    (by change 2328 + inline43Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline43Physical.code) (by decide))
    (by decide)
theorem inline43_pc : inline43Site.startPC = UInt256.ofNat 2921 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2328) = UInt256.ofNat 2913
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline43_advances : ∀ instruction ∈ inline43Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline43Gas : PairedAllInlineCoreTrace.CoreGasBlock inline43Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline43Physical inline43Site inline43_pc inline43_advances
theorem inline44_pcAfter : pcAfter (UInt256.ofNat 2959) PairedAllInlineCoreTrace.inline44Template = UInt256.ofNat 3005 := by rfl
def inline44Physical : PairedAllInlineCoreTrace.CoreBlock 2959 3005 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline44Template
  eval := PairedAllInlineCoreTrace.inline44Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline44Template_word s (UInt256.ofNat 2959) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline44_pcAfter] at h
    exact h

theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2367).take inline44Physical.code.length = inline44Physical.code := by rfl
def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline44Physical.code :=
  StackSiteBuilder.ofSlice inline44Physical.code 2367 inline44_slice
    (by change 2367 + inline44Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline44Physical.code) (by decide))
    (by decide)
theorem inline44_pc : inline44Site.startPC = UInt256.ofNat 2967 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2367) = UInt256.ofNat 2959
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline44_advances : ∀ instruction ∈ inline44Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline44Gas : PairedAllInlineCoreTrace.CoreGasBlock inline44Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline44Physical inline44Site inline44_pc inline44_advances
theorem inline45_pcAfter : pcAfter (UInt256.ofNat 3005) PairedAllInlineCoreTrace.inline45Template = UInt256.ofNat 3047 := by rfl
def inline45Physical : PairedAllInlineCoreTrace.CoreBlock 3005 3047 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline45Template
  eval := PairedAllInlineCoreTrace.inline45Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline45Template_word s (UInt256.ofNat 3005) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline45_pcAfter] at h
    exact h

theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2406).take inline45Physical.code.length = inline45Physical.code := by rfl
def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline45Physical.code :=
  StackSiteBuilder.ofSlice inline45Physical.code 2406 inline45_slice
    (by change 2406 + inline45Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline45Physical.code) (by decide))
    (by decide)
theorem inline45_pc : inline45Site.startPC = UInt256.ofNat 3013 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2406) = UInt256.ofNat 3005
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline45_advances : ∀ instruction ∈ inline45Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline45Gas : PairedAllInlineCoreTrace.CoreGasBlock inline45Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline45Physical inline45Site inline45_pc inline45_advances
theorem inline46_pcAfter : pcAfter (UInt256.ofNat 3047) PairedAllInlineCoreTrace.inline46Template = UInt256.ofNat 3086 := by rfl
def inline46Physical : PairedAllInlineCoreTrace.CoreBlock 3047 3086 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline46Template
  eval := PairedAllInlineCoreTrace.inline46Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline46Template_word s (UInt256.ofNat 3047) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline46_pcAfter] at h
    exact h

theorem inline46_slice :
    (Artifact.submissionArtifact.instructions.drop 2443).take inline46Physical.code.length = inline46Physical.code := by rfl
def inline46Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline46Physical.code :=
  StackSiteBuilder.ofSlice inline46Physical.code 2443 inline46_slice
    (by change 2443 + inline46Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline46Physical.code) (by decide))
    (by decide)
theorem inline46_pc : inline46Site.startPC = UInt256.ofNat 3055 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2443) = UInt256.ofNat 3047
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline46_advances : ∀ instruction ∈ inline46Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline46Gas : PairedAllInlineCoreTrace.CoreGasBlock inline46Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline46Physical inline46Site inline46_pc inline46_advances
theorem inline47_pcAfter : pcAfter (UInt256.ofNat 3086) PairedAllInlineCoreTrace.inline47Template = UInt256.ofNat 3125 := by rfl
def inline47Physical : PairedAllInlineCoreTrace.CoreBlock 3086 3125 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline47Template
  eval := PairedAllInlineCoreTrace.inline47Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline47Template_word s (UInt256.ofNat 3086) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline47_pcAfter] at h
    exact h

theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2476).take inline47Physical.code.length = inline47Physical.code := by rfl
def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline47Physical.code :=
  StackSiteBuilder.ofSlice inline47Physical.code 2476 inline47_slice
    (by change 2476 + inline47Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline47Physical.code) (by decide))
    (by decide)
theorem inline47_pc : inline47Site.startPC = UInt256.ofNat 3094 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2476) = UInt256.ofNat 3086
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline47_advances : ∀ instruction ∈ inline47Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline47Gas : PairedAllInlineCoreTrace.CoreGasBlock inline47Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline47Physical inline47Site inline47_pc inline47_advances
theorem group48_pcAfter : pcAfter (UInt256.ofNat 3125) PairedAllInlineCoreTrace.group48Template = UInt256.ofNat 3148 := by rfl
def group48Physical : PairedAllInlineCoreTrace.CoreBlock 3125 3148 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group48Template
  eval := PairedAllInlineCoreTrace.group48Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group48Template s (UInt256.ofNat 3125) f.frame rho hstack hrun
    rw [group48_pcAfter] at h
    exact h

theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2509).take group48Physical.code.length = group48Physical.code := by rfl
def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka group48Physical.code :=
  StackSiteBuilder.ofSlice group48Physical.code 2509 group48_slice
    (by change 2509 + group48Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group48Physical.code) (by decide))
    (by decide)
theorem group48_pc : group48Site.startPC = UInt256.ofNat 3133 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2509) = UInt256.ofNat 3125
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group48_advances : ∀ instruction ∈ group48Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group48Gas : PairedAllInlineCoreTrace.CoreGasBlock group48Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group48Physical group48Site group48_pc group48_advances
theorem group64_pcAfter : pcAfter (UInt256.ofNat 3828) PairedAllInlineCoreTrace.group64Template = UInt256.ofNat 3835 := by rfl
def group64Physical : PairedAllInlineCoreTrace.CoreBlock 3828 3835 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group64Template
  eval := PairedAllInlineCoreTrace.group64Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group64Template s (UInt256.ofNat 3828) f.frame rho hstack hrun
    rw [group64_pcAfter] at h
    exact h

theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3062).take group64Physical.code.length = group64Physical.code := by rfl
def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka group64Physical.code :=
  StackSiteBuilder.ofSlice group64Physical.code 3062 group64_slice
    (by change 3062 + group64Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group64Physical.code) (by decide))
    (by decide)
theorem group64_pc : group64Site.startPC = UInt256.ofNat 3836 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3062) = UInt256.ofNat 3828
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group64_advances : ∀ instruction ∈ group64Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group64Gas : PairedAllInlineCoreTrace.CoreGasBlock group64Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group64Physical group64Site group64_pc group64_advances
theorem inline64_pcAfter : pcAfter (UInt256.ofNat 3835) PairedAllInlineCoreTrace.inline64Template = UInt256.ofNat 3883 := by rfl
def inline64Physical : PairedAllInlineCoreTrace.CoreBlock 3835 3883 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline64Template
  eval := PairedAllInlineCoreTrace.inline64Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline64Template_word s (UInt256.ofNat 3835) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline64_pcAfter] at h
    exact h

theorem inline64_slice :
    (Artifact.submissionArtifact.instructions.drop 3065).take inline64Physical.code.length = inline64Physical.code := by rfl
def inline64Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline64Physical.code :=
  StackSiteBuilder.ofSlice inline64Physical.code 3065 inline64_slice
    (by change 3065 + inline64Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline64Physical.code) (by decide))
    (by decide)
theorem inline64_pc : inline64Site.startPC = UInt256.ofNat 3843 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3065) = UInt256.ofNat 3835
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline64_advances : ∀ instruction ∈ inline64Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline64Gas : PairedAllInlineCoreTrace.CoreGasBlock inline64Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline64Physical inline64Site inline64_pc inline64_advances
theorem inline65_pcAfter : pcAfter (UInt256.ofNat 3883) PairedAllInlineCoreTrace.inline65Template = UInt256.ofNat 3934 := by rfl
def inline65Physical : PairedAllInlineCoreTrace.CoreBlock 3883 3934 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline65Template
  eval := PairedAllInlineCoreTrace.inline65Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline65Template_word s (UInt256.ofNat 3883) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline65_pcAfter] at h
    exact h

theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3107).take inline65Physical.code.length = inline65Physical.code := by rfl
def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline65Physical.code :=
  StackSiteBuilder.ofSlice inline65Physical.code 3107 inline65_slice
    (by change 3107 + inline65Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline65Physical.code) (by decide))
    (by decide)
theorem inline65_pc : inline65Site.startPC = UInt256.ofNat 3891 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3107) = UInt256.ofNat 3883
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline65_advances : ∀ instruction ∈ inline65Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline65Gas : PairedAllInlineCoreTrace.CoreGasBlock inline65Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline65Physical inline65Site inline65_pc inline65_advances
theorem inline66_pcAfter : pcAfter (UInt256.ofNat 3934) PairedAllInlineCoreTrace.inline66Template = UInt256.ofNat 3985 := by rfl
def inline66Physical : PairedAllInlineCoreTrace.CoreBlock 3934 3985 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline66Template
  eval := PairedAllInlineCoreTrace.inline66Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline66Template_word s (UInt256.ofNat 3934) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline66_pcAfter] at h
    exact h

theorem inline66_slice :
    (Artifact.submissionArtifact.instructions.drop 3151).take inline66Physical.code.length = inline66Physical.code := by rfl
def inline66Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline66Physical.code :=
  StackSiteBuilder.ofSlice inline66Physical.code 3151 inline66_slice
    (by change 3151 + inline66Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline66Physical.code) (by decide))
    (by decide)
theorem inline66_pc : inline66Site.startPC = UInt256.ofNat 3942 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3151) = UInt256.ofNat 3934
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline66_advances : ∀ instruction ∈ inline66Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline66Gas : PairedAllInlineCoreTrace.CoreGasBlock inline66Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline66Physical inline66Site inline66_pc inline66_advances
theorem inline67_pcAfter : pcAfter (UInt256.ofNat 3985) PairedAllInlineCoreTrace.inline67Template = UInt256.ofNat 4036 := by rfl
def inline67Physical : PairedAllInlineCoreTrace.CoreBlock 3985 4036 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline67Template
  eval := PairedAllInlineCoreTrace.inline67Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline67Template_word s (UInt256.ofNat 3985) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline67_pcAfter] at h
    exact h

theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3195).take inline67Physical.code.length = inline67Physical.code := by rfl
def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline67Physical.code :=
  StackSiteBuilder.ofSlice inline67Physical.code 3195 inline67_slice
    (by change 3195 + inline67Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline67Physical.code) (by decide))
    (by decide)
theorem inline67_pc : inline67Site.startPC = UInt256.ofNat 3993 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3195) = UInt256.ofNat 3985
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline67_advances : ∀ instruction ∈ inline67Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline67Gas : PairedAllInlineCoreTrace.CoreGasBlock inline67Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline67Physical inline67Site inline67_pc inline67_advances
theorem inline68_pcAfter : pcAfter (UInt256.ofNat 4036) PairedAllInlineCoreTrace.inline68Template = UInt256.ofNat 4086 := by rfl
def inline68Physical : PairedAllInlineCoreTrace.CoreBlock 4036 4086 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline68Template
  eval := PairedAllInlineCoreTrace.inline68Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline68Template_word s (UInt256.ofNat 4036) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline68_pcAfter] at h
    exact h

theorem inline68_slice :
    (Artifact.submissionArtifact.instructions.drop 3239).take inline68Physical.code.length = inline68Physical.code := by rfl
def inline68Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline68Physical.code :=
  StackSiteBuilder.ofSlice inline68Physical.code 3239 inline68_slice
    (by change 3239 + inline68Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline68Physical.code) (by decide))
    (by decide)
theorem inline68_pc : inline68Site.startPC = UInt256.ofNat 4044 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3239) = UInt256.ofNat 4036
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline68_advances : ∀ instruction ∈ inline68Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline68Gas : PairedAllInlineCoreTrace.CoreGasBlock inline68Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline68Physical inline68Site inline68_pc inline68_advances
theorem inline69_pcAfter : pcAfter (UInt256.ofNat 4086) PairedAllInlineCoreTrace.inline69Template = UInt256.ofNat 4137 := by rfl
def inline69Physical : PairedAllInlineCoreTrace.CoreBlock 4086 4137 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline69Template
  eval := PairedAllInlineCoreTrace.inline69Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline69Template_word s (UInt256.ofNat 4086) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline69_pcAfter] at h
    exact h

theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3283).take inline69Physical.code.length = inline69Physical.code := by rfl
def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline69Physical.code :=
  StackSiteBuilder.ofSlice inline69Physical.code 3283 inline69_slice
    (by change 3283 + inline69Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline69Physical.code) (by decide))
    (by decide)
theorem inline69_pc : inline69Site.startPC = UInt256.ofNat 4094 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3283) = UInt256.ofNat 4086
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline69_advances : ∀ instruction ∈ inline69Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline69Gas : PairedAllInlineCoreTrace.CoreGasBlock inline69Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline69Physical inline69Site inline69_pc inline69_advances
theorem inline70_pcAfter : pcAfter (UInt256.ofNat 4137) PairedAllInlineCoreTrace.inline70Template = UInt256.ofNat 4185 := by rfl
def inline70Physical : PairedAllInlineCoreTrace.CoreBlock 4137 4185 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline70Template
  eval := PairedAllInlineCoreTrace.inline70Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline70Template_word s (UInt256.ofNat 4137) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline70_pcAfter] at h
    exact h

theorem inline70_slice :
    (Artifact.submissionArtifact.instructions.drop 3327).take inline70Physical.code.length = inline70Physical.code := by rfl
def inline70Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline70Physical.code :=
  StackSiteBuilder.ofSlice inline70Physical.code 3327 inline70_slice
    (by change 3327 + inline70Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline70Physical.code) (by decide))
    (by decide)
theorem inline70_pc : inline70Site.startPC = UInt256.ofNat 4145 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3327) = UInt256.ofNat 4137
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline70_advances : ∀ instruction ∈ inline70Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline70Gas : PairedAllInlineCoreTrace.CoreGasBlock inline70Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline70Physical inline70Site inline70_pc inline70_advances
theorem inline71_pcAfter : pcAfter (UInt256.ofNat 4185) PairedAllInlineCoreTrace.inline71Template = UInt256.ofNat 4236 := by rfl
def inline71Physical : PairedAllInlineCoreTrace.CoreBlock 4185 4236 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline71Template
  eval := PairedAllInlineCoreTrace.inline71Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline71Template_word s (UInt256.ofNat 4185) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline71_pcAfter] at h
    exact h

theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3369).take inline71Physical.code.length = inline71Physical.code := by rfl
def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline71Physical.code :=
  StackSiteBuilder.ofSlice inline71Physical.code 3369 inline71_slice
    (by change 3369 + inline71Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline71Physical.code) (by decide))
    (by decide)
theorem inline71_pc : inline71Site.startPC = UInt256.ofNat 4193 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3369) = UInt256.ofNat 4185
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline71_advances : ∀ instruction ∈ inline71Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline71Gas : PairedAllInlineCoreTrace.CoreGasBlock inline71Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline71Physical inline71Site inline71_pc inline71_advances
theorem inline72_pcAfter : pcAfter (UInt256.ofNat 4236) PairedAllInlineCoreTrace.inline72Template = UInt256.ofNat 4287 := by rfl
def inline72Physical : PairedAllInlineCoreTrace.CoreBlock 4236 4287 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline72Template
  eval := PairedAllInlineCoreTrace.inline72Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline72Template_word s (UInt256.ofNat 4236) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline72_pcAfter] at h
    exact h

theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3413).take inline72Physical.code.length = inline72Physical.code := by rfl
def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline72Physical.code :=
  StackSiteBuilder.ofSlice inline72Physical.code 3413 inline72_slice
    (by change 3413 + inline72Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline72Physical.code) (by decide))
    (by decide)
theorem inline72_pc : inline72Site.startPC = UInt256.ofNat 4244 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3413) = UInt256.ofNat 4236
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline72_advances : ∀ instruction ∈ inline72Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline72Gas : PairedAllInlineCoreTrace.CoreGasBlock inline72Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline72Physical inline72Site inline72_pc inline72_advances
theorem inline73_pcAfter : pcAfter (UInt256.ofNat 4287) PairedAllInlineCoreTrace.inline73Template = UInt256.ofNat 4334 := by rfl
def inline73Physical : PairedAllInlineCoreTrace.CoreBlock 4287 4334 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline73Template
  eval := PairedAllInlineCoreTrace.inline73Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline73Template_word s (UInt256.ofNat 4287) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline73_pcAfter] at h
    exact h

theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3457).take inline73Physical.code.length = inline73Physical.code := by rfl
def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline73Physical.code :=
  StackSiteBuilder.ofSlice inline73Physical.code 3457 inline73_slice
    (by change 3457 + inline73Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline73Physical.code) (by decide))
    (by decide)
theorem inline73_pc : inline73Site.startPC = UInt256.ofNat 4295 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3457) = UInt256.ofNat 4287
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline73_advances : ∀ instruction ∈ inline73Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline73Gas : PairedAllInlineCoreTrace.CoreGasBlock inline73Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline73Physical inline73Site inline73_pc inline73_advances
theorem inline74_pcAfter : pcAfter (UInt256.ofNat 4334) PairedAllInlineCoreTrace.inline74Template = UInt256.ofNat 4385 := by rfl
def inline74Physical : PairedAllInlineCoreTrace.CoreBlock 4334 4385 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline74Template
  eval := PairedAllInlineCoreTrace.inline74Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline74Template_word s (UInt256.ofNat 4334) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline74_pcAfter] at h
    exact h

theorem inline74_slice :
    (Artifact.submissionArtifact.instructions.drop 3499).take inline74Physical.code.length = inline74Physical.code := by rfl
def inline74Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline74Physical.code :=
  StackSiteBuilder.ofSlice inline74Physical.code 3499 inline74_slice
    (by change 3499 + inline74Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline74Physical.code) (by decide))
    (by decide)
theorem inline74_pc : inline74Site.startPC = UInt256.ofNat 4342 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3499) = UInt256.ofNat 4334
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline74_advances : ∀ instruction ∈ inline74Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline74Gas : PairedAllInlineCoreTrace.CoreGasBlock inline74Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline74Physical inline74Site inline74_pc inline74_advances
theorem inline75_pcAfter : pcAfter (UInt256.ofNat 4385) PairedAllInlineCoreTrace.inline75Template = UInt256.ofNat 4437 := by rfl
def inline75Physical : PairedAllInlineCoreTrace.CoreBlock 4385 4437 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline75Template
  eval := PairedAllInlineCoreTrace.inline75Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline75Template_word s (UInt256.ofNat 4385) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline75_pcAfter] at h
    exact h

theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3543).take inline75Physical.code.length = inline75Physical.code := by rfl
def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline75Physical.code :=
  StackSiteBuilder.ofSlice inline75Physical.code 3543 inline75_slice
    (by change 3543 + inline75Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline75Physical.code) (by decide))
    (by decide)
theorem inline75_pc : inline75Site.startPC = UInt256.ofNat 4393 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3543) = UInt256.ofNat 4385
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline75_advances : ∀ instruction ∈ inline75Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline75Gas : PairedAllInlineCoreTrace.CoreGasBlock inline75Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline75Physical inline75Site inline75_pc inline75_advances
theorem inline76_pcAfter : pcAfter (UInt256.ofNat 4437) PairedAllInlineCoreTrace.inline76Template = UInt256.ofNat 4487 := by rfl
def inline76Physical : PairedAllInlineCoreTrace.CoreBlock 4437 4487 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline76Template
  eval := PairedAllInlineCoreTrace.inline76Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline76Template_word s (UInt256.ofNat 4437) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline76_pcAfter] at h
    exact h

theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3587).take inline76Physical.code.length = inline76Physical.code := by rfl
def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline76Physical.code :=
  StackSiteBuilder.ofSlice inline76Physical.code 3587 inline76_slice
    (by change 3587 + inline76Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline76Physical.code) (by decide))
    (by decide)
theorem inline76_pc : inline76Site.startPC = UInt256.ofNat 4445 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3587) = UInt256.ofNat 4437
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline76_advances : ∀ instruction ∈ inline76Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline76Gas : PairedAllInlineCoreTrace.CoreGasBlock inline76Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline76Physical inline76Site inline76_pc inline76_advances
theorem inline77_pcAfter : pcAfter (UInt256.ofNat 4487) PairedAllInlineCoreTrace.inline77Template = UInt256.ofNat 4538 := by rfl
def inline77Physical : PairedAllInlineCoreTrace.CoreBlock 4487 4538 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline77Template
  eval := PairedAllInlineCoreTrace.inline77Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline77Template_word s (UInt256.ofNat 4487) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline77_pcAfter] at h
    exact h

theorem inline77_slice :
    (Artifact.submissionArtifact.instructions.drop 3631).take inline77Physical.code.length = inline77Physical.code := by rfl
def inline77Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline77Physical.code :=
  StackSiteBuilder.ofSlice inline77Physical.code 3631 inline77_slice
    (by change 3631 + inline77Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline77Physical.code) (by decide))
    (by decide)
theorem inline77_pc : inline77Site.startPC = UInt256.ofNat 4495 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3631) = UInt256.ofNat 4487
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline77_advances : ∀ instruction ∈ inline77Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline77Gas : PairedAllInlineCoreTrace.CoreGasBlock inline77Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline77Physical inline77Site inline77_pc inline77_advances
theorem inline78_pcAfter : pcAfter (UInt256.ofNat 4538) PairedAllInlineCoreTrace.inline78Template = UInt256.ofNat 4589 := by rfl
def inline78Physical : PairedAllInlineCoreTrace.CoreBlock 4538 4589 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline78Template
  eval := PairedAllInlineCoreTrace.inline78Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline78Template_word s (UInt256.ofNat 4538) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline78_pcAfter] at h
    exact h

theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3675).take inline78Physical.code.length = inline78Physical.code := by rfl
def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline78Physical.code :=
  StackSiteBuilder.ofSlice inline78Physical.code 3675 inline78_slice
    (by change 3675 + inline78Physical.code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline78Physical.code) (by decide))
    (by decide)
theorem inline78_pc : inline78Site.startPC = UInt256.ofNat 4546 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3675) = UInt256.ofNat 4538
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline78_advances : ∀ instruction ∈ inline78Physical.code.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline78Gas : PairedAllInlineCoreTrace.CoreGasBlock inline78Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline78Physical inline78Site inline78_pc inline78_advances
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCoreStraight

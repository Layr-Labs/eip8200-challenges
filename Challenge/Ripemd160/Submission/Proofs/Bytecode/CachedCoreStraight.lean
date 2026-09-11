import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreStraight
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace PairedAllInlineCoreTrace CachedCoreCommon
theorem group0_pcAfter : pcAfter (UInt256.ofNat 893) PairedAllInlineCoreTrace.group0Template = UInt256.ofNat 901 := by rfl
def group0Physical : PairedAllInlineCoreTrace.CoreBlock 893 901 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group0Template
  eval := PairedAllInlineCoreTrace.group0Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group0Template s (UInt256.ofNat 893) f.frame rho hstack hrun
    rw [group0_pcAfter] at h
    exact h

def group0Template : List Instr :=
  [ .push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHL ]
theorem group0_slice :
    (Artifact.submissionArtifact.instructions.drop 575).take group0Template.length = group0Template := by rfl
def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka group0Template :=
  StackSiteBuilder.ofSlice group0Template 575 group0_slice
    (by change 575 + group0Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group0Template) (by decide))
    (by decide)
theorem group0_pc : group0Site.startPC = UInt256.ofNat 893 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 575) = UInt256.ofNat 893
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group0_advances : ∀ instruction ∈ group0Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group0Gas : PairedAllInlineCoreTrace.CoreGasBlock group0Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group0Physical group0Site group0_pc group0_advances
theorem inline0_pcAfter : pcAfter (UInt256.ofNat 901) PairedSynthCoreTrace.inline0Template = UInt256.ofNat 951 := by rfl
def inline0Physical : PairedAllInlineCoreTrace.CoreBlock 901 951 [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline0Template
  eval := PairedAllInlineCoreTrace.inline0Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline0Template_word s (UInt256.ofNat 901) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline0_pcAfter] at h
    exact h

def inline0Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 368),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline0_slice :
    (Artifact.submissionArtifact.instructions.drop 578).take inline0Template.length = inline0Template := by rfl
def inline0Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline0Template :=
  StackSiteBuilder.ofSlice inline0Template 578 inline0_slice
    (by change 578 + inline0Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline0Template) (by decide))
    (by decide)
theorem inline0_pc : inline0Site.startPC = UInt256.ofNat 901 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 578) = UInt256.ofNat 901
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline0_advances : ∀ instruction ∈ inline0Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline0Gas : PairedAllInlineCoreTrace.CoreGasBlock inline0Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline0Physical inline0Site inline0_pc inline0_advances
theorem inline1_pcAfter : pcAfter (UInt256.ofNat 951) PairedSynthCoreTrace.inline1Template = UInt256.ofNat 1001 := by rfl
def inline1Physical : PairedAllInlineCoreTrace.CoreBlock 951 1001 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline1Template
  eval := PairedAllInlineCoreTrace.inline1Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline1Template_word s (UInt256.ofNat 951) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline1_pcAfter] at h
    exact h

def inline1Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 656),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 31),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline1_slice :
    (Artifact.submissionArtifact.instructions.drop 622).take inline1Template.length = inline1Template := by rfl
def inline1Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline1Template :=
  StackSiteBuilder.ofSlice inline1Template 622 inline1_slice
    (by change 622 + inline1Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline1Template) (by decide))
    (by decide)
theorem inline1_pc : inline1Site.startPC = UInt256.ofNat 951 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 622) = UInt256.ofNat 951
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline1_advances : ∀ instruction ∈ inline1Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline1Gas : PairedAllInlineCoreTrace.CoreGasBlock inline1Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline1Physical inline1Site inline1_pc inline1_advances
theorem inline8_pcAfter : pcAfter (UInt256.ofNat 1285) PairedSynthCoreTrace.inline8Template = UInt256.ofNat 1336 := by rfl
def inline8Physical : PairedAllInlineCoreTrace.CoreBlock 1285 1336 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline8Template
  eval := PairedAllInlineCoreTrace.inline8Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline8Template_word s (UInt256.ofNat 1285) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline8_pcAfter] at h
    exact h

def inline8Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 448),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 624),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 15),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline8_slice :
    (Artifact.submissionArtifact.instructions.drop 922).take inline8Template.length = inline8Template := by rfl
def inline8Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline8Template :=
  StackSiteBuilder.ofSlice inline8Template 922 inline8_slice
    (by change 922 + inline8Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline8Template) (by decide))
    (by decide)
theorem inline8_pc : inline8Site.startPC = UInt256.ofNat 1285 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 922) = UInt256.ofNat 1285
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline8_advances : ∀ instruction ∈ inline8Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline8Gas : PairedAllInlineCoreTrace.CoreGasBlock inline8Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline8Physical inline8Site inline8_pc inline8_advances
theorem inline9_pcAfter : pcAfter (UInt256.ofNat 1336) PairedSynthCoreTrace.inline9Template = UInt256.ofNat 1387 := by rfl
def inline9Physical : PairedAllInlineCoreTrace.CoreBlock 1336 1387 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline9Template
  eval := PairedAllInlineCoreTrace.inline9Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline9Template_word s (UInt256.ofNat 1336) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline9_pcAfter] at h
    exact h

def inline9Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 480),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 400),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline9_slice :
    (Artifact.submissionArtifact.instructions.drop 966).take inline9Template.length = inline9Template := by rfl
def inline9Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline9Template :=
  StackSiteBuilder.ofSlice inline9Template 966 inline9_slice
    (by change 966 + inline9Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline9Template) (by decide))
    (by decide)
theorem inline9_pc : inline9Site.startPC = UInt256.ofNat 1336 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 966) = UInt256.ofNat 1336
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline9_advances : ∀ instruction ∈ inline9Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline9Gas : PairedAllInlineCoreTrace.CoreGasBlock inline9Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline9Physical inline9Site inline9_pc inline9_advances
theorem inline10_pcAfter : pcAfter (UInt256.ofNat 1387) PairedSynthCoreTrace.inline10Template = UInt256.ofNat 1438 := by rfl
def inline10Physical : PairedAllInlineCoreTrace.CoreBlock 1387 1438 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline10Template
  eval := PairedAllInlineCoreTrace.inline10Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline10Template_word s (UInt256.ofNat 1387) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline10_pcAfter] at h
    exact h

def inline10Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 512),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 688),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline10_slice :
    (Artifact.submissionArtifact.instructions.drop 1010).take inline10Template.length = inline10Template := by rfl
def inline10Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline10Template :=
  StackSiteBuilder.ofSlice inline10Template 1010 inline10_slice
    (by change 1010 + inline10Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline10Template) (by decide))
    (by decide)
theorem inline10_pc : inline10Site.startPC = UInt256.ofNat 1387 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1010) = UInt256.ofNat 1387
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline10_advances : ∀ instruction ∈ inline10Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline10Gas : PairedAllInlineCoreTrace.CoreGasBlock inline10Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline10Physical inline10Site inline10_pc inline10_advances
theorem inline11_pcAfter : pcAfter (UInt256.ofNat 1438) PairedSynthCoreTrace.inline11Template = UInt256.ofNat 1489 := by rfl
def inline11Physical : PairedAllInlineCoreTrace.CoreBlock 1438 1489 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline11Template
  eval := PairedAllInlineCoreTrace.inline11Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline11Template_word s (UInt256.ofNat 1438) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline11_pcAfter] at h
    exact h

def inline11Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 464),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 15),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 21),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline11_slice :
    (Artifact.submissionArtifact.instructions.drop 1054).take inline11Template.length = inline11Template := by rfl
def inline11Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline11Template :=
  StackSiteBuilder.ofSlice inline11Template 1054 inline11_slice
    (by change 1054 + inline11Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline11Template) (by decide))
    (by decide)
theorem inline11_pc : inline11Site.startPC = UInt256.ofNat 1438 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1054) = UInt256.ofNat 1438
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline11_advances : ∀ instruction ∈ inline11Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline11Gas : PairedAllInlineCoreTrace.CoreGasBlock inline11Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline11Physical inline11Site inline11_pc inline11_advances
theorem inline12_pcAfter : pcAfter (UInt256.ofNat 1489) PairedSynthCoreTrace.inline12Template = UInt256.ofNat 1539 := by rfl
def inline12Physical : PairedAllInlineCoreTrace.CoreBlock 1489 1539 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline12Template
  eval := PairedAllInlineCoreTrace.inline12Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline12Template_word s (UInt256.ofNat 1489) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline12_pcAfter] at h
    exact h

def inline12Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 240),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 255),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline12_slice :
    (Artifact.submissionArtifact.instructions.drop 1098).take inline12Template.length = inline12Template := by rfl
def inline12Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline12Template :=
  StackSiteBuilder.ofSlice inline12Template 1098 inline12_slice
    (by change 1098 + inline12Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline12Template) (by decide))
    (by decide)
theorem inline12_pc : inline12Site.startPC = UInt256.ofNat 1489 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1098) = UInt256.ofNat 1489
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline12_advances : ∀ instruction ∈ inline12Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline12Gas : PairedAllInlineCoreTrace.CoreGasBlock inline12Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline12Physical inline12Site inline12_pc inline12_advances
theorem inline13_pcAfter : pcAfter (UInt256.ofNat 1539) PairedSynthCoreTrace.inline13Template = UInt256.ofNat 1590 := by rfl
def inline13Physical : PairedAllInlineCoreTrace.CoreBlock 1539 1590 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline13Template
  eval := PairedAllInlineCoreTrace.inline13Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline13Template_word s (UInt256.ofNat 1539) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline13_pcAfter] at h
    exact h

def inline13Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 608),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 528),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 127),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline13_slice :
    (Artifact.submissionArtifact.instructions.drop 1142).take inline13Template.length = inline13Template := by rfl
def inline13Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline13Template :=
  StackSiteBuilder.ofSlice inline13Template 1142 inline13_slice
    (by change 1142 + inline13Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline13Template) (by decide))
    (by decide)
theorem inline13_pc : inline13Site.startPC = UInt256.ofNat 1539 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1142) = UInt256.ofNat 1539
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline13_advances : ∀ instruction ∈ inline13Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline13Gas : PairedAllInlineCoreTrace.CoreGasBlock inline13Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline13Physical inline13Site inline13_pc inline13_advances
theorem inline14_pcAfter : pcAfter (UInt256.ofNat 1590) PairedSynthCoreTrace.inline14Template = UInt256.ofNat 1641 := by rfl
def inline14Physical : PairedAllInlineCoreTrace.CoreBlock 1590 1641 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline14Template
  eval := PairedAllInlineCoreTrace.inline14Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline14Template_word s (UInt256.ofNat 1590) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline14_pcAfter] at h
    exact h

def inline14Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 304),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline14_slice :
    (Artifact.submissionArtifact.instructions.drop 1186).take inline14Template.length = inline14Template := by rfl
def inline14Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline14Template :=
  StackSiteBuilder.ofSlice inline14Template 1186 inline14_slice
    (by change 1186 + inline14Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline14Template) (by decide))
    (by decide)
theorem inline14_pc : inline14Site.startPC = UInt256.ofNat 1590 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1186) = UInt256.ofNat 1590
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline14_advances : ∀ instruction ∈ inline14Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline14Gas : PairedAllInlineCoreTrace.CoreGasBlock inline14Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline14Physical inline14Site inline14_pc inline14_advances
theorem inline15_pcAfter : pcAfter (UInt256.ofNat 1641) PairedSynthCoreTrace.inline15Template = UInt256.ofNat 1692 := by rfl
def inline15Physical : PairedAllInlineCoreTrace.CoreBlock 1641 1692 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedSynthCoreTrace.inline15Template
  eval := PairedAllInlineCoreTrace.inline15Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedSynthCoreTrace.run_inline15Template_word s (UInt256.ofNat 1641) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline15_pcAfter] at h
    exact h

def inline15Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 592),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline15_slice :
    (Artifact.submissionArtifact.instructions.drop 1230).take inline15Template.length = inline15Template := by rfl
def inline15Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline15Template :=
  StackSiteBuilder.ofSlice inline15Template 1230 inline15_slice
    (by change 1230 + inline15Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline15Template) (by decide))
    (by decide)
theorem inline15_pc : inline15Site.startPC = UInt256.ofNat 1641 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1230) = UInt256.ofNat 1641
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline15_advances : ∀ instruction ∈ inline15Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline15Gas : PairedAllInlineCoreTrace.CoreGasBlock inline15Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline15Physical inline15Site inline15_pc inline15_advances
def group16Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op .POP,
    .push ⟨4, by decide⟩ (UInt256.ofNat 1548603684),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHL,
    .push ⟨4, by decide⟩ (UInt256.ofNat 1518500249),
    .op .OR ]
theorem group16_pcAfter : pcAfter (UInt256.ofNat 1692) group16Template = UInt256.ofNat 1708 := by rfl
def group16Physical : PairedAllInlineCoreTrace.CoreBlock 1692 1708 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := group16Template
  eval := PairedAllInlineCoreTrace.group16Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have hcap (k : Nat) (hk : k ≤ 20) : rho.length + k < 1024 := by omega
    simp (discharger := omega) [group16Template, runInstrSeq, Stepper.runInstr,
      coreStack, CoreReg.word, CoreFrame.frame, PairedAllInlineCoreTrace.group16Block,
      UInt256.succ, Instr.size, List.exchange, hrun, hcap, Nat.add_assoc,
      List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals repeat first | apply And.intro | rfl

theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1274).take group16Template.length = group16Template := by rfl
def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka group16Template :=
  StackSiteBuilder.ofSlice group16Template 1274 group16_slice
    (by change 1274 + group16Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group16Template) (by decide))
    (by decide)
theorem group16_pc : group16Site.startPC = UInt256.ofNat 1692 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1274) = UInt256.ofNat 1692
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group16_advances : ∀ instruction ∈ group16Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group16Gas : PairedAllInlineCoreTrace.CoreGasBlock group16Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group16Physical group16Site group16_pc group16_advances
theorem inline18_pcAfter : pcAfter (UInt256.ofNat 1808) PairedAllInlineCoreTrace.inline18Template = UInt256.ofNat 1861 := by rfl
def inline18Physical : PairedAllInlineCoreTrace.CoreBlock 1808 1861 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline18Template
  eval := PairedAllInlineCoreTrace.inline18Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline18Template_word s (UInt256.ofNat 1808) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline18_pcAfter] at h
    exact h

def inline18Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 608),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 304),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 127),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline18_slice :
    (Artifact.submissionArtifact.instructions.drop 1371).take inline18Template.length = inline18Template := by rfl
def inline18Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline18Template :=
  StackSiteBuilder.ofSlice inline18Template 1371 inline18_slice
    (by change 1371 + inline18Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline18Template) (by decide))
    (by decide)
theorem inline18_pc : inline18Site.startPC = UInt256.ofNat 1808 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1371) = UInt256.ofNat 1808
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline18_advances : ∀ instruction ∈ inline18Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline18Gas : PairedAllInlineCoreTrace.CoreGasBlock inline18Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline18Physical inline18Site inline18_pc inline18_advances
theorem inline19_pcAfter : pcAfter (UInt256.ofNat 1861) PairedAllInlineCoreTrace.inline19Template = UInt256.ofNat 1913 := by rfl
def inline19Physical : PairedAllInlineCoreTrace.CoreBlock 1861 1913 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline19Template
  eval := PairedAllInlineCoreTrace.inline19Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline19Template_word s (UInt256.ofNat 1861) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline19_pcAfter] at h
    exact h

def inline19Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 432),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline19_slice :
    (Artifact.submissionArtifact.instructions.drop 1417).take inline19Template.length = inline19Template := by rfl
def inline19Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline19Template :=
  StackSiteBuilder.ofSlice inline19Template 1417 inline19_slice
    (by change 1417 + inline19Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline19Template) (by decide))
    (by decide)
theorem inline19_pc : inline19Site.startPC = UInt256.ofNat 1861 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1417) = UInt256.ofNat 1861
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline19_advances : ∀ instruction ∈ inline19Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline19Gas : PairedAllInlineCoreTrace.CoreGasBlock inline19Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline19Physical inline19Site inline19_pc inline19_advances
theorem inline20_pcAfter : pcAfter (UInt256.ofNat 1913) PairedAllInlineCoreTrace.inline20Template = UInt256.ofNat 1962 := by rfl
def inline20Physical : PairedAllInlineCoreTrace.CoreBlock 1913 1962 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline20Template
  eval := PairedAllInlineCoreTrace.inline20Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline20Template_word s (UInt256.ofNat 1913) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline20_pcAfter] at h
    exact h

def inline20Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 512),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 208),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 21),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline20_slice :
    (Artifact.submissionArtifact.instructions.drop 1463).take inline20Template.length = inline20Template := by rfl
def inline20Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline20Template :=
  StackSiteBuilder.ofSlice inline20Template 1463 inline20_slice
    (by change 1463 + inline20Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline20Template) (by decide))
    (by decide)
theorem inline20_pc : inline20Site.startPC = UInt256.ofNat 1913 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1463) = UInt256.ofNat 1913
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline20_advances : ∀ instruction ∈ inline20Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline20Gas : PairedAllInlineCoreTrace.CoreGasBlock inline20Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline20Physical inline20Site inline20_pc inline20_advances
theorem inline22_pcAfter : pcAfter (UInt256.ofNat 2009) PairedAllInlineCoreTrace.inline22Template = UInt256.ofNat 2062 := by rfl
def inline22Physical : PairedAllInlineCoreTrace.CoreBlock 2009 2062 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline22Template
  eval := PairedAllInlineCoreTrace.inline22Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline22Template_word s (UInt256.ofNat 2009) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline22_pcAfter] at h
    exact h

def inline22Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 368),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline22_slice :
    (Artifact.submissionArtifact.instructions.drop 1550).take inline22Template.length = inline22Template := by rfl
def inline22Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline22Template :=
  StackSiteBuilder.ofSlice inline22Template 1550 inline22_slice
    (by change 1550 + inline22Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline22Template) (by decide))
    (by decide)
theorem inline22_pc : inline22Site.startPC = UInt256.ofNat 2009 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1550) = UInt256.ofNat 2009
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline22_advances : ∀ instruction ∈ inline22Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline22Gas : PairedAllInlineCoreTrace.CoreGasBlock inline22Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline22Physical inline22Site inline22_pc inline22_advances
theorem inline24_pcAfter : pcAfter (UInt256.ofNat 2112) PairedAllInlineCoreTrace.inline24Template = UInt256.ofNat 2158 := by rfl
def inline24Physical : PairedAllInlineCoreTrace.CoreBlock 2112 2158 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline24Template
  eval := PairedAllInlineCoreTrace.inline24Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline24Template_word s (UInt256.ofNat 2112) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline24_pcAfter] at h
    exact h

def inline24Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 656),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline24_slice :
    (Artifact.submissionArtifact.instructions.drop 1641).take inline24Template.length = inline24Template := by rfl
def inline24Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline24Template :=
  StackSiteBuilder.ofSlice inline24Template 1641 inline24_slice
    (by change 1641 + inline24Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline24Template) (by decide))
    (by decide)
theorem inline24_pc : inline24Site.startPC = UInt256.ofNat 2112 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1641) = UInt256.ofNat 2112
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline24_advances : ∀ instruction ∈ inline24Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline24Gas : PairedAllInlineCoreTrace.CoreGasBlock inline24Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline24Physical inline24Site inline24_pc inline24_advances
theorem inline25_pcAfter : pcAfter (UInt256.ofNat 2158) PairedAllInlineCoreTrace.inline25Template = UInt256.ofNat 2210 := by rfl
def inline25Physical : PairedAllInlineCoreTrace.CoreBlock 2158 2210 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline25Template
  eval := PairedAllInlineCoreTrace.inline25Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline25Template_word s (UInt256.ofNat 2158) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline25_pcAfter] at h
    exact h

def inline25Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 688),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 31),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline25_slice :
    (Artifact.submissionArtifact.instructions.drop 1681).take inline25Template.length = inline25Template := by rfl
def inline25Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline25Template :=
  StackSiteBuilder.ofSlice inline25Template 1681 inline25_slice
    (by change 1681 + inline25Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline25Template) (by decide))
    (by decide)
theorem inline25_pc : inline25Site.startPC = UInt256.ofNat 2158 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1681) = UInt256.ofNat 2158
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline25_advances : ∀ instruction ∈ inline25Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline25Gas : PairedAllInlineCoreTrace.CoreGasBlock inline25Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline25Physical inline25Site inline25_pc inline25_advances
theorem inline26_pcAfter : pcAfter (UInt256.ofNat 2210) PairedAllInlineCoreTrace.inline26Template = UInt256.ofNat 2263 := by rfl
def inline26Physical : PairedAllInlineCoreTrace.CoreBlock 2210 2263 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline26Template
  eval := PairedAllInlineCoreTrace.inline26Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline26Template_word s (UInt256.ofNat 2210) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline26_pcAfter] at h
    exact h

def inline26Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 480),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 464),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline26_slice :
    (Artifact.submissionArtifact.instructions.drop 1727).take inline26Template.length = inline26Template := by rfl
def inline26Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline26Template :=
  StackSiteBuilder.ofSlice inline26Template 1727 inline26_slice
    (by change 1727 + inline26Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline26Template) (by decide))
    (by decide)
theorem inline26_pc : inline26Site.startPC = UInt256.ofNat 2210 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1727) = UInt256.ofNat 2210
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline26_advances : ∀ instruction ∈ inline26Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline26Gas : PairedAllInlineCoreTrace.CoreGasBlock inline26Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline26Physical inline26Site inline26_pc inline26_advances
theorem inline29_pcAfter : pcAfter (UInt256.ofNat 2363) PairedAllInlineNewPairs.inline29Template = UInt256.ofNat 2416 := by rfl
def inline29Physical : PairedAllInlineCoreTrace.CoreBlock 2363 2416 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineNewPairs.inline29Template
  eval := PairedAllInlineCoreTrace.inline29Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineNewPairs.run_inline29Template_word s (UInt256.ofNat 2363) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline29_pcAfter] at h
    exact h

def inline29Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 496),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 255),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline29_slice :
    (Artifact.submissionArtifact.instructions.drop 1863).take inline29Template.length = inline29Template := by rfl
def inline29Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline29Template :=
  StackSiteBuilder.ofSlice inline29Template 1863 inline29_slice
    (by change 1863 + inline29Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline29Template) (by decide))
    (by decide)
theorem inline29_pc : inline29Site.startPC = UInt256.ofNat 2363 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1863) = UInt256.ofNat 2363
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline29_advances : ∀ instruction ∈ inline29Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline29Gas : PairedAllInlineCoreTrace.CoreGasBlock inline29Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline29Physical inline29Site inline29_pc inline29_advances
theorem inline30_pcAfter : pcAfter (UInt256.ofNat 2416) PairedAllInlineCoreTrace.inline30Template = UInt256.ofNat 2461 := by rfl
def inline30Physical : PairedAllInlineCoreTrace.CoreBlock 2416 2461 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline30Template
  eval := PairedAllInlineCoreTrace.inline30Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline30Template_word s (UInt256.ofNat 2416) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline30_pcAfter] at h
    exact h

def inline30Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨2, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 240),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 19),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline30_slice :
    (Artifact.submissionArtifact.instructions.drop 1909).take inline30Template.length = inline30Template := by rfl
def inline30Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline30Template :=
  StackSiteBuilder.ofSlice inline30Template 1909 inline30_slice
    (by change 1909 + inline30Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline30Template) (by decide))
    (by decide)
theorem inline30_pc : inline30Site.startPC = UInt256.ofNat 2416 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1909) = UInt256.ofNat 2416
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline30_advances : ∀ instruction ∈ inline30Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline30Gas : PairedAllInlineCoreTrace.CoreGasBlock inline30Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline30Physical inline30Site inline30_pc inline30_advances
theorem inline31_pcAfter : pcAfter (UInt256.ofNat 2461) PairedAllInlineCoreTrace.inline31Template = UInt256.ofNat 2511 := by rfl
def inline31Physical : PairedAllInlineCoreTrace.CoreBlock 2461 2511 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline31Template
  eval := PairedAllInlineCoreTrace.inline31Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline31Template_word s (UInt256.ofNat 2461) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline31_pcAfter] at h
    exact h

def inline31Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .OR,
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op .OR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 448),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 272),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 21),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline31_slice :
    (Artifact.submissionArtifact.instructions.drop 1949).take inline31Template.length = inline31Template := by rfl
def inline31Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline31Template :=
  StackSiteBuilder.ofSlice inline31Template 1949 inline31_slice
    (by change 1949 + inline31Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline31Template) (by decide))
    (by decide)
theorem inline31_pc : inline31Site.startPC = UInt256.ofNat 2461 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1949) = UInt256.ofNat 2461
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline31_advances : ∀ instruction ∈ inline31Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline31Gas : PairedAllInlineCoreTrace.CoreGasBlock inline31Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline31Physical inline31Site inline31_pc inline31_advances
def group32Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op .POP,
    .push ⟨5, by decide⟩ (UInt256.ofNat 6131039986),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHL,
    .push ⟨5, by decide⟩ (UInt256.ofNat 6154742689),
    .op .OR ]
theorem group32_pcAfter : pcAfter (UInt256.ofNat 2511) group32Template = UInt256.ofNat 2529 := by rfl
def group32Physical : PairedAllInlineCoreTrace.CoreBlock 2511 2529 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := group32Template
  eval := PairedAllInlineCoreTrace.group32Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have hcap (k : Nat) (hk : k ≤ 20) : rho.length + k < 1024 := by omega
    simp (discharger := omega) [group32Template, runInstrSeq, Stepper.runInstr,
      coreStack, CoreReg.word, CoreFrame.frame, PairedAllInlineCoreTrace.group32Block,
      UInt256.succ, Instr.size, List.exchange, hrun, hcap, Nat.add_assoc,
      List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals repeat first | apply And.intro | rfl

theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1993).take group32Template.length = group32Template := by rfl
def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka group32Template :=
  StackSiteBuilder.ofSlice group32Template 1993 group32_slice
    (by change 1993 + group32Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group32Template) (by decide))
    (by decide)
theorem group32_pc : group32Site.startPC = UInt256.ofNat 2511 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1993) = UInt256.ofNat 2511
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group32_advances : ∀ instruction ∈ group32Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group32Gas : PairedAllInlineCoreTrace.CoreGasBlock group32Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group32Physical group32Site group32_pc group32_advances
theorem inline33_pcAfter : pcAfter (UInt256.ofNat 2572) PairedAllInlineCoreTrace.inline33Template = UInt256.ofNat 2618 := by rfl
def inline33Physical : PairedAllInlineCoreTrace.CoreBlock 2572 2618 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline33Template
  eval := PairedAllInlineCoreTrace.inline33Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline33Template_word s (UInt256.ofNat 2572) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline33_pcAfter] at h
    exact h

def inline33Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨4, by decide⟩),
    .op .OR,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 512),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 368),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 25),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline33_slice :
    (Artifact.submissionArtifact.instructions.drop 2038).take inline33Template.length = inline33Template := by rfl
def inline33Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline33Template :=
  StackSiteBuilder.ofSlice inline33Template 2038 inline33_slice
    (by change 2038 + inline33Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline33Template) (by decide))
    (by decide)
theorem inline33_pc : inline33Site.startPC = UInt256.ofNat 2572 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2038) = UInt256.ofNat 2572
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline33_advances : ∀ instruction ∈ inline33Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline33Gas : PairedAllInlineCoreTrace.CoreGasBlock inline33Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline33Physical inline33Site inline33_pc inline33_advances
theorem inline34_pcAfter : pcAfter (UInt256.ofNat 2618) PairedAllInlineCoreTrace.inline34Template = UInt256.ofNat 2664 := by rfl
def inline34Physical : PairedAllInlineCoreTrace.CoreBlock 2618 2664 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline34Template
  eval := PairedAllInlineCoreTrace.inline34Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline34Template_word s (UInt256.ofNat 2618) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline34_pcAfter] at h
    exact h

def inline34Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 240),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 511),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline34_slice :
    (Artifact.submissionArtifact.instructions.drop 2077).take inline34Template.length = inline34Template := by rfl
def inline34Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline34Template :=
  StackSiteBuilder.ofSlice inline34Template 2077 inline34_slice
    (by change 2077 + inline34Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline34Template) (by decide))
    (by decide)
theorem inline34_pc : inline34Site.startPC = UInt256.ofNat 2618 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2077) = UInt256.ofNat 2618
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline34_advances : ∀ instruction ∈ inline34Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline34Gas : PairedAllInlineCoreTrace.CoreGasBlock inline34Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline34Physical inline34Site inline34_pc inline34_advances
theorem inline36_pcAfter : pcAfter (UInt256.ofNat 2707) PairedAllInlineCoreTrace.inline36Template = UInt256.ofNat 2753 := by rfl
def inline36Physical : PairedAllInlineCoreTrace.CoreBlock 2707 2753 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline36Template
  eval := PairedAllInlineCoreTrace.inline36Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline36Template_word s (UInt256.ofNat 2707) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline36_pcAfter] at h
    exact h

def inline36Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 480),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 432),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline36_slice :
    (Artifact.submissionArtifact.instructions.drop 2154).take inline36Template.length = inline36Template := by rfl
def inline36Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline36Template :=
  StackSiteBuilder.ofSlice inline36Template 2154 inline36_slice
    (by change 2154 + inline36Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline36Template) (by decide))
    (by decide)
theorem inline36_pc : inline36Site.startPC = UInt256.ofNat 2707 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2154) = UInt256.ofNat 2707
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline36_advances : ∀ instruction ∈ inline36Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline36Gas : PairedAllInlineCoreTrace.CoreGasBlock inline36Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline36Physical inline36Site inline36_pc inline36_advances
theorem inline37_pcAfter : pcAfter (UInt256.ofNat 2753) PairedAllInlineCoreTrace.inline37Template = UInt256.ofNat 2799 := by rfl
def inline37Physical : PairedAllInlineCoreTrace.CoreBlock 2753 2799 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline37Template
  eval := PairedAllInlineCoreTrace.inline37Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline37Template_word s (UInt256.ofNat 2753) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline37_pcAfter] at h
    exact h

def inline37Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨4, by decide⟩),
    .op .OR,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 656),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline37_slice :
    (Artifact.submissionArtifact.instructions.drop 2193).take inline37Template.length = inline37Template := by rfl
def inline37Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline37Template :=
  StackSiteBuilder.ofSlice inline37Template 2193 inline37_slice
    (by change 2193 + inline37Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline37Template) (by decide))
    (by decide)
theorem inline37_pc : inline37Site.startPC = UInt256.ofNat 2753 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2193) = UInt256.ofNat 2753
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline37_advances : ∀ instruction ∈ inline37Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline37Gas : PairedAllInlineCoreTrace.CoreGasBlock inline37Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline37Physical inline37Site inline37_pc inline37_advances
theorem inline38_pcAfter : pcAfter (UInt256.ofNat 2799) PairedAllInlineCoreTrace.inline38Template = UInt256.ofNat 2845 := by rfl
def inline38Physical : PairedAllInlineCoreTrace.CoreBlock 2799 2845 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline38Template
  eval := PairedAllInlineCoreTrace.inline38Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline38Template_word s (UInt256.ofNat 2799) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline38_pcAfter] at h
    exact h

def inline38Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 448),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 400),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 127),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline38_slice :
    (Artifact.submissionArtifact.instructions.drop 2232).take inline38Template.length = inline38Template := by rfl
def inline38Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline38Template :=
  StackSiteBuilder.ofSlice inline38Template 2232 inline38_slice
    (by change 2232 + inline38Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline38Template) (by decide))
    (by decide)
theorem inline38_pc : inline38Site.startPC = UInt256.ofNat 2799 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2232) = UInt256.ofNat 2799
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline38_advances : ∀ instruction ∈ inline38Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline38Gas : PairedAllInlineCoreTrace.CoreGasBlock inline38Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline38Physical inline38Site inline38_pc inline38_advances
theorem inline39_pcAfter : pcAfter (UInt256.ofNat 2845) PairedAllInlineCoreTrace.inline39Template = UInt256.ofNat 2887 := by rfl
def inline39Physical : PairedAllInlineCoreTrace.CoreBlock 2845 2887 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline39Template
  eval := PairedAllInlineCoreTrace.inline39Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline39Template_word s (UInt256.ofNat 2845) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline39_pcAfter] at h
    exact h

def inline39Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨4, by decide⟩),
    .op .OR,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 496),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 18),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline39_slice :
    (Artifact.submissionArtifact.instructions.drop 2271).take inline39Template.length = inline39Template := by rfl
def inline39Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline39Template :=
  StackSiteBuilder.ofSlice inline39Template 2271 inline39_slice
    (by change 2271 + inline39Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline39Template) (by decide))
    (by decide)
theorem inline39_pc : inline39Site.startPC = UInt256.ofNat 2845 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2271) = UInt256.ofNat 2845
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline39_advances : ∀ instruction ∈ inline39Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline39Gas : PairedAllInlineCoreTrace.CoreGasBlock inline39Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline39Physical inline39Site inline39_pc inline39_advances
theorem inline42_pcAfter : pcAfter (UInt256.ofNat 2973) PairedAllInlineCoreTrace.inline42Template = UInt256.ofNat 3018 := by rfl
def inline42Physical : PairedAllInlineCoreTrace.CoreBlock 2973 3018 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline42Template
  eval := PairedAllInlineCoreTrace.inline42Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline42Template_word s (UInt256.ofNat 2973) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline42_pcAfter] at h
    exact h

def inline42Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 592),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 255),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline42_slice :
    (Artifact.submissionArtifact.instructions.drop 2384).take inline42Template.length = inline42Template := by rfl
def inline42Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline42Template :=
  StackSiteBuilder.ofSlice inline42Template 2384 inline42_slice
    (by change 2384 + inline42Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline42Template) (by decide))
    (by decide)
theorem inline42_pc : inline42Site.startPC = UInt256.ofNat 2973 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2384) = UInt256.ofNat 2973
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline42_advances : ∀ instruction ∈ inline42Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline42Gas : PairedAllInlineCoreTrace.CoreGasBlock inline42Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline42Physical inline42Site inline42_pc inline42_advances
theorem inline44_pcAfter : pcAfter (UInt256.ofNat 3061) PairedAllInlineCoreTrace.inline44Template = UInt256.ofNat 3107 := by rfl
def inline44Physical : PairedAllInlineCoreTrace.CoreBlock 3061 3107 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline44Template
  eval := PairedAllInlineCoreTrace.inline44Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline44Template_word s (UInt256.ofNat 3061) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline44_pcAfter] at h
    exact h

def inline44Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨3, by decide⟩),
    .op .OR,
    .op (.Dup ⟨5, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 608),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 528),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 255),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline44_slice :
    (Artifact.submissionArtifact.instructions.drop 2461).take inline44Template.length = inline44Template := by rfl
def inline44Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline44Template :=
  StackSiteBuilder.ofSlice inline44Template 2461 inline44_slice
    (by change 2461 + inline44Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline44Template) (by decide))
    (by decide)
theorem inline44_pc : inline44Site.startPC = UInt256.ofNat 3061 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2461) = UInt256.ofNat 3061
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline44_advances : ∀ instruction ∈ inline44Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline44Gas : PairedAllInlineCoreTrace.CoreGasBlock inline44Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline44Physical inline44Site inline44_pc inline44_advances
theorem inline45_pcAfter : pcAfter (UInt256.ofNat 3107) PairedAllInlineCoreTrace.inline45Template = UInt256.ofNat 3149 := by rfl
def inline45Physical : PairedAllInlineCoreTrace.CoreBlock 3107 3149 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline45Template
  eval := PairedAllInlineCoreTrace.inline45Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline45Template_word s (UInt256.ofNat 3107) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline45_pcAfter] at h
    exact h

def inline45Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨4, by decide⟩),
    .op .OR,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 208),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline45_slice :
    (Artifact.submissionArtifact.instructions.drop 2500).take inline45Template.length = inline45Template := by rfl
def inline45Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline45Template :=
  StackSiteBuilder.ofSlice inline45Template 2500 inline45_slice
    (by change 2500 + inline45Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline45Template) (by decide))
    (by decide)
theorem inline45_pc : inline45Site.startPC = UInt256.ofNat 3107 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2500) = UInt256.ofNat 3107
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline45_advances : ∀ instruction ∈ inline45Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline45Gas : PairedAllInlineCoreTrace.CoreGasBlock inline45Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline45Physical inline45Site inline45_pc inline45_advances
theorem inline47_pcAfter : pcAfter (UInt256.ofNat 3185) PairedAllInlineCoreTrace.inline47Template = UInt256.ofNat 3224 := by rfl
def inline47Physical : PairedAllInlineCoreTrace.CoreBlock 3185 3224 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline47Template
  eval := PairedAllInlineCoreTrace.inline47Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline47Template_word s (UInt256.ofNat 3185) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline47_pcAfter] at h
    exact h

def inline47Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .NOT,
    .op (.Dup ⟨4, by decide⟩),
    .op .OR,
    .op (.Dup ⟨6, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 624),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline47_slice :
    (Artifact.submissionArtifact.instructions.drop 2569).take inline47Template.length = inline47Template := by rfl
def inline47Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline47Template :=
  StackSiteBuilder.ofSlice inline47Template 2569 inline47_slice
    (by change 2569 + inline47Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline47Template) (by decide))
    (by decide)
theorem inline47_pc : inline47Site.startPC = UInt256.ofNat 3185 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2569) = UInt256.ofNat 3185
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline47_advances : ∀ instruction ∈ inline47Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline47Gas : PairedAllInlineCoreTrace.CoreGasBlock inline47Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline47Physical inline47Site inline47_pc inline47_advances
def group48Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op .POP,
    .push ⟨4, by decide⟩ (UInt256.ofNat 2053994217),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHL,
    .push ⟨4, by decide⟩ (UInt256.ofNat 2400959708),
    .op .OR ]
theorem group48_pcAfter : pcAfter (UInt256.ofNat 3224) group48Template = UInt256.ofNat 3240 := by rfl
def group48Physical : PairedAllInlineCoreTrace.CoreBlock 3224 3240 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := group48Template
  eval := PairedAllInlineCoreTrace.group48Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have hcap (k : Nat) (hk : k ≤ 20) : rho.length + k < 1024 := by omega
    simp (discharger := omega) [group48Template, runInstrSeq, Stepper.runInstr,
      coreStack, CoreReg.word, CoreFrame.frame, PairedAllInlineCoreTrace.group48Block,
      UInt256.succ, Instr.size, List.exchange, hrun, hcap, Nat.add_assoc,
      List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals repeat first | apply And.intro | rfl

theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2602).take group48Template.length = group48Template := by rfl
def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka group48Template :=
  StackSiteBuilder.ofSlice group48Template 2602 group48_slice
    (by change 2602 + group48Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group48Template) (by decide))
    (by decide)
theorem group48_pc : group48Site.startPC = UInt256.ofNat 3224 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2602) = UInt256.ofNat 3224
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group48_advances : ∀ instruction ∈ group48Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group48Gas : PairedAllInlineCoreTrace.CoreGasBlock group48Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group48Physical group48Site group48_pc group48_advances
theorem inline48_pcAfter : pcAfter (UInt256.ofNat 3240) PairedAllInlineCoreTrace.inline48Template = UInt256.ofNat 3292 := by rfl
def inline48Physical : PairedAllInlineCoreTrace.CoreBlock 3240 3292 [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline48Template
  eval := PairedAllInlineCoreTrace.inline48Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline48Template_word s (UInt256.ofNat 3240) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline48_pcAfter] at h
    exact h

def inline48Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 464),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 15),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 21),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline48_slice :
    (Artifact.submissionArtifact.instructions.drop 2609).take inline48Template.length = inline48Template := by rfl
def inline48Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline48Template :=
  StackSiteBuilder.ofSlice inline48Template 2609 inline48_slice
    (by change 2609 + inline48Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline48Template) (by decide))
    (by decide)
theorem inline48_pc : inline48Site.startPC = UInt256.ofNat 3240 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2609) = UInt256.ofNat 3240
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline48_advances : ∀ instruction ∈ inline48Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline48Gas : PairedAllInlineCoreTrace.CoreGasBlock inline48Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline48Physical inline48Site inline48_pc inline48_advances
theorem inline49_pcAfter : pcAfter (UInt256.ofNat 3292) PairedAllInlineCoreTrace.inline49Template = UInt256.ofNat 3345 := by rfl
def inline49Physical : PairedAllInlineCoreTrace.CoreBlock 3292 3345 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline49Template
  eval := PairedAllInlineCoreTrace.inline49Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline49Template_word s (UInt256.ofNat 3292) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline49_pcAfter] at h
    exact h

def inline49Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 480),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 400),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 127),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline49_slice :
    (Artifact.submissionArtifact.instructions.drop 2655).take inline49Template.length = inline49Template := by rfl
def inline49Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline49Template :=
  StackSiteBuilder.ofSlice inline49Template 2655 inline49_slice
    (by change 2655 + inline49Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline49Template) (by decide))
    (by decide)
theorem inline49_pc : inline49Site.startPC = UInt256.ofNat 3292 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2655) = UInt256.ofNat 3292
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline49_advances : ∀ instruction ∈ inline49Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline49Gas : PairedAllInlineCoreTrace.CoreGasBlock inline49Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline49Physical inline49Site inline49_pc inline49_advances
theorem inline50_pcAfter : pcAfter (UInt256.ofNat 3345) PairedAllInlineCoreTrace.inline50Template = UInt256.ofNat 3398 := by rfl
def inline50Physical : PairedAllInlineCoreTrace.CoreBlock 3345 3398 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline50Template
  eval := PairedAllInlineCoreTrace.inline50Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline50Template_word s (UInt256.ofNat 3345) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline50_pcAfter] at h
    exact h

def inline50Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 336),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline50_slice :
    (Artifact.submissionArtifact.instructions.drop 2701).take inline50Template.length = inline50Template := by rfl
def inline50Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline50Template :=
  StackSiteBuilder.ofSlice inline50Template 2701 inline50_slice
    (by change 2701 + inline50Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline50Template) (by decide))
    (by decide)
theorem inline50_pc : inline50Site.startPC = UInt256.ofNat 3345 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2701) = UInt256.ofNat 3345
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline50_advances : ∀ instruction ∈ inline50Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline50Gas : PairedAllInlineCoreTrace.CoreGasBlock inline50Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline50Physical inline50Site inline50_pc inline50_advances
theorem inline51_pcAfter : pcAfter (UInt256.ofNat 3398) PairedAllInlineCoreTrace.inline51Template = UInt256.ofNat 3450 := by rfl
def inline51Physical : PairedAllInlineCoreTrace.CoreBlock 3398 3450 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline51Template
  eval := PairedAllInlineCoreTrace.inline51Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline51Template_word s (UInt256.ofNat 3398) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline51_pcAfter] at h
    exact h

def inline51Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 512),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 240),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 15),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 21),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline51_slice :
    (Artifact.submissionArtifact.instructions.drop 2747).take inline51Template.length = inline51Template := by rfl
def inline51Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline51Template :=
  StackSiteBuilder.ofSlice inline51Template 2747 inline51_slice
    (by change 2747 + inline51Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline51Template) (by decide))
    (by decide)
theorem inline51_pc : inline51Site.startPC = UInt256.ofNat 3398 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2747) = UInt256.ofNat 3398
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline51_advances : ∀ instruction ∈ inline51Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline51Gas : PairedAllInlineCoreTrace.CoreGasBlock inline51Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline51Physical inline51Site inline51_pc inline51_advances
theorem inline52_pcAfter : pcAfter (UInt256.ofNat 3450) PairedAllInlineCoreTrace.inline52Template = UInt256.ofNat 3495 := by rfl
def inline52Physical : PairedAllInlineCoreTrace.CoreBlock 3450 3495 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline52Template
  eval := PairedAllInlineCoreTrace.inline52Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline52Template_word s (UInt256.ofNat 3450) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline52_pcAfter] at h
    exact h

def inline52Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 304),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 18),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline52_slice :
    (Artifact.submissionArtifact.instructions.drop 2793).take inline52Template.length = inline52Template := by rfl
def inline52Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline52Template :=
  StackSiteBuilder.ofSlice inline52Template 2793 inline52_slice
    (by change 2793 + inline52Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline52Template) (by decide))
    (by decide)
theorem inline52_pc : inline52Site.startPC = UInt256.ofNat 3450 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2793) = UInt256.ofNat 3450
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline52_advances : ∀ instruction ∈ inline52Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline52Gas : PairedAllInlineCoreTrace.CoreGasBlock inline52Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline52Physical inline52Site inline52_pc inline52_advances
theorem inline53_pcAfter : pcAfter (UInt256.ofNat 3495) PairedAllInlineCoreTrace.inline53Template = UInt256.ofNat 3545 := by rfl
def inline53Physical : PairedAllInlineCoreTrace.CoreBlock 3495 3545 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline53Template
  eval := PairedAllInlineCoreTrace.inline53Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline53Template_word s (UInt256.ofNat 3495) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline53_pcAfter] at h
    exact h

def inline53Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 448),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 560),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 18),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline53_slice :
    (Artifact.submissionArtifact.instructions.drop 2833).take inline53Template.length = inline53Template := by rfl
def inline53Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline53Template :=
  StackSiteBuilder.ofSlice inline53Template 2833 inline53_slice
    (by change 2833 + inline53Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline53Template) (by decide))
    (by decide)
theorem inline53_pc : inline53Site.startPC = UInt256.ofNat 3495 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2833) = UInt256.ofNat 3495
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline53_advances : ∀ instruction ∈ inline53Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline53Gas : PairedAllInlineCoreTrace.CoreGasBlock inline53Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline53Physical inline53Site inline53_pc inline53_advances
theorem inline54_pcAfter : pcAfter (UInt256.ofNat 3545) PairedAllInlineCoreTrace.inline54Template = UInt256.ofNat 3598 := by rfl
def inline54Physical : PairedAllInlineCoreTrace.CoreBlock 3545 3598 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline54Template
  eval := PairedAllInlineCoreTrace.inline54Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline54Template_word s (UInt256.ofNat 3545) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline54_pcAfter] at h
    exact h

def inline54Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 688),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline54_slice :
    (Artifact.submissionArtifact.instructions.drop 2877).take inline54Template.length = inline54Template := by rfl
def inline54Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline54Template :=
  StackSiteBuilder.ofSlice inline54Template 2877 inline54_slice
    (by change 2877 + inline54Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline54Template) (by decide))
    (by decide)
theorem inline54_pc : inline54Site.startPC = UInt256.ofNat 3545 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2877) = UInt256.ofNat 3545
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline54_advances : ∀ instruction ∈ inline54Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline54Gas : PairedAllInlineCoreTrace.CoreGasBlock inline54Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline54Physical inline54Site inline54_pc inline54_advances
theorem inline56_pcAfter : pcAfter (UInt256.ofNat 3647) PairedAllInlineCoreTrace.inline56Template = UInt256.ofNat 3700 := by rfl
def inline56Physical : PairedAllInlineCoreTrace.CoreBlock 3647 3700 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline56Template
  eval := PairedAllInlineCoreTrace.inline56Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline56Template_word s (UInt256.ofNat 3647) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline56_pcAfter] at h
    exact h

def inline56Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 608),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 368),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline56_slice :
    (Artifact.submissionArtifact.instructions.drop 2968).take inline56Template.length = inline56Template := by rfl
def inline56Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline56Template :=
  StackSiteBuilder.ofSlice inline56Template 2968 inline56_slice
    (by change 2968 + inline56Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline56Template) (by decide))
    (by decide)
theorem inline56_pc : inline56Site.startPC = UInt256.ofNat 3647 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2968) = UInt256.ofNat 3647
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline56_advances : ∀ instruction ∈ inline56Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline56Gas : PairedAllInlineCoreTrace.CoreGasBlock inline56Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline56Physical inline56Site inline56_pc inline56_advances
theorem inline59_pcAfter : pcAfter (UInt256.ofNat 3800) PairedAllInlineCoreTrace.inline59Template = UInt256.ofNat 3853 := by rfl
def inline59Physical : PairedAllInlineCoreTrace.CoreBlock 3800 3853 [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline59Template
  eval := PairedAllInlineCoreTrace.inline59Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline59Template_word s (UInt256.ofNat 3800) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline59_pcAfter] at h
    exact h

def inline59Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 624),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline59_slice :
    (Artifact.submissionArtifact.instructions.drop 3104).take inline59Template.length = inline59Template := by rfl
def inline59Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline59Template :=
  StackSiteBuilder.ofSlice inline59Template 3104 inline59_slice
    (by change 3104 + inline59Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline59Template) (by decide))
    (by decide)
theorem inline59_pc : inline59Site.startPC = UInt256.ofNat 3800 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3104) = UInt256.ofNat 3800
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline59_advances : ∀ instruction ∈ inline59Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline59Gas : PairedAllInlineCoreTrace.CoreGasBlock inline59Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline59Physical inline59Site inline59_pc inline59_advances
theorem inline60_pcAfter : pcAfter (UInt256.ofNat 3853) PairedAllInlineCoreTrace.inline60Template = UInt256.ofNat 3906 := by rfl
def inline60Physical : PairedAllInlineCoreTrace.CoreBlock 3853 3906 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline60Template
  eval := PairedAllInlineCoreTrace.inline60Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline60Template_word s (UInt256.ofNat 3853) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline60_pcAfter] at h
    exact h

def inline60Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨11, by decide⟩),
    .op .OR,
    .op .XOR,
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 496),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 15),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline60_slice :
    (Artifact.submissionArtifact.instructions.drop 3150).take inline60Template.length = inline60Template := by rfl
def inline60Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline60Template :=
  StackSiteBuilder.ofSlice inline60Template 3150 inline60_slice
    (by change 3150 + inline60Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline60Template) (by decide))
    (by decide)
theorem inline60_pc : inline60Site.startPC = UInt256.ofNat 3853 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3150) = UInt256.ofNat 3853
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline60_advances : ∀ instruction ∈ inline60Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline60Gas : PairedAllInlineCoreTrace.CoreGasBlock inline60Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline60Physical inline60Site inline60_pc inline60_advances
theorem group64_pcAfter : pcAfter (UInt256.ofNat 4054) PairedAllInlineCoreTrace.group64Template = UInt256.ofNat 4061 := by rfl
def group64Physical : PairedAllInlineCoreTrace.CoreBlock 4054 4061 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group64Template
  eval := PairedAllInlineCoreTrace.group64Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group64Template s (UInt256.ofNat 4054) f.frame rho hstack hrun
    rw [group64_pcAfter] at h
    exact h

def group64Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op .POP,
    .push ⟨4, by decide⟩ (UInt256.ofNat 2840853838) ]
theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3329).take group64Template.length = group64Template := by rfl
def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka group64Template :=
  StackSiteBuilder.ofSlice group64Template 3329 group64_slice
    (by change 3329 + group64Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group64Template) (by decide))
    (by decide)
theorem group64_pc : group64Site.startPC = UInt256.ofNat 4054 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3329) = UInt256.ofNat 4054
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group64_advances : ∀ instruction ∈ group64Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group64Gas : PairedAllInlineCoreTrace.CoreGasBlock group64Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group64Physical group64Site group64_pc group64_advances
theorem inline65_pcAfter : pcAfter (UInt256.ofNat 4106) PairedAllInlineCoreTrace.inline65Template = UInt256.ofNat 4157 := by rfl
def inline65Physical : PairedAllInlineCoreTrace.CoreBlock 4106 4157 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline65Template
  eval := PairedAllInlineCoreTrace.inline65Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline65Template_word s (UInt256.ofNat 4106) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline65_pcAfter] at h
    exact h

def inline65Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 688),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 1023),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline65_slice :
    (Artifact.submissionArtifact.instructions.drop 3373).take inline65Template.length = inline65Template := by rfl
def inline65Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline65Template :=
  StackSiteBuilder.ofSlice inline65Template 3373 inline65_slice
    (by change 3373 + inline65Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline65Template) (by decide))
    (by decide)
theorem inline65_pc : inline65Site.startPC = UInt256.ofNat 4106 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3373) = UInt256.ofNat 4106
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline65_advances : ∀ instruction ∈ inline65Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline65Gas : PairedAllInlineCoreTrace.CoreGasBlock inline65Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline65Physical inline65Site inline65_pc inline65_advances
theorem inline67_pcAfter : pcAfter (UInt256.ofNat 4205) PairedAllInlineCoreTrace.inline67Template = UInt256.ofNat 4256 := by rfl
def inline67Physical : PairedAllInlineCoreTrace.CoreBlock 4205 4256 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline67Template
  eval := PairedAllInlineCoreTrace.inline67Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline67Template_word s (UInt256.ofNat 4205) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline67_pcAfter] at h
    exact h

def inline67Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 480),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 336),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 23),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline67_slice :
    (Artifact.submissionArtifact.instructions.drop 3460).take inline67Template.length = inline67Template := by rfl
def inline67Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline67Template :=
  StackSiteBuilder.ofSlice inline67Template 3460 inline67_slice
    (by change 3460 + inline67Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline67Template) (by decide))
    (by decide)
theorem inline67_pc : inline67Site.startPC = UInt256.ofNat 4205 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3460) = UInt256.ofNat 4205
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline67_advances : ∀ instruction ∈ inline67Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline67Gas : PairedAllInlineCoreTrace.CoreGasBlock inline67Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline67Physical inline67Site inline67_pc inline67_advances
theorem inline69_pcAfter : pcAfter (UInt256.ofNat 4303) PairedAllInlineCoreTrace.inline69Template = UInt256.ofNat 4354 := by rfl
def inline69Physical : PairedAllInlineCoreTrace.CoreBlock 4303 4354 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline69Template
  eval := PairedAllInlineCoreTrace.inline69Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline69Template_word s (UInt256.ofNat 4303) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline69_pcAfter] at h
    exact h

def inline69Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 368),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline69_slice :
    (Artifact.submissionArtifact.instructions.drop 3547).take inline69Template.length = inline69Template := by rfl
def inline69Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline69Template :=
  StackSiteBuilder.ofSlice inline69Template 3547 inline69_slice
    (by change 3547 + inline69Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline69Template) (by decide))
    (by decide)
theorem inline69_pc : inline69Site.startPC = UInt256.ofNat 4303 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3547) = UInt256.ofNat 4303
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline69_advances : ∀ instruction ∈ inline69Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline69Gas : PairedAllInlineCoreTrace.CoreGasBlock inline69Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline69Physical inline69Site inline69_pc inline69_advances
theorem inline71_pcAfter : pcAfter (UInt256.ofNat 4399) PairedAllInlineCoreTrace.inline71Template = UInt256.ofNat 4450 := by rfl
def inline71Physical : PairedAllInlineCoreTrace.CoreBlock 4399 4450 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline71Template
  eval := PairedAllInlineCoreTrace.inline71Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline71Template_word s (UInt256.ofNat 4399) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline71_pcAfter] at h
    exact h

def inline71Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 512),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 432),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 26),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline71_slice :
    (Artifact.submissionArtifact.instructions.drop 3632).take inline71Template.length = inline71Template := by rfl
def inline71Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline71Template :=
  StackSiteBuilder.ofSlice inline71Template 3632 inline71_slice
    (by change 3632 + inline71Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline71Template) (by decide))
    (by decide)
theorem inline71_pc : inline71Site.startPC = UInt256.ofNat 4399 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3632) = UInt256.ofNat 4399
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline71_advances : ∀ instruction ∈ inline71Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline71Gas : PairedAllInlineCoreTrace.CoreGasBlock inline71Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline71Physical inline71Site inline71_pc inline71_advances
theorem inline72_pcAfter : pcAfter (UInt256.ofNat 4450) PairedAllInlineCoreTrace.inline72Template = UInt256.ofNat 4501 := by rfl
def inline72Physical : PairedAllInlineCoreTrace.CoreBlock 4450 4501 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline72Template
  eval := PairedAllInlineCoreTrace.inline72Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline72Template_word s (UInt256.ofNat 4450) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline72_pcAfter] at h
    exact h

def inline72Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 400),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 7),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline72_slice :
    (Artifact.submissionArtifact.instructions.drop 3676).take inline72Template.length = inline72Template := by rfl
def inline72Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline72Template :=
  StackSiteBuilder.ofSlice inline72Template 3676 inline72_slice
    (by change 3676 + inline72Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline72Template) (by decide))
    (by decide)
theorem inline72_pc : inline72Site.startPC = UInt256.ofNat 4450 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3676) = UInt256.ofNat 4450
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline72_advances : ∀ instruction ∈ inline72Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline72Gas : PairedAllInlineCoreTrace.CoreGasBlock inline72Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline72Physical inline72Site inline72_pc inline72_advances
theorem inline73_pcAfter : pcAfter (UInt256.ofNat 4501) PairedAllInlineCoreTrace.inline73Template = UInt256.ofNat 4548 := by rfl
def inline73Physical : PairedAllInlineCoreTrace.CoreBlock 4501 4548 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline73Template
  eval := PairedAllInlineCoreTrace.inline73Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline73Template_word s (UInt256.ofNat 4501) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline73_pcAfter] at h
    exact h

def inline73Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 272),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline73_slice :
    (Artifact.submissionArtifact.instructions.drop 3720).take inline73Template.length = inline73Template := by rfl
def inline73Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline73Template :=
  StackSiteBuilder.ofSlice inline73Template 3720 inline73_slice
    (by change 3720 + inline73Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline73Template) (by decide))
    (by decide)
theorem inline73_pc : inline73Site.startPC = UInt256.ofNat 4501 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3720) = UInt256.ofNat 4501
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline73_advances : ∀ instruction ∈ inline73Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline73Gas : PairedAllInlineCoreTrace.CoreGasBlock inline73Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline73Physical inline73Site inline73_pc inline73_advances
theorem inline75_pcAfter : pcAfter (UInt256.ofNat 4596) PairedAllInlineCoreTrace.inline75Template = UInt256.ofNat 4648 := by rfl
def inline75Physical : PairedAllInlineCoreTrace.CoreBlock 4596 4648 [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline75Template
  eval := PairedAllInlineCoreTrace.inline75Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline75Template_word s (UInt256.ofNat 4596) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline75_pcAfter] at h
    exact h

def inline75Template : List Instr :=
  [ .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 448),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 656),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 511),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline75_slice :
    (Artifact.submissionArtifact.instructions.drop 3805).take inline75Template.length = inline75Template := by rfl
def inline75Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline75Template :=
  StackSiteBuilder.ofSlice inline75Template 3805 inline75_slice
    (by change 3805 + inline75Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline75Template) (by decide))
    (by decide)
theorem inline75_pc : inline75Site.startPC = UInt256.ofNat 4596 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3805) = UInt256.ofNat 4596
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline75_advances : ∀ instruction ∈ inline75Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline75Gas : PairedAllInlineCoreTrace.CoreGasBlock inline75Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline75Physical inline75Site inline75_pc inline75_advances
theorem inline76_pcAfter : pcAfter (UInt256.ofNat 4648) PairedAllInlineCoreTrace.inline76Template = UInt256.ofNat 4698 := by rfl
def inline76Physical : PairedAllInlineCoreTrace.CoreBlock 4648 4698 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline76Template
  eval := PairedAllInlineCoreTrace.inline76Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline76Template_word s (UInt256.ofNat 4648) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline76_pcAfter] at h
    exact h

def inline76Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 208),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 15),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 21),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline76_slice :
    (Artifact.submissionArtifact.instructions.drop 3849).take inline76Template.length = inline76Template := by rfl
def inline76Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline76Template :=
  StackSiteBuilder.ofSlice inline76Template 3849 inline76_slice
    (by change 3849 + inline76Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline76Template) (by decide))
    (by decide)
theorem inline76_pc : inline76Site.startPC = UInt256.ofNat 4648 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3849) = UInt256.ofNat 4648
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline76_advances : ∀ instruction ∈ inline76Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline76Gas : PairedAllInlineCoreTrace.CoreGasBlock inline76Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline76Physical inline76Site inline76_pc inline76_advances
theorem inline78_pcAfter : pcAfter (UInt256.ofNat 4746) PairedAllInlineCoreTrace.inline78Template = UInt256.ofNat 4797 := by rfl
def inline78Physical : PairedAllInlineCoreTrace.CoreBlock 4746 4797 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.inline78Template
  eval := PairedAllInlineCoreTrace.inline78Block.eval
  run := by
    intro s f rho hstack hrun hactive
    have h := PairedAllInlineCoreTrace.run_inline78Template_word s (UInt256.ofNat 4746) f.frame rho
      hstack hrun hactive rfl rfl rfl rfl
    rw [inline78_pcAfter] at h
    exact h

def inline78Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op .OR,
    .op (.Dup ⟨10, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .XOR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MLOAD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 496),
    .op .MLOAD,
    .op .OR,
    .op .ADD,
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 63),
    .op .MUL,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 27),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND ]
theorem inline78_slice :
    (Artifact.submissionArtifact.instructions.drop 3936).take inline78Template.length = inline78Template := by rfl
def inline78Site : GenericRoundSite Artifact.submissionArtifact .Osaka inline78Template :=
  StackSiteBuilder.ofSlice inline78Template 3936 inline78_slice
    (by change 3936 + inline78Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := inline78Template) (by decide))
    (by decide)
theorem inline78_pc : inline78Site.startPC = UInt256.ofNat 4746 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3936) = UInt256.ofNat 4746
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem inline78_advances : ∀ instruction ∈ inline78Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def inline78Gas : PairedAllInlineCoreTrace.CoreGasBlock inline78Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site inline78Physical inline78Site inline78_pc inline78_advances
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreStraight

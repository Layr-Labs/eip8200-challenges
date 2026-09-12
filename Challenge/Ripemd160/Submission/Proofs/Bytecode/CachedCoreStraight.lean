import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreStraight
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace PairedAllInlineCoreTrace CachedCoreCommon
def group0Template : List Instr :=
  [.push ⟨20, by decide⟩ (UInt256.ofNat 460344169260758029377710773882198039553172832256)]

theorem group0_pcAfter : pcAfter (UInt256.ofNat 755) group0Template = UInt256.ofNat 776 := by rfl

theorem run_group0_push (s : State) (q : PairedHelperBooleanTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running) :
    runInstrSeq group0Template {s with pc := UInt256.ofNat 755, stack := PairedAllInlineCoreTrace.group0Entry q rho} =
      some {s with pc := UInt256.ofNat 776, stack := PairedAllInlineCoreTrace.group0Output q rho} := by
  have hcap : rho.length + 9 < 1024 := by omega
  simp (discharger := omega) [group0Template, PairedAllInlineCoreTrace.group0Entry,
    PairedAllInlineCoreTrace.group0Output, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    hrun, List.length_append, Nat.add_assoc, hcap, Word.literal_eq_ofNat]
  rfl

def group0Physical : PairedAllInlineCoreTrace.CoreBlock 755 776 [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := group0Template
  eval := PairedAllInlineCoreTrace.group0Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    exact run_group0_push s f.frame rho hstack hrun

theorem group0_slice :
    (Artifact.submissionArtifact.instructions.drop 490).take group0Template.length = group0Template := by rfl
def group0Site : GenericRoundSite Artifact.submissionArtifact .Osaka group0Template :=
  StackSiteBuilder.ofSlice group0Template 490 group0_slice
    (by change 490 + group0Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group0Template) (by decide))
    (by decide)
theorem group0_pc : group0Site.startPC = UInt256.ofNat 755 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 490) = UInt256.ofNat 755
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group0_advances : ∀ instruction ∈ group0Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group0Gas : PairedAllInlineCoreTrace.CoreGasBlock group0Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group0Physical group0Site group0_pc group0_advances
theorem group16_pcAfter : pcAfter (UInt256.ofNat 1541) PairedAllInlineCoreTrace.group16Template = UInt256.ofNat 1564 := by rfl
def group16Physical : PairedAllInlineCoreTrace.CoreBlock 1541 1564 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group16Template
  eval := PairedAllInlineCoreTrace.group16Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group16Template s (UInt256.ofNat 1541) f.frame rho hstack hrun
    rw [group16_pcAfter] at h
    exact h

def group16Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op .POP,
    .push ⟨20, by decide⟩ (UInt256.ofNat 526962527014005041256681316140890030896371104153) ]
theorem group16_slice :
    (Artifact.submissionArtifact.instructions.drop 1188).take group16Template.length = group16Template := by rfl
def group16Site : GenericRoundSite Artifact.submissionArtifact .Osaka group16Template :=
  StackSiteBuilder.ofSlice group16Template 1188 group16_slice
    (by change 1188 + group16Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group16Template) (by decide))
    (by decide)
theorem group16_pc : group16Site.startPC = UInt256.ofNat 1541 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1188) = UInt256.ofNat 1541
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group16_advances : ∀ instruction ∈ group16Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group16Gas : PairedAllInlineCoreTrace.CoreGasBlock group16Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group16Physical group16Site group16_pc group16_advances
theorem group32_pcAfter : pcAfter (UInt256.ofNat 2341) PairedAllInlineCoreTrace.group32Template = UInt256.ofNat 2365 := by rfl
def group32Physical : PairedAllInlineCoreTrace.CoreBlock 2341 2365 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group32Template
  eval := PairedAllInlineCoreTrace.group32Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group32Template s (UInt256.ofNat 2341) f.frame rho hstack hrun
    rw [group32_pcAfter] at h
    exact h

def group32Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op .POP,
    .push ⟨21, by decide⟩ (UInt256.ofNat 2086284798122997420139349764661223671126594022305) ]
theorem group32_slice :
    (Artifact.submissionArtifact.instructions.drop 1904).take group32Template.length = group32Template := by rfl
def group32Site : GenericRoundSite Artifact.submissionArtifact .Osaka group32Template :=
  StackSiteBuilder.ofSlice group32Template 1904 group32_slice
    (by change 1904 + group32Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group32Template) (by decide))
    (by decide)
theorem group32_pc : group32Site.startPC = UInt256.ofNat 2341 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1904) = UInt256.ofNat 2341
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group32_advances : ∀ instruction ∈ group32Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group32Gas : PairedAllInlineCoreTrace.CoreGasBlock group32Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group32Physical group32Site group32_pc group32_advances
theorem group48_pcAfter : pcAfter (UInt256.ofNat 3034) PairedAllInlineCoreTrace.group48Template = UInt256.ofNat 3057 := by rfl
def group48Physical : PairedAllInlineCoreTrace.CoreBlock 3034 3057 [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] [.k, .d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group48Template
  eval := PairedAllInlineCoreTrace.group48Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group48Template s (UInt256.ofNat 3034) f.frame rho hstack hrun
    rw [group48_pcAfter] at h
    exact h

def group48Template : List Instr :=
  [ .op (.Swap ⟨0, by decide⟩),
    .op .POP,
    .push ⟨20, by decide⟩ (UInt256.ofNat 698938013802679700166637234969497128417458109660) ]
theorem group48_slice :
    (Artifact.submissionArtifact.instructions.drop 2510).take group48Template.length = group48Template := by rfl
def group48Site : GenericRoundSite Artifact.submissionArtifact .Osaka group48Template :=
  StackSiteBuilder.ofSlice group48Template 2510 group48_slice
    (by change 2510 + group48Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group48Template) (by decide))
    (by decide)
theorem group48_pc : group48Site.startPC = UInt256.ofNat 3034 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2510) = UInt256.ofNat 3034
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group48_advances : ∀ instruction ∈ group48Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group48Gas : PairedAllInlineCoreTrace.CoreGasBlock group48Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group48Physical group48Site group48_pc group48_advances
theorem group64_pcAfter : pcAfter (UInt256.ofNat 3845) PairedAllInlineCoreTrace.group64Template = UInt256.ofNat 3852 := by rfl
def group64Physical : PairedAllInlineCoreTrace.CoreBlock 3845 3852 [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] [.k, .a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] where
  code := PairedAllInlineCoreTrace.group64Template
  eval := PairedAllInlineCoreTrace.group64Block.eval
  run := by
    intro s f rho hstack hrun _hactive
    have h := PairedAllInlineCoreTrace.run_group64Template s (UInt256.ofNat 3845) f.frame rho hstack hrun
    rw [group64_pcAfter] at h
    exact h

def group64Template : List Instr :=
  [ .op (.Swap ⟨3, by decide⟩),
    .op .POP,
    .push ⟨4, by decide⟩ (UInt256.ofNat 2840853838) ]
theorem group64_slice :
    (Artifact.submissionArtifact.instructions.drop 3234).take group64Template.length = group64Template := by rfl
def group64Site : GenericRoundSite Artifact.submissionArtifact .Osaka group64Template :=
  StackSiteBuilder.ofSlice group64Template 3234 group64_slice
    (by change 3234 + group64Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := group64Template) (by decide))
    (by decide)
theorem group64_pc : group64Site.startPC = UInt256.ofNat 3845 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3234) = UInt256.ofNat 3845
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem group64_advances : ∀ instruction ∈ group64Template.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def group64Gas : PairedAllInlineCoreTrace.CoreGasBlock group64Physical Artifact.submissionArtifact .Osaka :=
  PairedAllInlineCoreTrace.CoreGasBlock.of_site group64Physical group64Site group64_pc group64_advances
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreStraight

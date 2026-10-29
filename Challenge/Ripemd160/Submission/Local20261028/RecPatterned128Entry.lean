import Challenge.Ripemd160.Submission.Local20261028.RecPatternedSites
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Patterned128Entry
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace StackRoundTemplate

private def fallbackTemplate : List Instr := [.push 1 245, .op .JUMP]
private def genericTemplate : List Instr := [.op .JUMPDEST]
private theorem fallback_slice : (Control.Artifact.submissionArtifact.instructions.drop 6097).take fallbackTemplate.length = fallbackTemplate := by rfl
private theorem generic_slice : (Control.Artifact.submissionArtifact.instructions.drop 133).take genericTemplate.length = genericTemplate := by rfl
private def fallbackSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka fallbackTemplate :=
 StackSiteBuilder.ofSlice fallbackTemplate 6097 fallback_slice
  (by change 6097 + fallbackTemplate.length ≤ Control.Artifact.submissionInstructions.length; rw [CandidateArtifact.instruction_count]; decide)
  code_bound (Control.StackRoundData.templateWellFormed_mem (instructions := fallbackTemplate) (by decide)) (by decide)
private def genericSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka genericTemplate :=
 StackSiteBuilder.ofSlice genericTemplate 133 generic_slice
  (by change 133 + genericTemplate.length ≤ Control.Artifact.submissionInstructions.length; rw [CandidateArtifact.instruction_count]; decide)
  code_bound (Control.StackRoundData.templateWellFormed_mem (instructions := genericTemplate) (by decide)) (by decide)
private theorem fallback_pc : fallbackSite.startPC = UInt256.ofNat 8086 := by
 change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6097) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem generic_pc : genericSite.startPC = UInt256.ofNat 245 := by
 change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 133) = _
 rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private theorem fallback_raw_general (s : State) (hrun : s.halt = .Running)
 (hv : Decode.isValidJumpDest s.executionEnv.code 245 = true) :
 runInstrSeq fallbackTemplate {s with pc := UInt256.ofNat 8086, stack := []} =
  some {s with pc := UInt256.ofNat 245, stack := []} := by
 simp [fallbackTemplate,runInstrSeq,DataStepper.runInstr,hrun,
  Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat,hv]
private theorem fallback_raw (input : ByteArray) :
 runInstrSeq fallbackTemplate (PatternedScan.stS input 8086 []) = some (PatternedScan.stS input 245 []) :=
 fallback_raw_general (initialState submissionBytecode input 0) rfl DirectGuard.generic_dest
private theorem generic_raw (input : ByteArray) :
 runInstrSeq genericTemplate (PatternedScan.stS input 245 []) = some (PatternedScan.stS input 246 []) := by
  simp [genericTemplate,runInstrSeq,DataStepper.runInstr,PatternedScan.stS,initialState,
   Word.literal_eq_ofNat,Word.succ_ofNat_mod,Word.ofNat_add_mod,Word.word_toNat_ofNat]
private def fallbackGas (input : ByteArray) : GasSteps (PatternedScan.stS input 8086 []) (PatternedScan.stS input 245 []) :=
 RecognitionLift.gasSteps_of_raw fallbackSite _ _ rfl rfl rfl deployAddress_not_precompile fallback_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) (fallback_raw input)
private def genericGas (input : ByteArray) : GasSteps (PatternedScan.stS input 245 []) (PatternedScan.stS input 246 []) :=
 RecognitionLift.gasSteps_of_raw genericSite _ _ rfl rfl rfl deployAddress_not_precompile generic_pc.symm
  (RecognitionLift.advancesAll_sound _ (by decide)) (generic_raw input)
private def gasSteps_fallback (input : ByteArray) :
 GasSteps (PatternedScan.stS input 8086 []) (PatternedScan.stS input 246 []) :=
 (fallbackGas input).trans (genericGas input)

/-- Tiny misses enter the generic compressor directly. -/
def gasSteps_after_arm_miss (input : ByteArray) (_hfit : CalldataFits input)
 (_hn : ¬ RecognitionAccumulator.Allowed input.size) :
 GasSteps (Control.AbcArm.fallbackState input) (Control.Execution.atPC input 246) :=
 gasSteps_fallback input


#print axioms gasSteps_short
#print axioms gasSteps_to_arm
#print axioms gasSteps_after_arm_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Patterned128Entry

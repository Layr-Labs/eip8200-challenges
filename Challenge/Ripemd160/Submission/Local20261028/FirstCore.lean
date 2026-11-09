import Challenge.Ripemd160.Submission.Local20261028.CoreGas
import Challenge.Ripemd160.Submission.Local20261028.PrepFirstReady
import Challenge.Ripemd160.Submission.Local20261028.PrepFirst608
import Challenge.Ripemd160.Submission.Local20261028.PrepFirstPrologue
import Challenge.Ripemd160.Submission.Local20261028.GeneralMessageReady
import Challenge.Ripemd160.Submission.Local20261028.PadTrace
import Challenge.Ripemd160.Submission.Local20261028.NormalMessage
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstCore
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate RipemdSubmissionTables20261028 RipemdMemoryBridge20261028
def initialHash : Compression.HashState :=
  ⟨1732584193, 4023233417, 2562383102, 271733878, 3285377520⟩
def frame (continuation : UInt256) (rho : List UInt256) :=
  StaggerPersistentFrame.frame initialHash (UInt256.ofNat 1056) continuation (NormalPrepare.masks rho)
open RipemdSubmission20261101
abbrev prefixArgs := FirstPrologue.args
def prepared (s : State) : State := {s with memory := RipemdSubmission20261101.FirstMemory.memory27 s}
theorem frame_eq (cont : UInt256) (rho : List UInt256) :
    First0.inputs (prefixArgs cont) rho = frame cont rho := by
  simp [First0.inputs, prefixArgs, FirstPrologue.args, FirstPrologue.frame, frame, initialHash,
    StaggerPersistentFrame.frame, NormalPrepare.masks]
  decide +kernel
theorem table_run (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq FirstTable.template {s with pc := UInt256.ofNat 9944, stack := frame cont rho} =
      some {prepared s with pc := UInt256.ofNat 10185, stack := frame cont rho} := by
  have h := FirstTable.run s (prefixArgs cont) rho (by omega) hr ha
  rw [frame_eq, RipemdSubmission20261101.FirstMemory.eq5] at h
  simpa only [RipemdSubmission20261101.FirstMemory.state5, prepared, ← frame_eq, First0.inputs] using h
def tableSite : GenericRoundSite CandidateArtifact.artifact .Osaka FirstTable.template :=
  StackSiteBuilder.ofSlice FirstTable.template 6845 (by rfl)
    (by change 6845 + (FirstTable.template).length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem tableSite_pc : tableSite.startPC = UInt256.ofNat 9944 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 6845) = UInt256.ofNat 9944
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def table_gas (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 9944, stack := frame cont rho}
      {prepared s with pc := UInt256.ofNat 10185, stack := frame cont rho} := by
  apply RecognitionLift.gasSteps_of_raw tableSite {s with pc := UInt256.ofNat 9944, stack := frame cont rho}
    {prepared s with pc := UInt256.ofNat 10185, stack := frame cont rho} hc hf hr hnp tableSite_pc.symm
  · apply RecognitionLift.advancesAll_sound; decide +kernel
  · exact table_run s cont rho hs hr ha

def prefixState (s : State) (cont : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10422, stack := PrefixBefore.outputs (prefixArgs cont) rho s}
def rest : List Instr := ((FirstPrologue.suffix ++ RoundComposition.block 77) ++ CoreEpilogue.template) ++ CoreTail.template

theorem split_template : CoreBody.template = PrefixBefore.template ++ rest := by
  simp only [CoreBody.template, rest, ← List.append_assoc]
  rfl

theorem rest_run (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq rest {prefixState s cont rho with pc := UInt256.ofNat 930} =
      some {s with pc := UInt256.ofNat 4622, stack := Word.ofUInt32 initialHash.h2 ::
        StaggerPersistentFrame.frame (CoreFunctional.result s.memory initialHash) (UInt256.ofNat 1056) cont (NormalPrepare.masks rho)} := by
  have hw := CoreBody.run s initialHash (UInt256.ofNat 1056) cont (NormalPrepare.masks rho)
    (by simp only [NormalPrepare.masks, List.length_cons]; omega) hr ha
  rw [split_template] at hw
  obtain ⟨u,hu,_,ht⟩ := PadTrace.split (s := {s with pc := UInt256.ofNat 794, stack := frame cont rho}) (by decide : rest ≠ []) hr hw
  have hb := PrefixBefore.run s (prefixArgs cont) rho (by omega) hr ha
  have hi : PrefixBefore.inputs (prefixArgs cont) rho = frame cont rho := frame_eq cont rho
  rw [hi] at hb
  change runInstrSeq PrefixBefore.template {s with pc := UInt256.ofNat 794, stack := frame cont rho} = some u at hu
  rw [hb] at hu
  cases hu
  exact ht
def prefixSite : GenericRoundSite CandidateArtifact.artifact .Osaka PrefixAfter.template :=
  StackSiteBuilder.ofSlice PrefixAfter.template 6941 (by rfl)
    (by change 6941 + (PrefixAfter.template).length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem prefixSite_pc : prefixSite.startPC = UInt256.ofNat 10185 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 6941) = UInt256.ofNat 10185
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def prefix_gas (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hm608 : MachineState.readWord s.memory 608 = UInt256.ofNat 5708990770823839524233143877797980545530986752) :
    GasSteps {s with pc := UInt256.ofNat 10185, stack := frame cont rho} (prefixState s cont rho) := by
  apply PadLift.gasSteps_of_raw prefixSite {s with pc := UInt256.ofNat 10185, stack := frame cont rho}
    (prefixState s cont rho) hc hf hr hnp prefixSite_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · have h := PrefixAfter.run s (prefixArgs cont) rho (by omega) hr ha
    have hi : PrefixAfter.inputs (prefixArgs cont) rho = frame cont rho := frame_eq cont rho
    rw [hi, ← FirstPrologue.outputs_eq s cont rho hm608] at h
    exact h

def jumpTemplate : List Instr := [.push ⟨2,by decide⟩ (UInt256.ofNat 930), .op .JUMP]
def jumpSite : GenericRoundSite CandidateArtifact.artifact .Osaka jumpTemplate :=
  StackSiteBuilder.ofSlice jumpTemplate 7018 (by rfl)
    (by change 7018 + (jumpTemplate).length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem jumpSite_pc : jumpSite.startPC = UInt256.ofNat 10422 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 7018) = UInt256.ofNat 10422
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
theorem valid_join : Decode.isValidJumpDest CandidateArtifact.artifact.code 930 = true := by
  have hpc : CandidateArtifact.artifact.instructionPC 458 = 930 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel
  have h := CandidateArtifact.artifact.isValidJumpDest_index 458 (by rfl)
  rw [hpc] at h
  exact h

def jump_gas (s : State) (rho : List UInt256) (hs : rho.length ≤ 990)
    (hr : s.halt = .Running) (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 10422, stack := rho} {s with pc := UInt256.ofNat 930, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 10422, stack := rho}
    {s with pc := UInt256.ofNat 930, stack := rho} hc hf hr hnp jumpSite_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hv : Decode.isValidJumpDest s.executionEnv.code 930 = true := by rw [hc]; exact valid_join
    simp [jumpTemplate, runInstrSeq, DataStepper.runInstr, hr, hv,
      show rho.length < 1024 by omega, show rho.length+1 < 1024 by omega]
def restSite : GenericRoundSite CandidateArtifact.artifact .Osaka rest :=
  StackSiteBuilder.ofSlice rest 458 (by rfl)
    (by change 458 + (rest).length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem restSite_pc : restSite.startPC = UInt256.ofNat 930 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 458) = UInt256.ofNat 930
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def rest_gas (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {prefixState s cont rho with pc := UInt256.ofNat 930}
      {s with pc := UInt256.ofNat 4622, stack := Word.ofUInt32 initialHash.h2 ::
        StaggerPersistentFrame.frame (CoreFunctional.result s.memory initialHash) (UInt256.ofNat 1056) cont (NormalPrepare.masks rho)} := by
  apply ModFoldLift.gasSteps_of_raw restSite {prefixState s cont rho with pc := UInt256.ofNat 930}
    {s with pc := UInt256.ofNat 4622, stack := Word.ofUInt32 initialHash.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result s.memory initialHash) (UInt256.ofNat 1056) cont (NormalPrepare.masks rho)} hc hf hr hnp restSite_pc.symm
  · apply ModFoldLift.advancesAll_sound; decide +kernel
  · exact rest_run s cont rho hs hr ha

def gasSteps (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 9944, stack := frame cont rho}
      {prepared s with pc := UInt256.ofNat 4622, stack := Word.ofUInt32 initialHash.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result (prepared s).memory initialHash) (UInt256.ofNat 1056) cont (NormalPrepare.masks rho)} := by
  have hm608 := First608.read s (prefixArgs cont) rho hc
  rw [RipemdSubmission20261101.FirstMemory.actual_memory] at hm608
  have hlen : (PrefixBefore.outputs (prefixArgs cont) rho (prepared s)).length ≤ 990 := by
    simp only [PrefixBefore.outputs, List.length_append, List.length_cons, List.length_nil]
    omega
  exact (table_gas s cont rho hs hr ha hc hf hnp).trans
    ((prefix_gas (prepared s) cont rho hs hr ha hc hf hnp hm608).trans
      ((jump_gas (prepared s) (PrefixBefore.outputs (prefixArgs cont) rho (prepared s)) hlen hr hc hf hnp).trans
        (rest_gas (prepared s) cont rho hs hr ha hc hf hnp)))

theorem ready (s : State)
    (hm : Matches s.memory FirstLayout.initial (FirstLayout.value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    CoreMessage.Ready (prepared s).memory (GeneralMessageReady.entryWords s.memory) := by
  have h := FirstReady.ready s (prefixArgs 0) [] hm hc
  rw [RipemdSubmission20261101.FirstMemory.actual_memory] at h
  exact h
#print axioms gasSteps
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstCore

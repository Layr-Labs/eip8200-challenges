import Challenge.Ripemd160.Submission.Local20261028.CoreGas
import Challenge.Ripemd160.Submission.Local20261028.FirstMessageReady
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
def prepared (s : State) : State := {s with memory := FirstMemory.memory33 s}
theorem frame_eq (continuation : UInt256) (rho : List UInt256) :
    First0.inputs (FirstMemory.frame continuation) rho = frame continuation rho := by rfl
theorem table_run (s : State) (continuation : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq FirstTable.template {s with pc := UInt256.ofNat 10141, stack := frame continuation rho} =
      some {prepared s with pc := UInt256.ofNat 10496, stack := frame continuation rho} := by
  have h := FirstTable.run s (FirstMemory.frame continuation) rho (by omega) hr ha
  rw [frame_eq, FirstMemory.eq7] at h
  exact h
def tableSite : GenericRoundSite CandidateArtifact.artifact .Osaka FirstTable.template :=
  StackSiteBuilder.ofSlice FirstTable.template 6921 (by rfl)
    (by change 6921 + FirstTable.template.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem table_pc : tableSite.startPC = UInt256.ofNat 10141 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 6921) = UInt256.ofNat 10141
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def table_gas (s : State) (continuation : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 10141, stack := frame continuation rho}
      {prepared s with pc := UInt256.ofNat 10496, stack := frame continuation rho} := by
  apply PadLift.gasSteps_of_raw tableSite
    {s with pc := UInt256.ofNat 10141, stack := frame continuation rho}
    {prepared s with pc := UInt256.ofNat 10496, stack := frame continuation rho}
    hc hf hr hnp table_pc.symm
  · apply PadLift.advancesAll_sound
    decide +kernel
  · exact table_run s continuation rho hs hr ha
def jumpTemplate : List Instr := [.push ⟨2,by decide⟩ (UInt256.ofNat 823), .op .JUMP]
def jumpSite : GenericRoundSite CandidateArtifact.artifact .Osaka jumpTemplate :=
  StackSiteBuilder.ofSlice jumpTemplate 7023 (by rfl)
    (by change 7023 + jumpTemplate.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem jump_pc : jumpSite.startPC = UInt256.ofNat 10496 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 7023) = UInt256.ofNat 10496
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
theorem valid_join : Decode.isValidJumpDest CandidateArtifact.artifact.code 823 = true := by
  have hpc : CandidateArtifact.artifact.instructionPC 348 = 823 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel
  have h := CandidateArtifact.artifact.isValidJumpDest_index 348 (by rfl)
  rw [hpc] at h
  exact h
def jump_gas (s : State) (rho : List UInt256) (hs : rho.length ≤ 990)
    (hr : s.halt = .Running) (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 10496, stack := rho} {s with pc := UInt256.ofNat 823, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 10496, stack := rho}
    {s with pc := UInt256.ofNat 823, stack := rho} hc hf hr hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hv : Decode.isValidJumpDest s.executionEnv.code 823 = true := by rw [hc]; exact valid_join
    simp [jumpTemplate, runInstrSeq, DataStepper.runInstr, hr, hv,
      show rho.length < 1024 by omega, show rho.length+1 < 1024 by omega]
def joinSite : GenericRoundSite CandidateArtifact.artifact .Osaka [.op .JUMPDEST] :=
  StackSiteBuilder.ofSlice [.op .JUMPDEST] 348 (by rfl)
    (by change 348 + 1 ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide)) (by decide)
theorem join_pc : joinSite.startPC = UInt256.ofNat 823 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 348) = UInt256.ofNat 823
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def join_gas (s : State) (rho : List UInt256) (hs : rho.length ≤ 990)
    (hr : s.halt = .Running) (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 823, stack := rho} {s with pc := UInt256.ofNat 824, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 823, stack := rho}
    {s with pc := UInt256.ofNat 824, stack := rho} hc hf hr hnp join_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · simp [runInstrSeq, DataStepper.runInstr, hr, show rho.length < 1024 by omega]
    rfl
def gasSteps (s : State) (continuation : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 10141, stack := frame continuation rho}
      {prepared s with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 initialHash.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result (prepared s).memory initialHash) (UInt256.ofNat 1056) continuation (NormalPrepare.masks rho)} := by
  have hlen : (frame continuation rho).length ≤ 990 := by
    simp only [frame, StaggerPersistentFrame.frame, NormalPrepare.masks, List.length_append, List.length_cons, List.length_nil]
    omega
  exact (table_gas s continuation rho hs hr ha hc hf hnp).trans
    ((jump_gas (prepared s) (frame continuation rho) hlen hr hc hf hnp).trans
      ((join_gas (prepared s) (frame continuation rho) hlen hr hc hf hnp).trans
        (CoreGas.gasSteps (prepared s) initialHash (UInt256.ofNat 1056) continuation (NormalPrepare.masks rho)
          (by simp only [NormalPrepare.masks, List.length_cons]; omega) hr ha hc hf hnp)))
theorem ready (s : State)
    (hm : Matches s.memory FirstMemory.initial (FirstMemory.value s.memory)) :
    CoreMessage.Ready (prepared s).memory (GeneralMessageReady.entryWords s.memory) := by
  have h := FirstMessageReady.ready s 0 [] hm
  rw [FirstMemory.eq7] at h
  exact h
#print axioms gasSteps
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstCore

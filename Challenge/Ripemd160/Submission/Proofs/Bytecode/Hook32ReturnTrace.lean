import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Return
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32ReturnTrace
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Shared32Sites Hook32Return StackRoundTrace StackRoundTemplate

/-- MSTORE followed by RETURN reads exactly the freshly written 32 bytes,
regardless of the prior memory (including empty memory). -/
theorem returned_bytes (s : State) (stk : List UInt256) (value : UInt256) (pc : Nat) :
    (returned s stk value pc).hReturn = Data.Bytes.natToBytesPadded value.toNat 32 := by
  have hsize : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  change MachineState.readPadded (written s value) 0 32 = _
  have hr := Memory.readPadded_writeBytes_same s.memory
    (Data.Bytes.natToBytesPadded value.toNat 32) 0
  simpa only [hsize, written] using hr

namespace hit0
abbrev template : List Instr := stub0
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 5443).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 5443 actual_slice
    (by change 5443 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 9792 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 5443) = UInt256.ofNat 9792
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Exact artifact instructions, including the terminal RETURN, lifted to gas semantics. -/
def gas_stub (s : State) (e : Env s) (stk : List UInt256)
    (hlen : stk.length + 2 < 1024) :
    GasSteps (atState s 9792 stk) (returned s stk push0 9819) := by
  apply PadLift.gasSteps_of_raw site (atState s 9792 stk) (returned s stk push0 9819)
    e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact run_stub0 s e.run stk hlen

theorem returns_spec (s : State) (stk : List UInt256)
    (hsize : s.executionEnv.calldata.size = 32)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = Hook32.word0) :
    (returned s stk push0 9819).hReturn = spec s.executionEnv.calldata := by
  rw [returned_bytes, Hook32Digest.spec_eq_returnBytes_word0 _ hsize hhit]
  rfl
end hit0

namespace hit1
abbrev template : List Instr := stub1
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 5450).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 5450 actual_slice
    (by change 5450 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 9820 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 5450) = UInt256.ofNat 9820
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Exact artifact instructions, including the terminal RETURN, lifted to gas semantics. -/
def gas_stub (s : State) (e : Env s) (stk : List UInt256)
    (hlen : stk.length + 2 < 1024) :
    GasSteps (atState s 9820 stk) (returned s stk push1 9847) := by
  apply PadLift.gasSteps_of_raw site (atState s 9820 stk) (returned s stk push1 9847)
    e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact run_stub1 s e.run stk hlen

theorem returns_spec (s : State) (stk : List UInt256)
    (hsize : s.executionEnv.calldata.size = 32)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = Hook32.word1) :
    (returned s stk push1 9847).hReturn = spec s.executionEnv.calldata := by
  rw [returned_bytes, Hook32Digest.spec_eq_returnBytes_word1 _ hsize hhit]
  rfl
end hit1

namespace hit2
abbrev template : List Instr := stub2
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 5457).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 5457 actual_slice
    (by change 5457 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 9848 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 5457) = UInt256.ofNat 9848
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Exact artifact instructions, including the terminal RETURN, lifted to gas semantics. -/
def gas_stub (s : State) (e : Env s) (stk : List UInt256)
    (hlen : stk.length + 2 < 1024) :
    GasSteps (atState s 9848 stk) (returned s stk push2 9875) := by
  apply PadLift.gasSteps_of_raw site (atState s 9848 stk) (returned s stk push2 9875)
    e.code e.fork e.run e.np site_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact run_stub2 s e.run stk hlen

theorem returns_spec (s : State) (stk : List UInt256)
    (hsize : s.executionEnv.calldata.size = 32)
    (hhit : MachineState.readWord s.executionEnv.calldata 0 = Hook32.word2) :
    (returned s stk push2 9875).hReturn = spec s.executionEnv.calldata := by
  rw [returned_bytes, Hook32Digest.spec_eq_returnBytes_word2 _ hsize hhit]
  rfl
end hit2

#print axioms hit0.gas_stub
#print axioms hit1.gas_stub
#print axioms hit2.gas_stub
#print axioms hit0.returns_spec
#print axioms hit1.returns_spec
#print axioms hit2.returns_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32ReturnTrace

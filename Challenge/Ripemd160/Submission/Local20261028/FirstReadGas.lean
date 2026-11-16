import Challenge.Ripemd160.Submission.Local20261028.FirstRead
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstReadGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate RipemdMemoryBridge20261028
def template : List Instr :=
  (FirstRead.template ++ RipemdSubmission20261101.First0.templateA) ++ ReverseLiteralRaw.jumpTemplate 9983
def site : GenericRoundSite CandidateArtifact.artifact .Osaka template :=
  StackSiteBuilder.ofSlice template 4005 (by rfl)
    (by change 4005 + template.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem site_pc : site.startPC = UInt256.ofNat 6376 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 4005) = UInt256.ofNat 6376
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
theorem run (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (hcd : MachineState.readWord s.executionEnv.calldata 0 = MachineState.readWord s.memory 1056) :
    runInstrSeq template {s with pc := UInt256.ofNat 6376, stack := FirstCore.frame cont rho} =
      some (FirstCore.midState (FirstRead.result s) cont rho) := by
  have h1 := FirstRead.run s cont rho hs hr ha hcd
  have h2 := RipemdSubmission20261101.First0.runA (FirstRead.result s) (FirstCore.prefixArgs cont) rho
    (by omega) hr ha
  rw [FirstCore.frame_eq] at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 hr h2
  have h3 := ReverseLiteralRaw.run_jump
    {FirstRead.result s with memory := RipemdSubmission20261101.First0.midMemory (FirstRead.result s)}
    (UInt256.ofNat 6449) 9983
    (RipemdSubmission20261101.First0.midStack (FirstCore.prefixArgs cont) rho (FirstRead.result s))
    (by simp only [RipemdSubmission20261101.First0.midStack, RipemdSubmission20261101.First0.outputs,
          List.length_cons, List.length_append, List.length_nil]; omega)
    hr
    (by
      change Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 9983).toNat = true
      rw [hc]
      exact FirstCore.valid9983)
  exact DenseScheduleTrace.runInstrSeq_append_running h12 hr h3
def gasSteps (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcd : MachineState.readWord s.executionEnv.calldata 0 = MachineState.readWord s.memory 1056) :
    GasSteps {s with pc := UInt256.ofNat 6376, stack := FirstCore.frame cont rho}
      (FirstCore.midState (FirstRead.result s) cont rho) := by
  apply RecognitionLift.gasSteps_of_raw site {s with pc := UInt256.ofNat 6376, stack := FirstCore.frame cont rho}
    (FirstCore.midState (FirstRead.result s) cont rho)
    hc hf hr hnp site_pc.symm
  · apply RecognitionLift.advancesAll_sound
    decide +kernel
  · exact run s cont rho hs hr ha hc hcd
def complete (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcd : MachineState.readWord s.executionEnv.calldata 0 = MachineState.readWord s.memory 1056) :
    GasSteps {s with pc := UInt256.ofNat 6376, stack := FirstCore.frame cont rho}
      {FirstCore.prepared (FirstRead.result s) with pc := UInt256.ofNat 4622, stack := Word.ofUInt32 FirstCore.initialHash.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result (FirstCore.prepared (FirstRead.result s)).memory FirstCore.initialHash) (UInt256.ofNat 1056) cont (NormalPrepare.masks rho)} :=
  (gasSteps s cont rho hs hr ha hc hf hnp hcd).trans
    (FirstCore.gasSteps (FirstRead.result s) cont rho hs hr ha hc hf hnp)
theorem ready (s : State) (m : ByteArray)
    (hm : s.memory = PairedScheduleMemory.writeWord m 162 FirstInitial.highWord)
    (hz : ∀ a, a < 1056 → m[a]?.getD 0 = 0)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    CoreMessage.Ready (FirstCore.prepared (FirstRead.result s)).memory
      (GeneralMessageReady.entryWords (FirstRead.result s).memory) := by
  apply FirstCore.ready (FirstRead.result s) ?_ hc
  rw [FirstRead.memory_eq s m hm]
  exact FirstInitial.matches_initial m hz
#print axioms complete
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstReadGas

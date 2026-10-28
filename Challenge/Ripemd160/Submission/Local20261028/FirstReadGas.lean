import Challenge.Ripemd160.Submission.Local20261028.FirstRead
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstReadGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate RipemdMemoryBridge20261028
def site : GenericRoundSite CandidateArtifact.artifact .Osaka FirstRead.template :=
  StackSiteBuilder.ofSlice FirstRead.template 6898 (by rfl)
    (by change 6898 + FirstRead.template.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem site_pc : site.startPC = UInt256.ofNat 10108 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 6898) = UInt256.ofNat 10108
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def gasSteps (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 10108, stack := FirstCore.frame cont rho}
      {FirstRead.result s with pc := UInt256.ofNat 10141, stack := FirstCore.frame cont rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat 10108, stack := FirstCore.frame cont rho}
    {FirstRead.result s with pc := UInt256.ofNat 10141, stack := FirstCore.frame cont rho}
    hc hf hr hnp site_pc.symm
  · apply PadLift.advancesAll_sound
    decide +kernel
  · exact FirstRead.run s cont rho hs hr ha
def complete (s : State) (cont : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 10108, stack := FirstCore.frame cont rho}
      {FirstCore.prepared (FirstRead.result s) with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 FirstCore.initialHash.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result (FirstCore.prepared (FirstRead.result s)).memory FirstCore.initialHash) (UInt256.ofNat 1056) cont (NormalPrepare.masks rho)} :=
  (gasSteps s cont rho hs hr ha hc hf hnp).trans
    (FirstCore.gasSteps (FirstRead.result s) cont rho hs hr ha hc hf hnp)
theorem ready (s : State) (m : ByteArray)
    (hm : s.memory = PairedScheduleMemory.writeWord m 162 FirstInitial.highWord)
    (hz : ∀ a, a < 1056 → m[a]?.getD 0 = 0) :
    CoreMessage.Ready (FirstCore.prepared (FirstRead.result s)).memory
      (GeneralMessageReady.entryWords (FirstRead.result s).memory) := by
  apply FirstCore.ready
  rw [FirstRead.memory_eq s m hm]
  exact FirstInitial.matches_initial m hz
#print axioms complete
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstReadGas

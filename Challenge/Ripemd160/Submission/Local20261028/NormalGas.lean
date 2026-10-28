import Challenge.Ripemd160.Submission.Local20261028.NormalMessage
import Challenge.Ripemd160.Submission.Local20261028.CoreGas
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate NormalPrepare
theorem actual_slice :
    (CandidateArtifact.artifact.instructions.drop 159).take NormalPrepare.template.length = NormalPrepare.template := by rfl
def site : GenericRoundSite CandidateArtifact.artifact .Osaka NormalPrepare.template :=
  StackSiteBuilder.ofSlice NormalPrepare.template 159 actual_slice
    (by change 159 + NormalPrepare.template.length ≤ CandidateArtifact.instructions.length
        rw [CandidateArtifact.instruction_count]; decide +kernel)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide +kernel)) (by decide +kernel)
theorem site_pc : site.startPC = UInt256.ofNat 462 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 159) = UInt256.ofNat 462
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel
def prepare (s : State) (h : Compression.HashState) (p : Nat) (limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (hp : 1056 ≤ p) (hb : p+64 < 2^256)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      {s with pc := UInt256.ofNat 462, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)}
      {scheduled s p with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)} := by
  apply PadLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 462, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)}
    {scheduled s p with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)}
    hc hf hr hnp site_pc.symm
  · apply PadLift.advancesAll_sound
    decide +kernel
  · exact NormalPrepare.run s h p limit rho hs hr hp hb
def gasSteps (s : State) (h : Compression.HashState) (p : Nat) (limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (hp : 1056 ≤ p) (hb : p+64 < 2^256)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      {s with pc := UInt256.ofNat 462, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)}
      {scheduled s p with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (CoreFunctional.result (scheduled s p).memory h) (UInt256.ofNat p) limit (masks rho)} := by
  have gp := prepare s h p limit rho hs hr hp hb hc hf hnp
  have gc := CoreGas.gasSteps (scheduled s p) h (UInt256.ofNat p) limit (masks rho)
    (by simp only [masks, List.length_cons]; omega) hr
    (by have h := Stagger144Active.loaded_active_ge35 s p hp hb; exact Nat.le_trans (by decide) h)
    hc hf hnp
  exact gp.trans gc

theorem correct_block (s : State) (h : Compression.HashState) (p : Nat) (limit : UInt256) (rho : List UInt256)
    (bs : ByteArray) (off : Nat)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (hp : 1056 ≤ p) (hb : p+64 < 2^256)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hz : Clear s.memory) (hm : ScheduleCorrect.MessageBlockAt s.memory (UInt256.ofNat p) bs off) :
    ∃ h' : Compression.HashState,
      Nonempty (GasSteps
        {s with pc := UInt256.ofNat 462, stack := StaggerPersistentFrame.frame h (UInt256.ofNat p) limit (masks rho)}
        {scheduled s p with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame h' (UInt256.ofNat p) limit (masks rho)}) ∧
      CompressionCorrect.hashArray h' = Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs off ∧
      Clear (scheduled s p).memory ∧
      (∀ a, 1040 ≤ a → (scheduled s p).memory[a]?.getD 0 = s.memory[a]?.getD 0) :=
  ⟨CoreFunctional.result (scheduled s p).memory h,
    ⟨gasSteps s h p limit rho hs hr hp hb hc hf hnp⟩,
    NormalMessage.result_compressBlock s p bs off h hb hz hm,
    NormalPrepare.clear s p hz, NormalPrepare.outside s p⟩
#print axioms prepare
#print axioms gasSteps
#print axioms correct_block
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalGas

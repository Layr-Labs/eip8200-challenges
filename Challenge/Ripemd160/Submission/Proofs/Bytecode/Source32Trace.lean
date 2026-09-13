import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Physical
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32CallerFacts
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCorrect
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Correct
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerFunctional StaggerPersistentFrame

def maskRho : List UInt256 := [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
def sourceState (input : ByteArray) : State := PaddingTrace.source32Returned input

def tableState (input : ByteArray) : State :=
  {sourceState input with memory := Source32Physical.resultMemory (sourceState input).memory}

def finalHash (input : ByteArray) : Compression.HashState :=
  PersistentStaggerFunctional.result (tableState input).memory StackRunBridge.initialHashState

def result (input : ByteArray) : State :=
  StaggerPersistentSerialize.result (tableState input) (finalHash input)
    (UInt256.ofNat 64) (UInt256.ofNat 64) maskRho

theorem paddedWord (input : ByteArray) (hfit : CalldataFits input) (h32 : input.size = 32) :
    Padding.paddedWord input = UInt256.ofNat 64 := by
  rw [Padding.paddedWord_eq input hfit]
  simp [Padding.paddedLength, h32]

theorem blockCount (input : ByteArray) (h32 : input.size = 32) :
    DriverTrace.blockCount input = 1 := by
  simp [DriverTrace.blockCount, Padding.paddedLength, h32]

noncomputable def fullTrace (input : ByteArray) (hfit : CalldataFits input) (h32 : input.size = 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 353)) :
    GasSteps (initialState submissionBytecode input 0) (result input) := by
  let s := sourceState input
  let q := tableState input
  let h := StackRunBridge.initialHashState
  have hs : s = {s with pc := UInt256.ofNat 391, stack := UInt256.ofNat 64 :: maskRho} := by
    dsimp only [s, sourceState, PaddingTrace.source32Returned, PaddingTrace.padFrame, maskRho]
    rw [paddedWord input hfit h32]
  have ha : s.activeWords = UInt256.ofNat 36 := PaddingTrace.source32_active input h32
  have har : 35 ≤ s.activeWords.toNat := by rw [ha]; decide
  have hr : s.halt = .Running := rfl
  have hc : s.executionEnv.code = Artifact.submissionArtifact.code := rfl
  have hf : s.fork = .Osaka := rfl
  have hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := deployAddress_not_precompile
  have g0 := PaddingTrace.gasSteps_source32 input hfit h32 entryPrefix
  have g1 := StaggerPersistentStart.gasSteps_push s (UInt256.ofNat 64) maskRho
    (by decide) hr hc hf hn
  rw [← hs] at g1
  have hflag : MachineState.readWord s.memory 32 = UInt256.ofNat 128 :=
    Source32Memory.read32 _
  have g2 := Source32Entry.gasSteps_dispatch_hit s
    (frame h (UInt256.ofNat 0) (UInt256.ofNat 64) maskRho)
    (by simp [frame, maskRho]) hr (by omega) hflag hc hf hn
  have hloaded : DenseScheduleTemplate.activeAfterWord s.activeWords (UInt256.ofNat 1120) = s.activeWords := by
    rw [ha]
    decide
  have g3 := Source32Physical.gasSteps_source s h (UInt256.ofNat 64) hr har hloaded hc hf hn
  have hrq : q.halt = .Running := rfl
  have hcq : q.executionEnv.code = Artifact.submissionArtifact.code := rfl
  have hfq : q.fork = .Osaka := rfl
  have hnq : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := deployAddress_not_precompile
  have haq : 35 ≤ q.activeWords.toNat := har
  have gb := StaggerPersistentBootstrapBridge.gasSteps_body q h (UInt256.ofNat 0)
    (UInt256.ofNat 64) maskRho (by decide) hrq haq hcq hfq hnq
  have gt := PersistentStaggerTailBridge.gasSteps q h
    (StaggerCoreModel.paired q.memory (initial h)) (UInt256.ofNat 0) (UInt256.ofNat 64)
    maskRho (by decide) hrq hcq hfq hnq
  have hrest : StaggerPersistentPackBridge.suffix (initial h) (UInt256.ofNat 0)
      (UInt256.ofNat 64) maskRho = coreRest h (UInt256.ofNat 0) (UInt256.ofNat 64) maskRho := by
    change StaggerPersistentPackBridge.suffix (StaggerPersistentBootstrapBridge.initial h) _ _ _ = _
    rw [StaggerPersistentBootstrapBridge.initial_eq]
    rfl
  have he : (initial h).e = Word.ofUInt32 h.h4 := by
    change (StaggerPersistentBootstrapBridge.initial h).e = _
    rw [StaggerPersistentBootstrapBridge.initial_eq]
  rw [he, hrest] at gt
  have gx := StaggerPersistentLoopSites.gasSteps_exit q (finalHash input)
    (UInt256.ofNat 0) (UInt256.ofNat 64) maskRho (by decide) hrq (by decide)
    (Nat.lt_trans hfit (by decide)) (by change input.size ≠ _; rw [h32]; decide) hcq hfq hnq
  have hnxt : StaggerPersistentLoopRaw.nextOffset (UInt256.ofNat 0) = UInt256.ofNat 64 := by decide
  rw [hnxt] at gx
  have go := StaggerPersistentSerialize.gasSteps q (UInt256.ofNat 64) (UInt256.ofNat 64)
    (finalHash input) [] (by decide) hrq hcq hfq hnq
  exact g0.trans (g1.trans (g2.trans (g3.trans (gb.trans (gt.trans (gx.trans go))))))


#print axioms fullTrace
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Correct

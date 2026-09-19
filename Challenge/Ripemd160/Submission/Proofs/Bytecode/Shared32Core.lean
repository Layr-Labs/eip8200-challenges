import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Sites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerializeMath
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Core
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Shared32Sites
namespace Functional
abbrev initial := PersistentStaggerFunctional.initial
abbrev result := PersistentStaggerFunctional.result
end Functional

def maskRho : List UInt256 := [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

/-- The resident compression body is independent of the message-copy and padding setup. -/
def gasSteps_body (s : State) (e : Env s) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) (hstack : rho.length ≤ 894)
    (hactive : 35 ≤ s.activeWords.toNat) :
    GasSteps
      {s with pc := UInt256.ofNat 859, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with
        pc := UInt256.ofNat 4625
        stack := StaggerPersistentFrame.frame (Functional.result s.memory h) off limit rho} := by
  have gb := StaggerPersistentBootstrapBridge.gasSteps_body s h off limit rho
    hstack e.run hactive e.code e.fork e.np
  have gt := PersistentStaggerTailBridge.gasSteps s h
    (StaggerCoreModel.paired s.memory (Functional.initial h)) off limit rho
    (by omega) e.run e.code e.fork e.np
  have he : (PersistentStaggerFunctional.initial h).e = Word.ofUInt32 h.h4 := by
    rw [PersistentStaggerTailBridge.initial_eq]
  have hsuffix : StaggerPersistentPackBridge.suffix
      (PersistentStaggerFunctional.initial h) off limit rho =
      StaggerPersistentFrame.coreRest h off limit rho := by
    rw [PersistentStaggerTailBridge.initial_eq]
    rfl
  rw [he, hsuffix] at gt
  exact gb.trans gt

def entryState (s : State) : State :=
  {s with
    pc := UInt256.ofNat 859
    stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState
      (UInt256.ofNat 0) (UInt256.ofNat 32) maskRho}

def resultHash (s : State) : Compression.HashState :=
  Functional.result s.memory StackRunBridge.initialHashState

def resultState (s : State) : State :=
  StaggerPersistentSerialize.result s (resultHash s)
    (UInt256.ofNat 64) (UInt256.ofNat 32) maskRho

def gasSteps (s : State) (e : Env s) (input : ByteArray)
    (hcal : s.executionEnv.calldata = input) (h32 : input.size = 32)
    (hactive : s.activeWords = UInt256.ofNat 35) :
    GasSteps (entryState s) (resultState s) := by
  have gb := gasSteps_body s e StackRunBridge.initialHashState
    (UInt256.ofNat 0) (UInt256.ofNat 32) maskRho (by decide)
    (by rw [hactive]; decide)
  have ge := StaggerPersistentLoopSites.gasSteps_exit s (resultHash s)
    (UInt256.ofNat 0) (UInt256.ofNat 32) maskRho (by decide) e.run
    (by decide) (by rw [hcal, h32]; decide) (by rw [hcal, h32]; decide)
    e.code e.fork e.np
  have go := StaggerPersistentSerialize.gasSteps s (UInt256.ofNat 64) (UInt256.ofNat 32)
    (resultHash s) [] (by decide) e.run e.code e.fork e.np
  have hoff : StaggerPersistentLoopRaw.nextOffset (UInt256.ofNat 0) = UInt256.ofNat 64 := by decide
  rw [hoff] at ge
  exact gb.trans (ge.trans go)

theorem blockCount32 (input : ByteArray) (h32 : input.size = 32) :
    DriverTrace.blockCount input = 1 := by
  simp [DriverTrace.blockCount, Padding.paddedLength, h32]

theorem resultHash_spec (s : State) (input : ByteArray) (h32 : input.size = 32)
    (hready : StaggerMessage.Ready s.memory
      (fun k => (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]!)) :
    CompressionCorrect.hashArray (resultHash s) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input) := by
  have hf := PersistentStaggerFunctional.result_compressBlock s.memory
    (Padding.paddedMessage input) 0 StackRunBridge.initialHashState hready
  have hzero : CompressionCorrect.hashArray StackRunBridge.initialHashState =
      CompressionSeamBridge.hashAfter input 0 := by rfl
  rw [hzero] at hf
  rw [blockCount32 input h32, show (1 : Nat) = 0 + 1 by rfl,
    StackRunBridge.hashAfter_succ]
  exact hf

theorem returned_spec (s : State) (input : ByteArray) (h32 : input.size = 32)
    (hready : StaggerMessage.Ready s.memory
      (fun k => (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]!)) :
    (resultState s).hReturn = spec input :=
  StaggerPersistentSerialize.returned_spec_of_hashArray s input
    (UInt256.ofNat 64) (UInt256.ofNat 32) maskRho (resultHash s)
    (resultHash_spec s input h32 hready)

@[simp] theorem resultState_halt (s : State) : (resultState s).halt = .Returned := rfl
@[simp] theorem resultState_callStack (s : State) : (resultState s).callStack = s.callStack := rfl

#print axioms gasSteps_body
#print axioms gasSteps
#print axioms returned_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Core

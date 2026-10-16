import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreLeft79
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapBridge
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open PersistentStaggerFunctional

def tailInput (memory : ByteArray) (h : Compression.HashState) (l r : WordLane)
    (off limit : UInt256) : StaggerPersistentTailRaw.Input :=
  {ld := l.d, lb := l.b, le := l.e, la := l.a, k := UInt256.ofNat 2840853838,
   lc := l.c, re := r.e, rc := r.c, ra := r.a, rd := r.d, rb := r.b,
   factor := factorPlusWord, lower := UInt256.ofNat 4294967295,
   cache140 := fusedModulusWord 5 7, cache190 := fusedCoefficientWord 0 2,
   cache310 := fusedCoefficientWord 0 3, cache350 := fusedModulusWord 8 5,
   literal72 := MachineState.readWord memory 360, literal28 := UInt256.ofNat 28,
   h4 := Word.ofUInt32 h.h4, h1 := Word.ofUInt32 h.h1, h2 := Word.ofUInt32 h.h2,
   h3 := Word.ofUInt32 h.h3, h0 := Word.ofUInt32 h.h0, off := off, limit := limit}

theorem combine_eq (memory : ByteArray) (h : Compression.HashState) (q r : WordLane)
    (off limit : UInt256) :
    StaggerPersistentFrame.combine h (tailInput memory h (StaggerCoreLeft79.epilogueRaw memory q) r off limit) =
      combine h (StaggerCoreModel.epilogue memory q) r := by
  simp only [StaggerPersistentFrame.combine, tailInput, combine,
    PairedCompressionBridge.combineLanes, Paired80Compression.unpackLeft,
    StaggerFinalMemory.unpackRight, StaggerPersistentFrame.high,
    StaggerFinalMemory.high32, Paired80Compression.low32, Word.toUInt32, StaggerCoreLeft79.epilogueRaw, StaggerCoreModel.epilogue, StaggerCoreLeft79.left79Raw_a, StaggerCoreLeft79.left79Raw_b, StaggerCoreLeft79.left79Raw_c, StaggerCoreLeft79.left79Raw_e, StaggerCoreLeft79.left79Raw_d_shift]
  congr 1 <;> apply UInt32.eq_of_toBitVec_eq <;>
    simp only [UInt32.toBitVec_add] <;> ac_rfl

theorem initial_eq (h : Compression.HashState) :
    initial h = (⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
      Word.ofUInt32 h.h3, Word.ofUInt32 h.h4⟩ : WordLane) := StaggerPersistentBootstrapBridge.initial_eq h

theorem suffix_eq (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) :
    StaggerCore.suffixState s (initial h).e q
      (StaggerPersistentPackBridge.suffix (initial h) off limit rho) =
    {s with pc := UInt256.ofNat 4490, stack := StaggerPersistentTailRaw.entryStack (StaggerPersistentFrame.bind h
        (tailInput s.memory h (StaggerCoreLeft79.epilogueRaw s.memory q) q off limit)) rho} := by
  rw [initial_eq]
  rfl

/-- The block-exit stack (4537) for lanes `q`: the `h3` sum and the two `h2` addends on top, the
`h4`, `h1` and `h0` words masked in their slots and the continuation in slot 16. -/
def preStackQ (memory : ByteArray) (h : Compression.HashState) (q : WordLane)
    (off cont : UInt256) (rho : List UInt256) : List UInt256 :=
  ScheduledTailRaw.stack3a (ScheduledTailFrame.bind h (ScheduledTailBridge.fromCurrent
    (tailInput memory h (StaggerCoreLeft79.epilogueRaw memory q) q off cont))) rho

/-- The tail input of the block exit for a block run on `memory` from hash `h`. -/
def exitQ (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256) : ScheduledTailRaw.Input :=
  ScheduledTailBridge.fromCurrent (tailInput memory h
    (StaggerCoreLeft79.epilogueRaw memory (StaggerCoreModel.paired memory (initial h)))
    (StaggerCoreModel.paired memory (initial h)) off cont)

/-- The block-exit stack of a block run on `memory` from hash `h`. -/
def preStack (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) : List UInt256 :=
  preStackQ memory h (StaggerCoreModel.paired memory (initial h)) off cont rho

/-- The resident tail stops at the block exit with the continuation still in slot 16. -/
def gasSteps (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 980)
    (hr : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (StaggerCore.suffixState s (initial h).e q
      (StaggerPersistentPackBridge.suffix (initial h) off limit rho))
      {s with pc := UInt256.ofNat 4537, stack := preStackQ s.memory h q off limit rho} := by
  rw [suffix_eq]
  exact StaggerPersistentTailSite.gasSteps s off limit h
    (tailInput s.memory h (StaggerCoreLeft79.epilogueRaw s.memory q) q off limit)
    rho hs hr hcode hfork hnp

/-- The loop targets' tail copy completes the block: the combined frame, continuation kept. -/
theorem run_copy (s : State) (pc : UInt256) (memory : ByteArray) (h : Compression.HashState)
    (off cont : UInt256) (rho : List UInt256) (hs : rho.length ≤ 980) (hr : s.halt = .Running) :
    StackRoundTrace.runInstrSeq ScheduledTailFrame.copyTemplate
      {s with pc := pc, stack := preStack memory h off cont rho} =
      some {s with
        pc := StackRoundTrace.pcAfter pc ScheduledTailFrame.copyTemplate
        stack := StaggerPersistentFrame.frame (PersistentStaggerFunctional.result memory h) off cont rho} := by
  have g := ScheduledTailFrame.run_copy s pc h (ScheduledTailBridge.fromCurrent
    (tailInput memory h (StaggerCoreLeft79.epilogueRaw memory (StaggerCoreModel.paired memory (initial h)))
      (StaggerCoreModel.paired memory (initial h)) off cont)) rho hs hr
  rw [ScheduledTailBridge.combine_current, combine_eq] at g
  exact g

/-- The hash the exit stack completes to, in the epilogue's terms. -/
theorem result_eq (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256) :
    ScheduledTailFrame.combine h (ScheduledTailBridge.fromCurrent
      (tailInput memory h (StaggerCoreLeft79.epilogueRaw memory (StaggerCoreModel.paired memory (initial h)))
        (StaggerCoreModel.paired memory (initial h)) off cont)) =
      PersistentStaggerFunctional.result memory h := by
  rw [ScheduledTailBridge.combine_current, combine_eq]
  rfl

#print axioms combine_eq
#print axioms gasSteps
#print axioms run_copy
#print axioms result_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge

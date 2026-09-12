import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapBridge
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired80WordRound
open PersistentStaggerFunctional

def tailInput (memory : ByteArray) (h : Compression.HashState) (l r : WordLane)
    (off limit : UInt256) : StaggerPersistentTailRaw.Input :=
  {ld := l.d, lb := l.b, le := l.e, la := l.a, k := UInt256.ofNat 2840853838,
   lc := l.c, re := r.e, rc := r.c, ra := r.a, rd := r.d, rb := r.b,
   factor := UInt256.ofNat 4294967297, lower := UInt256.ofNat 4294967295,
   cache140 := MachineState.readWord memory 140, cache190 := MachineState.readWord memory 190,
   cache310 := MachineState.readWord memory 310, cache350 := MachineState.readWord memory 350,
   h4 := Word.ofUInt32 h.h4, h1 := Word.ofUInt32 h.h1, h2 := Word.ofUInt32 h.h2,
   h3 := Word.ofUInt32 h.h3, h0 := Word.ofUInt32 h.h0, off := off, limit := limit}

theorem combine_eq (memory : ByteArray) (h : Compression.HashState) (l r : WordLane)
    (off limit : UInt256) :
    StaggerPersistentFrame.combine h (tailInput memory h l r off limit) = combine h l r := by
  simp only [StaggerPersistentFrame.combine, tailInput, combine,
    PairedCompressionBridge.combineLanes, Paired80Compression.unpackLeft,
    Paired80Compression.unpackRight, StaggerPersistentFrame.high,
    Paired80Compression.high32, Paired80Compression.low32, Word.toUInt32]
  congr 1 <;> apply UInt32.eq_of_toBitVec_eq <;>
    simp only [UInt32.toBitVec_add] <;> ac_rfl

theorem initial_eq (h : Compression.HashState) :
    initial h = (⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
      Word.ofUInt32 h.h3, Word.ofUInt32 h.h4⟩ : WordLane) := StaggerPersistentBootstrapBridge.initial_eq h

theorem suffix_eq (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) :
    StaggerCore.suffixState s (initial h).e q
      (StaggerPersistentPackBridge.suffix (initial h) off limit rho) =
    {s with pc := UInt256.ofNat 4555, stack := StaggerPersistentTailRaw.stack0 (StaggerPersistentFrame.bind h
        (tailInput s.memory h (StaggerCoreModel.epilogue s.memory q) q off limit)) rho} := by
  rw [initial_eq]
  rfl

def gasSteps (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 980)
    (hr : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (StaggerCore.suffixState s (initial h).e q
      (StaggerPersistentPackBridge.suffix (initial h) off limit rho))
      {s with pc := UInt256.ofNat 471, stack := StaggerPersistentFrame.frame (combine h (StaggerCoreModel.epilogue s.memory q) q) off limit rho} := by
  rw [suffix_eq]
  have g := StaggerPersistentTailSite.gasSteps s off limit h
    (tailInput s.memory h (StaggerCoreModel.epilogue s.memory q) q off limit)
    rho hs hr hcode hfork hnp
  rw [combine_eq] at g
  exact g

#print axioms combine_eq
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge

import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCoreRight
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRepresentation
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapBridge
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound Paired144WordRotation StaggerCoreCommon

def initial (h : Compression.HashState) : WordLane :=
  StaggerScalarWord.embed (StaggerRepresentation.initialCrypto h)

theorem initial_eq (h : Compression.HashState) :
    initial h = (⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
      Word.ofUInt32 h.h3, Word.ofUInt32 h.h4⟩ : WordLane) := by
  simp only [StaggerRepresentation.word_ofUInt32]
  rfl

def input (h : Compression.HashState) (off limit : UInt256) :
    StaggerPersistentBootstrapRaw.Input :=
  ⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
    Word.ofUInt32 h.h3, Word.ofUInt32 h.h4, off, limit⟩

def entry (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 1130, stack := StaggerPersistentFrame.frame h off limit rho}

theorem input_eq (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) :
    StaggerPersistentBootstrapRaw.inputStack (input h off limit) rho =
      StaggerPersistentFrame.frame h off limit rho := by
  simp only [StaggerPersistentBootstrapRaw.inputStack, input, StaggerPersistentFrame.frame,
    StaggerPersistentBootstrapRaw.factorWord_eq, StaggerPersistentBootstrapRaw.fusedMinus_eq,
    StaggerPersistentBootstrapRaw.coefficient30_eq, StaggerPersistentBootstrapRaw.coefficient03_eq,
    StaggerPersistentBootstrapRaw.coefficient02_eq]

theorem output_eq (memory : ByteArray) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) :
    StaggerPersistentBootstrapRaw.outputStack memory (input h off limit) rho =
      stack memory (Word.ofUInt32 h.h4)
        [.factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .e]
        (initial h) (initial h) (UInt256.ofNat 1352829926)
        (StaggerPersistentFrame.coreRest h off limit rho) := by
  have hf : factorPlusWord = UInt256.ofNat 158456325065422163343096938498 := by decide
  have h140 : fusedModulusWord 5 7 = UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096 := by decide
  have h190 : fusedCoefficientWord 0 2 = UInt256.ofNat 475368975196266490007815979009 := by decide
  have h310 : fusedCoefficientWord 0 3 = UInt256.ofNat 1109194275457955143345843994625 := by decide
  have h350 : fusedModulusWord 8 5 = UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928 := by decide
  have hm : lowerWord = UInt256.ofNat 4294967295 := by decide
  simp [StaggerPersistentBootstrapRaw.outputStack, StaggerPersistentBootstrapRaw.inputStack, input, stack, StaggerCoreCommon.word,
    initial_eq, StaggerPersistentFrame.coreRest, hf, hm, h140, h190, h310, h350]

def gasSteps (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 900) (hr : s.halt = .Running)
    (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s h off limit rho)
      (StaggerPersistentCoreRight.initialState s (Word.ofUInt32 h.h4) (initial h)
        (StaggerPersistentFrame.coreRest h off limit rho)) := by
  have g := StaggerPersistentBootstrapSite.gasSteps s (input h off limit) rho hs hr ha hcode hfork hnp
  rw [input_eq, output_eq] at g
  exact g

#print axioms initial_eq
#print axioms output_eq
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapBridge

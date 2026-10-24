import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopRouting
import Challenge.Modexp.Submission.Proofs.CRT.FinalProductBridge
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 100000
set_option maxRecDepth 40000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTLoopComplete
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.PureLoop HistoricalSearch.LoopInvariant
open HistoricalSearch.CRTLoopInduction HistoricalSearch.CRTLoopOperations HistoricalSearch.CRTLoopRouting

attribute [local irreducible] ColumnSequence.states PureLoop.raw PureLoop.checked PureLoop.finish

variable (s : State) (minv : UInt256) (n : Nat → UInt256) (N : Nat)

noncomputable def advance
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (k : Nat) (mem : ByteArray)
    (f : CRTLoopFrames.Frame) (A : Nat) (hk : 1 ≤ k)
    (hcap : f.rest.length ≤ 982) (h : Invariant mem n minv f N (k+1) A) :
    GasSteps (atCache s mem 5859 n minv f)
      (atCache s (next s minv n k mem) 5859 n minv (nextFrame s minv n k mem f)) := by
  by_cases hlt : Q s minv n mem < R
  · exact direct s minv n mem f N k A env hcap hact hk h hlt
  · have g1 := checkedRound s minv n mem f N (k+1) A env hcap hact h
    rw [if_neg hlt] at g1
    have g2 := CRTGasStepsNormalized.handlerCount s (checked s minv n mem) n minv f env hcap hact
    have hc : (MachineState.readWord (checked s minv n mem) 1728).toNat ≠ 0 := by
      rw [checked_counter, h.counter]
      omega
    rw [if_neg hc] at g2
    have g3 := CRTGasStepsNormalized.handlerBody s (checked s minv n mem) n minv f env hcap hact
    have g := (g1.trans g2).trans g3
    simpa only [next, nextFrame, if_neg hlt] using g

#print axioms advance

noncomputable def lastProduct
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (mem : ByteArray) (f : CRTLoopFrames.Frame) (A : Nat)
    (hcap : f.rest.length ≤ 982) (h : Invariant mem n minv f N 1 A) :
    GasSteps (atOld s (finish s minv n mem) 3256 (UInt256.ofNat 0)
        (UInt256.ofNat (2^256-256)) (UInt256.ofNat 3643) (lastFrame s minv n mem f))
      (finished s (finish s minv n mem) f) := by
  let f' := lastFrame s minv n mem f
  have hf : Invariant mem n minv f' N 1 A := h.flow
    (CRTAdapterMeaning.cachedTop (checked s minv n mem)) CiosCached.allOnes f.ret f.rest
  have g := FinalProductBridge.round_product s minv n mem f' N 1 A
    (UInt256.ofNat 0) (UInt256.ofNat (2^256-256)) (UInt256.ofNat 3643) hf
    (by exact le_trans hcap (by decide)) env.running env.code env.forkEq env.noPrecompile hact hcds
  exact g

#print axioms lastProduct

noncomputable def last
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (mem : ByteArray) (f : CRTLoopFrames.Frame) (A : Nat)
    (hcap : f.rest.length ≤ 982) (h : Invariant mem n minv f N 1 A) :
    GasSteps (atCache s mem 5859 n minv f)
      (finished s (finish s minv n mem) f) := by
  have g1 := lastExit s minv n mem f N A env hcap hact h
  have g2 := lastTail s minv n mem f N A env hcap hact h
  have g3 := lastProduct s minv n N env hact hcds mem f A hcap h
  exact (g1.trans g2).trans g3

#print axioms last

noncomputable def operations
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256) :
    Operations s minv n N where
  advance := advance s minv n N env hact
  last := last s minv n N env hact hcds

/-- Concrete retained loop: every direct/overflow-handler branch is linked to the
installed instructions, then the existing final mixed product returns to690. -/
noncomputable def run
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (k : Nat) (mem : ByteArray) (f : CRTLoopFrames.Frame) (A : Nat)
    (hcap : f.rest.length ≤ 982) (h : Invariant mem n minv f N k A) :
    GasSteps (atCache s mem 5859 n minv f)
      (finished s (memory s minv n k mem) f) :=
  CRTLoopInduction.run s minv n N (operations s minv n N env hact hcds) k mem f A hcap h

#print axioms operations
#print axioms run
end HistoricalSearch.CRTLoopComplete

import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopOperations
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTLoopRouting
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.CRTLoopArithmetic
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.PureLoop
open HistoricalSearch.LoopInvariant HistoricalSearch.CRTLoopInduction
open HistoricalSearch.CRTLoopOperations

variable (s : State) (minv : UInt256) (n : Nat → UInt256)

def direct (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (hk : 1 ≤ k) (h : Invariant mem n minv f N (k+1) A)
    (hlt : Q s minv n mem < R) :
    GasSteps (atCache s mem 5859 n minv f)
      (atCache s (next s minv n k mem) 5859 n minv (nextFrame s minv n k mem f)) := by
  have g1 := checkedRound s minv n mem f N (k+1) A env hcap hact h
  rw [if_pos hlt] at g1
  have g2 := CRTGasStepsNormalized.count s (checked s minv n mem) n minv f env hcap hact
  have hc : (MachineState.readWord (checked s minv n mem) 1728).toNat ≠ 0 := by
    rw [checked_counter, h.counter]
    omega
  rw [if_neg hc] at g2
  have g3 := CRTGasStepsNormalized.retain s (checked s minv n mem) n minv f env hcap hact
  simpa only [next, nextFrame, if_pos hlt] using (g1.trans g2).trans g3

def lastExit (mem : ByteArray) (f : CRTLoopFrames.Frame) (N A : Nat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (h : Invariant mem n minv f N 1 A) :
    GasSteps (atCache s mem 5859 n minv f)
      (atCache s (checked s minv n mem) 8800 n minv f) := by
  have g1 := checkedRound s minv n mem f N 1 A env hcap hact h
  by_cases hlt : Q s minv n mem < R
  · rw [if_pos hlt] at g1
    have g2 := CRTGasStepsNormalized.count s (checked s minv n mem) n minv f env hcap hact
    have hc : (MachineState.readWord (checked s minv n mem) 1728).toNat = 0 := by
      rw [checked_counter, h.counter]
    rw [if_pos hc] at g2
    exact g1.trans g2
  · rw [if_neg hlt] at g1
    have g2 := CRTGasStepsNormalized.handlerCount s (checked s minv n mem) n minv f env hcap hact
    have hc : (MachineState.readWord (checked s minv n mem) 1728).toNat = 0 := by
      rw [checked_counter, h.counter]
    rw [if_pos hc] at g2
    exact g1.trans g2

def lastFrame (mem : ByteArray) (f : CRTLoopFrames.Frame) : CRTLoopFrames.Frame :=
  {f with aprev := cachedTop (checked s minv n mem), counter := CiosCached.allOnes}

def lastTail (mem : ByteArray) (f : CRTLoopFrames.Frame) (N A : Nat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (h : Invariant mem n minv f N 1 A) :
    GasSteps (atCache s (checked s minv n mem) 8800 n minv f)
      (atOld s (finish s minv n mem) 3256 (UInt256.ofNat 0)
        (UInt256.ofNat (2^256-256)) (UInt256.ofNat 3643) (lastFrame s minv n mem f)) := by
  let E := exitMemory (checked s minv n mem)
  let flag := UInt256.ofNat (Q s minv n mem / R)
  have hE := h.toStatic.transport (exit_live s minv n mem)
  have hF := h.toStatic.transport (finish_live s minv n mem)
  have ge := CRTGasStepsNormalized.exit s (checked s minv n mem) n minv f env hcap hact
  have gt := CRTExitTail.gasSteps_last s E flag f.w3 (UInt256.ofNat 3643) f.tl f.inv
    f.m0 f.m96 f.m64 f.m32 (cachedTop (checked s minv n mem)) f.ret f.rest hcap
    env.running env.code env.forkEq env.noPrecompile hact hE.s32
  have he : CRTExitTail.memory E flag = finish s minv n mem := rfl
  have hs : atOld s E 3942 flag (UInt256.ofNat 0) (UInt256.ofNat 3643)
      (exitFrame (checked s minv n mem) f) =
      TnM128SquareExit.frameAt flag (MachineState.readWord E 128) 3942 s E 8
        (UInt256.ofNat 0) f.w3 (UInt256.ofNat 3643) f.tl f.inv f.m0 f.m96 f.m64 f.m32
        (cachedTop (checked s minv n mem)) (UInt256.ofNat 0) f.ret f.rest := by
    unfold atOld exitFrame
    rw [counter_word s minv n mem f N 1 A h, hE.m128]
  rw [flag_word s minv n mem f N 1 A h] at ge
  have g := ge.trans (gt.cast hs.symm rfl)
  rw [he, hF.m128] at g
  exact g

#print axioms direct
#print axioms lastExit
#print axioms lastTail
end HistoricalSearch.CRTLoopRouting

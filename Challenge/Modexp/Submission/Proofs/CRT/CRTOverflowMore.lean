import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopOperations
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace HistoricalSearch.CRTOverflowMore
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.CRTLoopFrames HistoricalSearch.CRTLoopArithmetic
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.PureLoop
open HistoricalSearch.LoopInvariant HistoricalSearch.CRTLoopOperations

/-- At the exit branch with another square remaining, the original tail
normalizes the output and reenters the mixed representation. This trace is
valid for either overflow flag; the loop uses it on the overflow branch. -/
def gasSteps (s : State) (minv : UInt256) (n : Nat → UInt256)
    (mem : ByteArray) (f : CRTLoopFrames.Frame) (N k A : Nat)
    (hk : 1 ≤ k) (h : Invariant mem n minv f N (k+1) A)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (atCache s (checked s minv n mem) 8800 n minv f)
      (atCache s (entryMemory (finish s minv n mem) (UInt256.ofNat (k-1))) 5859 n minv
        {f with aprev := cachedTop (checked s minv n mem), counter := UInt256.ofNat (k-1)}) := by
  let cm := checked s minv n mem
  let em := exitMemory cm
  let tn := UInt256.ofNat (Q s minv n mem / R)
  let fn : CRTLoopFrames.Frame :=
    {f with aprev := cachedTop cm, counter := UInt256.ofNat (k-1)}
  have he := h.toStatic.transport (exit_live s minv n mem)
  have hf := h.toStatic.transport (finish_live s minv n mem)
  have hflag : MachineState.readWord cm 1760 = tn := flag_word s minv n mem f N (k+1) A h
  have hcount : MachineState.readWord cm 1728 = UInt256.ofNat k := by
    simpa only [Nat.add_sub_cancel] using counter_word s minv n mem f N (k+1) A h
  have hc : k-1+1 = k := by omega
  have hbound : k-1+1 ≤ 15 := by have hb := h.countBound; omega
  have hmem : CRTExitTail.memory em tn = finish s minv n mem := rfl
  have g0 := CRTGasStepsNormalized.exit s cm n minv f env hcap hact
  have g1 := CRTExitTail.gasSteps_more s em tn (k-1) f.w3 (UInt256.ofNat 3643)
    f.tl f.inv f.m0 f.m96 f.m64 f.m32 (cachedTop cm) f.ret f.rest
    hcap env.running env.code env.forkEq env.noPrecompile hact he.s32 hbound
  have hstart :
      atOld s em 3942 (MachineState.readWord cm 1760) (UInt256.ofNat 0)
        (UInt256.ofNat 3643) (exitFrame cm f) =
      TnM128SquareExit.frameAt tn (MachineState.readWord em 128) 3942 s em 8
        (UInt256.ofNat 0) f.w3 (UInt256.ofNat 3643) f.tl f.inv f.m0 f.m96 f.m64
        f.m32 (cachedTop cm) (UInt256.ofNat (k-1+1)) f.ret f.rest := by
    rw [hflag, hc]
    simp only [atOld, exitFrame, hcount, show MachineState.readWord em 128 = f.m128 from he.m128]
  have hend :
      TnM128SquareExit.frameAt (UInt256.ofNat 0)
        (MachineState.readWord (CRTExitTail.memory em tn) 128) 4816 s
        (CRTExitTail.memory em tn) 8 (UInt256.ofNat (2^256-256)) f.w3
        (UInt256.ofNat 3643) f.tl f.inv f.m0 f.m96 f.m64 f.m32 (cachedTop cm)
        (UInt256.ofNat (k-1)) f.ret f.rest =
      atOld s (finish s minv n mem) 4816 (UInt256.ofNat 0)
        (UInt256.ofNat (2^256-256)) (UInt256.ofNat 3643) fn := by
    rw [hmem, hf.m128]
    rfl
  have g01 := g0.trans (g1.cast hstart.symm hend)
  have g2 := CRTGasStepsNormalized.entry s (finish s minv n mem) fn
    (UInt256.ofNat (2^256-256)) (UInt256.ofNat 3643) env hcap hact
  have hout :
      atCache s (entryMemory (finish s minv n mem) fn.counter) 5859
        (inputWord (finish s minv n mem) 0) (MachineState.readWord (finish s minv n mem) 2720) fn =
      atCache s (entryMemory (finish s minv n mem) (UInt256.ofNat (k-1))) 5859 n minv fn := by
    unfold atCache cache
    rw [←hf.cachedInverse, ←hf.cachedDigits 0 (by decide), ←hf.cachedDigits 1 (by decide),
      ←hf.cachedDigits 2 (by decide), ←hf.cachedDigits 3 (by decide),
      ←hf.cachedDigits 4 (by decide), ←hf.cachedDigits 5 (by decide),
      ←hf.cachedDigits 6 (by decide), ←hf.cachedDigits 7 (by decide),
      ←hf.cachedDigits 8 (by decide)]
  exact g01.trans (g2.cast rfl hout)

#print axioms gasSteps
end HistoricalSearch.CRTOverflowMore

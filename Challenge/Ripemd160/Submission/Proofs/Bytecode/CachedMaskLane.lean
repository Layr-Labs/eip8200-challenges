import Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskLane
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackCompression QuadSemantic StackRoundTemplate StackRoundTrace CavityQuadGroup
open FullInlineParams (left4 right4)
open QuadRoundTemplate (factor)
abbrev Artifact := FullInlineSites.A
abbrev low32DenseWordsAt := QuadSemantic.DenseWordsAt
abbrev stateAt := CavityQuadGroup.stateAt

private theorem left_entry_end : FullInlineSites.leftEntry.destination.pc.succ = FullInlineSites.leftPC 0 := by
  change (UInt256.ofNat (FullInlineSites.A.instructionPC 3146)).succ = UInt256.ofNat 5234
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
private theorem left_return_start : FullInlineSites.leftReturn.push.pc = FullInlineSites.leftPC 20 := by
  change UInt256.ofNat (FullInlineSites.A.instructionPC 5371) = UInt256.ofNat 8034
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
private theorem left_return_end : FullInlineSites.leftReturn.destination.pc.succ = QuadLayout.leftPC 20 := by
  change (UInt256.ofNat (FullInlineSites.A.instructionPC 2142)).succ = UInt256.ofNat (FullInlineSites.A.instructionPC 2143)
  repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private noncomputable def left_quad (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (rho : List UInt256) (k : Fin 20)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1006) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (FullInlineSites.leftPC k.val) w (mask :: rho))
      (stateAt s (FullInlineSites.leftPC (k.val + 1)) (left4 word k w) (mask :: rho)) := by
  let site := FullInlineSites.left k
  have raw := CachedMaskQuadGroup.run_left (FullInlineParams.left k) s site.startPC w rho
    (FullInlineParams.left_fits s k hactive) hstack hrun
  rw [← CavityFragmentChain.site_end site, FullInlineParams.left_apply s word w k hwords] at raw
  have g : GasSteps (stateAt s site.startPC w (mask :: rho))
      (stateAt s site.endPC (left4 word k w) (mask :: rho)) := by
    apply Stepper.runLocatedBlock_sound Artifact .Osaka site.path
    · exact hcode
    · exact hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw site (CachedMaskQuadGroup.advances (FullInlineParams.left k) 0)
        (stateAt s site.startPC w (mask :: rho)) rfl]
      exact raw
    · exact hrun
    · exact hnp
  simpa only [site, FullInlineSites.left_start, FullInlineSites.left_end] using g

noncomputable def gasSteps_left80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1006) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.leftPC 0) working (mask :: rho))
      (stateAt s (QuadLayout.leftPC 20) (leftRounds word 80 working) (mask :: rho)) := by
  let states := fun n => stateAt s (FullInlineSites.leftPC n)
    (leftRounds word (4 * n) working) (mask :: rho)
  have step (i : Nat) (hi : i < 20) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, hi⟩
    have g := left_quad s word (leftRounds word (4 * i) working) rho k
      hwords hactive hstack hcode hfork hrun hnp
    have hnext : leftRounds word (4 * (i + 1)) working =
        left4 word k (leftRounds word (4 * i) working) := by
      rw [leftRounds_quad word i working]
      rfl
    apply g.cast
    · rfl
    · change stateAt s (FullInlineSites.leftPC (i + 1))
          (left4 word k (leftRounds word (4 * i) working)) (mask :: rho) =
        stateAt s (FullInlineSites.leftPC (i + 1))
          (leftRounds word (4 * (i + 1)) working) (mask :: rho)
      rw [hnext]
  have core := GasSteps.iterateBounded 20 step
  have hcap (w : Compression.EvmWorking) :
      ([w.a, w.b, w.c, w.d, w.e] ++ factor :: (mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge FullInlineSites.leftEntry s
    ([working.a, working.b, working.c, working.d, working.e] ++ factor :: (mask :: rho))
    (hcap working) hcode hfork hrun hnp
  let finish := leftRounds word 80 working
  have leave := gasSteps_bridge FullInlineSites.leftReturn s
    ([finish.a, finish.b, finish.c, finish.d, finish.e] ++ factor :: (mask :: rho))
    (hcap finish) hcode hfork hrun hnp
  rw [left_entry_end] at enter
  rw [left_return_start, left_return_end] at leave
  exact (enter.trans core).trans leave

private theorem right_entry_end : FullInlineSites.rightEntry.destination.pc.succ = FullInlineSites.rightPC 0 := by
  change (UInt256.ofNat (FullInlineSites.A.instructionPC 5373)).succ = UInt256.ofNat 8039
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
private theorem right_return_start : FullInlineSites.rightReturn.push.pc = FullInlineSites.rightPC 20 := by
  change UInt256.ofNat (FullInlineSites.A.instructionPC 7598) = UInt256.ofNat 10839
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide
private theorem right_return_end : FullInlineSites.rightReturn.destination.pc.succ = QuadLayout.rightPC 20 := by
  change (UInt256.ofNat (FullInlineSites.A.instructionPC 2804)).succ = UInt256.ofNat (FullInlineSites.A.instructionPC 2805)
  repeat' rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private noncomputable def right_quad (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256) (k : Fin 20)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1001) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (FullInlineSites.rightPC k.val) w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s (FullInlineSites.rightPC (k.val + 1)) (right4 word k w) (a :: b :: c :: d :: e :: mask :: rho)) := by
  let site := FullInlineSites.right k
  have raw := CachedMaskQuadGroup.run_right (FullInlineParams.right k) s site.startPC w a b c d e rho
    (FullInlineParams.right_fits s k hactive) hstack hrun
  rw [← CavityFragmentChain.site_end site, FullInlineParams.right_apply s word w k hwords] at raw
  have g : GasSteps (stateAt s site.startPC w (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s site.endPC (right4 word k w) (a :: b :: c :: d :: e :: mask :: rho)) := by
    apply Stepper.runLocatedBlock_sound Artifact .Osaka site.path
    · exact hcode
    · exact hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw site (CachedMaskQuadGroup.advances (FullInlineParams.right k) 5)
        (stateAt s site.startPC w (a :: b :: c :: d :: e :: mask :: rho)) rfl]
      exact raw
    · exact hrun
    · exact hnp
  simpa only [site, FullInlineSites.right_start, FullInlineSites.right_end] using g

noncomputable def gasSteps_right80 (s : State) (word : Nat → UInt32)
    (working : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hwords : low32DenseWordsAt s word) (hactive : 39 ≤ s.activeWords.toNat)
    (hstack : rho.length < 1001) (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (QuadLayout.rightPC 0) working (a :: b :: c :: d :: e :: mask :: rho))
      (stateAt s (QuadLayout.rightPC 20) (rightRounds word 80 working) (a :: b :: c :: d :: e :: mask :: rho)) := by
  let states := fun n => stateAt s (FullInlineSites.rightPC n)
    (rightRounds word (4 * n) working) (a :: b :: c :: d :: e :: mask :: rho)
  have step (i : Nat) (hi : i < 20) : GasSteps (states i) (states (i + 1)) := by
    let k : Fin 20 := ⟨i, hi⟩
    have g := right_quad s word (rightRounds word (4 * i) working) a b c d e rho k
      hwords hactive hstack hcode hfork hrun hnp
    have hnext : rightRounds word (4 * (i + 1)) working =
        right4 word k (rightRounds word (4 * i) working) := by
      rw [rightRounds_quad word i working]
      rfl
    apply g.cast
    · rfl
    · change stateAt s (FullInlineSites.rightPC (i + 1))
          (right4 word k (rightRounds word (4 * i) working)) (a :: b :: c :: d :: e :: mask :: rho) =
        stateAt s (FullInlineSites.rightPC (i + 1))
          (rightRounds word (4 * (i + 1)) working) (a :: b :: c :: d :: e :: mask :: rho)
      rw [hnext]
  have core := GasSteps.iterateBounded 20 step
  have hcap (w : Compression.EvmWorking) :
      ([w.a, w.b, w.c, w.d, w.e] ++ factor :: (a :: b :: c :: d :: e :: mask :: rho)).length < 1023 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have enter := gasSteps_bridge FullInlineSites.rightEntry s
    ([working.a, working.b, working.c, working.d, working.e] ++ factor :: (a :: b :: c :: d :: e :: mask :: rho))
    (hcap working) hcode hfork hrun hnp
  let finish := rightRounds word 80 working
  have leave := gasSteps_bridge FullInlineSites.rightReturn s
    ([finish.a, finish.b, finish.c, finish.d, finish.e] ++ factor :: (a :: b :: c :: d :: e :: mask :: rho))
    (hcap finish) hcode hfork hrun hnp
  rw [right_entry_end] at enter
  rw [right_return_start, right_return_end] at leave
  exact (enter.trans core).trans leave

#print axioms gasSteps_left80
#print axioms gasSteps_right80
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskLane

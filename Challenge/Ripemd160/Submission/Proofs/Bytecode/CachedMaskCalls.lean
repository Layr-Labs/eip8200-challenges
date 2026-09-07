import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadFallthroughTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate


namespace Normal

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (helperCode : List Instr) where
  returnPC : UInt256
  helperPC : UInt256
  call : QuadCallTrace.CallSite artifact fork
    returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3
  helper : GenericRoundSite artifact fork
    helperCode
  helper_start : helper.startPC = helperPC
  helperJump : LocatedSite artifact fork
  helper_jump_instr : helperJump.located.instruction = .op .JUMP
  helper_end : helperJump.pc = helper.endPC
  returnSite : LocatedSite artifact fork
  return_instr : returnSite.located.instruction = .op .JUMPDEST
  return_at : returnSite.pc = returnPC
  helper_valid : Decode.isValidJumpDest artifact.code helperPC.toNat = true
  return_valid : Decode.isValidJumpDest artifact.code returnPC.toNat = true



def gasSteps_quad_of_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (helperCode : List Instr)
    (site : RoundSite artifact fork p0 p1 p2 p3 r0 r1 r2 r3 helperCode)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ghelper : GasSteps
      (QuadRoundState.quadHelperEntry s site.helper.startPC
        p0 p1 p2 p3 site.returnPC r0 r1 r2 r3 working rho)
      (QuadRoundState.quadAfterHelperBeforeJump s site.helper.endPC
        site.returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho))
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (QuadRoundState.quadWorking s working j p0 p1 p2 p3
            r0 r1 r2 r3 constant) ++ [QuadRoundTemplate.factor] ++ rho
        activeWords :=
          (QuadRoundState.quadActiveWordsAfterUInt256_4 s
            p0.toNat p1.toNat p2.toNat p3.toNat)} := by
  have helperValid : Decode.isValidJumpDest s.executionEnv.code
      site.helperPC.toNat = true := by
    rw [hcode]
    exact site.helper_valid
  have gc := QuadCallTrace.gasSteps_call
    site.returnPC p0 p1 p2 p3 site.helperPC r0 r1 r2 r3
    site.call s working rho hstack hrun helperValid hcode hfork hnp
  have gc' : GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho))
      (QuadRoundState.quadHelperEntry s site.helper.startPC
        p0 p1 p2 p3 site.returnPC r0 r1 r2 r3 working rho) := by
    apply gc.cast rfl
    rw [site.helper_start]
  let t : State :=
    {s with activeWords :=
      (QuadRoundState.quadActiveWordsAfterUInt256_4 s
        p0.toNat p1.toNat p2.toNat p3.toNat)}
  let words : List UInt256 := roundWords
      (QuadRoundState.quadWorking s working j p0 p1 p2 p3
        r0 r1 r2 r3 constant) ++ [QuadRoundTemplate.factor] ++ rho
  have wordsBound : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have returnValid : Decode.isValidJumpDest t.executionEnv.code
      site.returnSite.pc.toNat = true := by
    change Decode.isValidJumpDest s.executionEnv.code site.returnSite.pc.toNat = true
    rw [hcode, site.return_at]
    exact site.return_valid
  have gr := SharedCallTrace.gasSteps_return site.helperJump site.returnSite
    site.helper_jump_instr site.return_instr t words wordsBound hrun returnValid
      hcode hfork hnp
  have before :
      QuadRoundState.quadAfterHelperBeforeJump s site.helper.endPC
        site.returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho =
      {t with pc := site.helperJump.pc, stack := site.returnSite.pc :: words} := by
    rw [site.helper_end, site.return_at]
    rfl
  have after :
      {t with pc := site.returnSite.pc.succ, stack := words} =
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (QuadRoundState.quadWorking s working j p0 p1 p2 p3
            r0 r1 r2 r3 constant) ++ [QuadRoundTemplate.factor] ++ rho
        activeWords := QuadRoundState.quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
    rfl
  exact gc'.trans (ghelper.trans (gr.cast before.symm after))


#print axioms gasSteps_quad_of_helper

end Normal

namespace Fallthrough

open QuadFallthroughTrace

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (helperCode : List Instr) where
  returnPC : UInt256
  callPushes : GenericRoundSite artifact fork
    (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3)
  helper : GenericRoundSite artifact fork
    helperCode
  helper_start : helper.startPC = callPushes.endPC
  helperJump : LocatedSite artifact fork
  helper_jump_instr : helperJump.located.instruction = .op .JUMP
  helper_end : helperJump.pc = helper.endPC
  returnSite : LocatedSite artifact fork
  return_instr : returnSite.located.instruction = .op .JUMPDEST
  return_at : returnSite.pc = returnPC
  return_valid : Decode.isValidJumpDest artifact.code returnPC.toNat = true



def gasSteps_of_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (helperCode : List Instr)
    (site : RoundSite artifact fork p0 p1 p2 p3 r0 r1 r2 r3 helperCode)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ghelper : GasSteps
      (quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC
        r0 r1 r2 r3 working rho)
      (quadAfterHelperBeforeJump s site.helper.endPC site.returnPC j working
        p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    GasSteps
      (roundEntry s site.callPushes.startPC working.a working.b working.c
        working.d working.e (factor :: rho))
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant) ++
          [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  have gp : GasSteps
      (roundEntry s site.callPushes.startPC working.a working.b working.c
        working.d working.e (factor :: rho))
      (quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC
        r0 r1 r2 r3 working rho) := by
    apply Stepper.runLocatedBlock_sound artifact fork site.callPushes.path
    · exact hcode
    · exact hfork
    · rw [site.helper_start]
      exact runLocatedBlock_pushes site.returnPC p0 p1 p2 p3 r0 r1 r2 r3
        site.callPushes s working rho hstack hrun
    · exact hrun
    · exact hnp
  let t : State :=
    {s with activeWords :=
      (quadActiveWordsAfterUInt256_4 s
        p0.toNat p1.toNat p2.toNat p3.toNat)}
  let words : List UInt256 := roundWords
    (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant) ++
    [factor] ++ rho
  have wordsBound : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have returnValid : Decode.isValidJumpDest t.executionEnv.code
      site.returnSite.pc.toNat = true := by
    change Decode.isValidJumpDest s.executionEnv.code site.returnSite.pc.toNat = true
    rw [hcode, site.return_at]
    exact site.return_valid
  have gr := SharedCallTrace.gasSteps_return site.helperJump site.returnSite
    site.helper_jump_instr site.return_instr t words wordsBound hrun returnValid
      hcode hfork hnp
  have before :
      quadAfterHelperBeforeJump s site.helper.endPC site.returnPC j working
        p0 p1 p2 p3 r0 r1 r2 r3 constant rho =
      {t with pc := site.helperJump.pc, stack := site.returnSite.pc :: words} := by
    rw [site.helper_end, site.return_at]
    rfl
  have after :
      {t with pc := site.returnSite.pc.succ, stack := words} =
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant) ++
          [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
    rfl
  exact gp.trans (ghelper.trans (gr.cast before.symm after))


#print axioms gasSteps_of_helper

end Fallthrough

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls

import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadFallthroughTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newShiftedHoistHelper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls.ShiftedCall

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

/-- Instructions push `s3, p3, s2, p2, s1, p1, s0, return-PC, p0,
helper-PC`.  The resulting top-first stack has the quad helper-entry shape. -/
def quadCallPushes (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  [ShiftedHoistHelper.controlPush r3, push2 p3,
    ShiftedHoistHelper.controlPush r2, push2 p2,
    ShiftedHoistHelper.controlPush r1, push2 p1,
    ShiftedHoistHelper.controlPush r0, push2 returnPC,
    push2 p0, push2 helperPC]

/-- State after the quad wrapper has pushed its ten values. -/
def quadCallPushed (s : State) (pc returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := pc
    stack := [helperPC, p0, returnPC, ShiftedHoistHelper.shiftedFactor r0, p1,
      ShiftedHoistHelper.shiftedFactor r1, p2, ShiftedHoistHelper.shiftedFactor r2, p3,
      ShiftedHoistHelper.shiftedFactor r3] ++ roundWords working ++
      [QuadRoundTemplate.factor] ++ rho }

theorem quadCallPushes_advances (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) :
    ∀ instruction ∈ quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [quadCallPushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_quadCallPushes (s : State)
    (pc returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (QuadRoundTemplate.factor :: rho)) =
    some (quadCallPushed s
      (pcAfter pc (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3))
      returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3 working rho) := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by
    omega
  simp (discharger := omega)
    [quadCallPushes, quadCallPushed, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, ShiftedHoistHelper.controlPush, push1, push2, hrun, hcap,
      Nat.add_assoc, Instr.size_push, roundWords,
      QuadRoundTemplate.factor]

theorem runLocatedBlock_quadCallPushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (site : GenericRoundSite artifact fork
      (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d
        working.e (QuadRoundTemplate.factor :: rho)) =
      some (quadCallPushed s site.endPC returnPC p0 p1 p2 p3 helperPC
        r0 r1 r2 r3 working rho) := by
  have hend : site.endPC = pcAfter site.startPC
      (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site
    (quadCallPushes_advances _ _ _ _ _ _ _ _ _ _)
    (roundEntry s site.startPC working.a working.b working.c working.d
      working.e (QuadRoundTemplate.factor :: rho)) rfl]
  rw [runInstrSeq_quadCallPushes s site.startPC returnPC p0 p1 p2 p3 helperPC
    r0 r1 r2 r3 working rho hstack hrun, ← hend]

structure CallSite (artifact : ProgramArtifact) (fork : Fork)
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) where
  pushes : GenericRoundSite artifact fork
    (quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3)
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = pushes.endPC

def CallSite.path {artifact : ProgramArtifact} {fork : Fork}
    {returnPC p0 p1 p2 p3 helperPC : UInt256}
    {r0 r1 r2 r3 : Nat}
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3) : List (Stepper.Located artifact fork) :=
  site.pushes.path ++ [site.jump.located]

theorem runLocatedBlock_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho)) =
      some (ShiftedHoistHelper.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) := by
  apply Stepper.runLocatedBlock_append site.pushes.path [site.jump.located] _
    (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 working rho)
  · exact runLocatedBlock_quadCallPushes returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 site.pushes s working rho hstack hrun
  · exact hrun
  · have hcap :
        ([p0, returnPC, ShiftedHoistHelper.shiftedFactor r0, p1,
          ShiftedHoistHelper.shiftedFactor r1, p2, ShiftedHoistHelper.shiftedFactor r2, p3,
          ShiftedHoistHelper.shiftedFactor r3] ++ roundWords working ++
          [QuadRoundTemplate.factor] ++ rho).length < 1023 := by
      simp [roundWords]
      omega
    have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr s
      helperPC
      ([p0, returnPC, ShiftedHoistHelper.shiftedFactor r0, p1,
        ShiftedHoistHelper.shiftedFactor r1, p2, ShiftedHoistHelper.shiftedFactor r2, p3,
        ShiftedHoistHelper.shiftedFactor r3] ++ roundWords working ++
        [QuadRoundTemplate.factor] ++ rho) hcap hvalid
    have hlocated : Stepper.runLocated site.jump.located
        (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
          r0 r1 r2 r3 working rho) =
        some (ShiftedHoistHelper.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) := by
      simpa [quadCallPushed, ShiftedHoistHelper.quadHelperEntry, roundWords,
        site.jump_pc, QuadRoundTemplate.factor] using h
    simp only [Stepper.runLocatedBlock, hlocated]

def gasSteps_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s site.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho))
      (ShiftedHoistHelper.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_call returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 site s working rho hstack hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls.ShiftedCall

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls.ShiftedFallthrough

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

def pushes (returnPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  [ShiftedHoistHelper.controlPush r3, push2 p3,
    ShiftedHoistHelper.controlPush r2, push2 p2,
    ShiftedHoistHelper.controlPush r1, push2 p1,
    ShiftedHoistHelper.controlPush r0, push2 returnPC,
    push2 p0]

theorem pushes_advances (returnPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) :
    ∀ instruction ∈ pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [pushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_pushes (s : State)
    (pc returnPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (factor :: rho)) =
    some (ShiftedHoistHelper.quadHelperEntry s
      (pcAfter pc (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3))
      p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  simp (discharger := omega)
    [pushes, ShiftedHoistHelper.quadHelperEntry, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, ShiftedHoistHelper.controlPush, push1, push2, hrun, hcap,
      Nat.add_assoc, Instr.size_push, roundWords, factor]

theorem runLocatedBlock_pushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (site : GenericRoundSite artifact fork
      (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d
        working.e (factor :: rho)) =
      some (ShiftedHoistHelper.quadHelperEntry s site.endPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) := by
  have hend : site.endPC = pcAfter site.startPC
      (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site
    (pushes_advances _ _ _ _ _ _ _ _ _)
    (roundEntry s site.startPC working.a working.b working.c working.d
      working.e (factor :: rho)) rfl]
  rw [runInstrSeq_pushes s site.startPC returnPC p0 p1 p2 p3
    r0 r1 r2 r3 working rho hstack hrun, ← hend]


end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls.ShiftedFallthrough

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate


namespace Normal

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (helperCode : List Instr) where
  returnPC : UInt256
  helperPC : UInt256
  call : ShiftedCall.CallSite artifact fork
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
      (ShiftedHoistHelper.quadHelperEntry s site.helper.startPC
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
  have gc := ShiftedCall.gasSteps_call
    site.returnPC p0 p1 p2 p3 site.helperPC r0 r1 r2 r3
    site.call s working rho hstack hrun helperValid hcode hfork hnp
  have gc' : GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c
        working.d working.e (QuadRoundTemplate.factor :: rho))
      (ShiftedHoistHelper.quadHelperEntry s site.helper.startPC
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

open ShiftedFallthrough

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
      (ShiftedHoistHelper.quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC
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
      (ShiftedHoistHelper.quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC
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

import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskCalls
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedHoistHelper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Loaded-word quad calls

The quad-call preamble loads each schedule word where it used to push the
word's pointer: `PUSH1 off; MLOAD` in place of `PUSH2 ptr`.  The pushed state
therefore holds the four loaded words and the memory expansion of the four
loads, which is exactly the entry the loaded-word helper expects.  The
composed call/helper/return endpoint is unchanged from the shifted layer.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedCalls

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

/-- Active words after loading at `p3`, `p2`, `p1`, `p0` in that order. -/
def afterLoad (s : State) (p : UInt256) : State :=
  { s with activeWords := s.activeWordsAfterUInt256 p.toNat 32 }

def loadedActiveWords (s : State) (p3 p2 p1 p0 : UInt256) : UInt256 :=
  (afterLoad (afterLoad (afterLoad (afterLoad s p3) p2) p1) p0).activeWords

/-- Loading in the caller's order expands memory exactly as the helper's
`p0, p1, p2, p3` order did. -/
theorem loadedActiveWords_eq (s : State) (p0 p1 p2 p3 : UInt256) :
    loadedActiveWords s p3 p2 p1 p0 =
      quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat := by
  have hs : s.activeWords.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    s.activeWords.val.isLt
  have h0 : p0.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    p0.val.isLt
  have h1 : p1.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    p1.val.isLt
  have h2 : p2.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    p2.val.isLt
  have h3 : p3.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    p3.val.isLt
  apply Word.word_ext
  simp only [loadedActiveWords, afterLoad, quadActiveWordsAfterUInt256_4,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
    MachineState.activeWordsAfter, Word.word_toNat_ofNat, Nat.max_def,
    show ((32 : Nat) = 0) ↔ False from by decide,
    show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by
      norm_num]
  split_ifs <;> omega

namespace ShiftedCall

/-- Instructions push `s3, w3, s2, w2, s1, w1, s0, return-PC, w0, helper-PC`,
loading each word `w_i` from its schedule offset `p_i` as it goes, with SWAP8
before the `w0` load to exchange A and return-PC. -/
def quadCallPushes (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  [ShiftedHoistHelper.controlPush r3, push1 p3, .op .MLOAD,
    ShiftedHoistHelper.controlPush r2, push1 p2, .op .MLOAD,
    ShiftedHoistHelper.controlPush r1, push1 p1, .op .MLOAD,
    ShiftedHoistHelper.controlPush r0, push2 returnPC,
    .op (.Swap ⟨7, by decide⟩), push1 p0, .op .MLOAD, push2 helperPC]

/-- State after the quad wrapper has pushed its values and loaded the words. -/
def quadCallPushed (s : State) (pc returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := pc
    stack := [helperPC, MachineState.readWord s.memory p0.toNat, working.a,
      ShiftedHoistHelper.shiftedFactor r0,
      MachineState.readWord s.memory p1.toNat, ShiftedHoistHelper.shiftedFactor r1,
      MachineState.readWord s.memory p2.toNat, ShiftedHoistHelper.shiftedFactor r2,
      MachineState.readWord s.memory p3.toNat, ShiftedHoistHelper.shiftedFactor r3,
      returnPC, working.b, working.c, working.d, working.e] ++
      [QuadRoundTemplate.factor] ++ rho
    activeWords := quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat }

theorem quadCallPushes_advances (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (r0 r1 r2 r3 : Nat) :
    ∀ instruction ∈ quadCallPushes returnPC p0 p1 p2 p3 helperPC r0 r1 r2 r3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [quadCallPushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (StraightLine.push _ _)
    | exact Or.inl (StraightLine.swap _)
    | exact Or.inl StraightLine.mload

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
  rw [quadCallPushed, ← loadedActiveWords_eq s p0 p1 p2 p3]
  simp (config := { maxSteps := 5000000 }) (discharger := omega)
    [quadCallPushes, loadedActiveWords, afterLoad, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, ShiftedHoistHelper.controlPush, push1, push2, hrun, hcap,
      Nat.add_assoc, Instr.size_push, Instr.size_op, UInt256.succ, List.exchange, roundWords,
      List.getElem?_cons_zero, Option.bind_some, QuadRoundTemplate.factor,
      State.activeWordsAfterUInt256]
  simp only [Nat.add_comm]
  rfl

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
      some (LoadedHoistHelper.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) := by
  apply Stepper.runLocatedBlock_append site.pushes.path [site.jump.located] _
    (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 working rho)
  · exact runLocatedBlock_quadCallPushes returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 site.pushes s working rho hstack hrun
  · exact hrun
  · let loaded : State :=
      {s with activeWords :=
        quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat}
    let rest : List UInt256 :=
      [MachineState.readWord s.memory p0.toNat, working.a,
        ShiftedHoistHelper.shiftedFactor r0,
        MachineState.readWord s.memory p1.toNat, ShiftedHoistHelper.shiftedFactor r1,
        MachineState.readWord s.memory p2.toNat, ShiftedHoistHelper.shiftedFactor r2,
        MachineState.readWord s.memory p3.toNat, ShiftedHoistHelper.shiftedFactor r3,
        returnPC, working.b, working.c, working.d, working.e] ++
        [QuadRoundTemplate.factor] ++ rho
    have hcap : rest.length < 1023 := by
      simp [rest]
      omega
    have hvalid' : Decode.isValidJumpDest loaded.executionEnv.code helperPC.toNat = true :=
      hvalid
    have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr loaded
      helperPC rest hcap hvalid'
    have hlocated : Stepper.runLocated site.jump.located
        (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
          r0 r1 r2 r3 working rho) =
        some (LoadedHoistHelper.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) := by
      simpa [quadCallPushed, LoadedHoistHelper.quadHelperEntry, loaded, rest,
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
      (LoadedHoistHelper.quadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_call returnPC p0 p1 p2 p3 helperPC
      r0 r1 r2 r3 site s working rho hstack hrun hvalid
  · exact hrun
  · exact hnp

end ShiftedCall

namespace ShiftedFallthrough

/-- The last wrapper of a group falls through into the helper: the same
pushes and loads, without the helper-PC push. -/
def pushes (returnPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  [ShiftedHoistHelper.controlPush r3, push1 p3, .op .MLOAD,
    ShiftedHoistHelper.controlPush r2, push1 p2, .op .MLOAD,
    ShiftedHoistHelper.controlPush r1, push1 p1, .op .MLOAD,
    ShiftedHoistHelper.controlPush r0, push2 returnPC,
    .op (.Swap ⟨7, by decide⟩), push1 p0, .op .MLOAD]

theorem pushes_advances (returnPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) :
    ∀ instruction ∈ pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [pushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | exact Or.inl (StraightLine.push _ _)
    | exact Or.inl (StraightLine.swap _)
    | exact Or.inl StraightLine.mload

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_pushes (s : State)
    (pc returnPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (factor :: rho)) =
    some (LoadedHoistHelper.quadHelperEntry s
      (pcAfter pc (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3))
      p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  rw [LoadedHoistHelper.quadHelperEntry, ← loadedActiveWords_eq s p0 p1 p2 p3]
  simp (config := { maxSteps := 5000000 }) (discharger := omega)
    [pushes, loadedActiveWords, afterLoad, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, ShiftedHoistHelper.controlPush, push1, push2, hrun, hcap,
      Nat.add_assoc, Instr.size_push, Instr.size_op, UInt256.succ, List.exchange, roundWords,
      List.getElem?_cons_zero, Option.bind_some, factor, State.activeWordsAfterUInt256]
  simp only [Nat.add_comm]
  rfl

theorem runLocatedBlock_pushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (site : GenericRoundSite artifact fork
      (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d
        working.e (factor :: rho)) =
      some (LoadedHoistHelper.quadHelperEntry s site.endPC p0 p1 p2 p3 returnPC
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

end ShiftedFallthrough

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
      (LoadedHoistHelper.quadHelperEntry s site.helper.startPC
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
      (LoadedHoistHelper.quadHelperEntry s site.helper.startPC
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
      (LoadedHoistHelper.quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC
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
      (LoadedHoistHelper.quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedCalls


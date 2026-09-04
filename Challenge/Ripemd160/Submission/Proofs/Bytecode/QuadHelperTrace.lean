import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false

/-!
# Q4M quad-round helper composition

Composes a genuine quad helper evaluation with the ten-push call and the
common return trace.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (j : Nat) (p0 p1 p2 p3 M0 M1 M2 M3 : UInt256) (w0 w1 w2 w3 : Fin 33)
    (constant : UInt256) where
  returnPC : UInt256
  helperPC : UInt256
  call : QuadCallTrace.CallSite artifact fork returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3
    w0 w1 w2 w3
  helper : GenericRoundSite artifact fork (quadBeforeJumpTemplate j constant)
  helper_start : helper.startPC = helperPC
  helperJump : LocatedSite artifact fork
  helper_jump_instr : helperJump.located.instruction = .op .JUMP
  helper_end : helperJump.pc = helper.endPC
  returnSite : LocatedSite artifact fork
  return_instr : returnSite.located.instruction = .op .JUMPDEST
  return_at : returnSite.pc = returnPC
  helper_valid : Decode.isValidJumpDest artifact.code helperPC.toNat = true
  return_valid : Decode.isValidJumpDest artifact.code returnPC.toNat = true

/-- Decidable approximation of `PairMultiplyLift.Advances` for the template check. -/
def advancesB : Instr → Bool
  | .push _ _ => true
  | .op .ADD => true
  | .op .AND => true
  | .op .OR => true
  | .op .XOR => true
  | .op .NOT => true
  | .op .SHL => true
  | .op .SHR => true
  | .op .POP => true
  | .op .MLOAD => true
  | .op (.Dup _) => true
  | .op (.Swap _) => true
  | .op .SUB => true
  | .op .JUMPDEST => true
  | .op .MUL => true
  | _ => false

theorem advances_of_advancesB (instruction : Instr) (h : advancesB instruction = true) :
    PairMultiplyLift.Advances instruction := by
  unfold PairMultiplyLift.Advances SharedCallTrace.Advances
  cases instruction with
  | push width value => exact Or.inl (Or.inl (StraightLine.push width value))
  | op operation =>
      cases operation with
      | StopArith o =>
          cases o <;> simp [advancesB] at h <;>
            first
            | exact Or.inl (Or.inl StraightLine.add)
            | exact Or.inr rfl
            | exact Or.inl (Or.inr (Or.inl rfl))
      | CompBit o =>
          cases o <;> simp [advancesB] at h <;>
            first
            | exact Or.inl (Or.inl StraightLine.and)
            | exact Or.inl (Or.inl StraightLine.or)
            | exact Or.inl (Or.inl StraightLine.xor)
            | exact Or.inl (Or.inl StraightLine.not)
            | exact Or.inl (Or.inl StraightLine.shl)
            | exact Or.inl (Or.inl StraightLine.shr)
      | StackMemFlow o =>
          cases o <;> simp [advancesB] at h <;>
            first
            | exact Or.inl (Or.inl StraightLine.pop)
            | exact Or.inl (Or.inl StraightLine.mload)
            | exact Or.inl (Or.inr (Or.inr rfl))
      | Dup o => exact Or.inl (Or.inl (StraightLine.dup o))
      | Swap o => exact Or.inl (Or.inl (StraightLine.swap o))
      | Keccak o => cases o <;> simp [advancesB] at h
      | Env o => cases o <;> simp [advancesB] at h
      | Block o => cases o <;> simp [advancesB] at h
      | Push o => simp [advancesB] at h
      | DupN o => simp [advancesB] at h
      | SwapN o => simp [advancesB] at h
      | Exchange o => simp [advancesB] at h
      | Log o => simp [advancesB] at h
      | System o => cases o <;> simp [advancesB] at h

theorem template_all_advancesB (j : Nat) (hj : j < 5) (constant : UInt256) :
    (quadBeforeJumpTemplate j constant).all advancesB = true := by
  interval_cases j <;>
    simp [quadBeforeJumpTemplate, quadBeforeJumpTemplate0, quadBeforeJumpTemplate1,
      quadBeforeJumpTemplate2, quadBeforeJumpTemplate3, quadBeforeJumpTemplate4,
      seg0_0, seg0_1, seg0_2, seg0_3, seg0_4, seg0_5,
      seg1_0, seg1_1, seg1_2, seg1_3, seg1_4, seg1_5,
      seg2_0, seg2_1, seg2_2, seg2_3, seg2_4, seg2_5,
      seg3_0, seg3_1, seg3_2, seg3_3, seg3_4, seg3_5,
      seg4_0, seg4_1, seg4_2, seg4_3, seg4_4, seg4_5,
      op, push1, push4, push5, advancesB]

theorem template_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ quadBeforeJumpTemplate j constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  apply advances_of_advancesB
  have h := template_all_advancesB j hj constant
  rw [List.all_eq_true] at h
  exact h instruction hmem

theorem runLocatedBlock_quad_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (p0 p1 p2 p3 M0 M1 M2 M3 : UInt256) (constant : UInt256)
    (site : GenericRoundSite artifact fork (quadBeforeJumpTemplate j constant))
    (s : State) (returnPC : UInt256) (working : EvmWorking) (rest : List UInt256)
    (hraw :
      runInstrSeq (quadBeforeJumpTemplate j constant)
        (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.startPC (quadBeforeJumpTemplate j constant)) returnPC
        (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) rest)) :
    Stepper.runLocatedBlock site.path
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest) =
      some (quadAfterHelperBeforeJump s site.endPC returnPC
        (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) rest) := by
  have hend : site.endPC = pcAfter site.startPC (quadBeforeJumpTemplate j constant) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site (template_advances j hj constant)
    (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest) rfl]
  rw [hraw, ← hend]

def gasSteps_helper_of_raw {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (p0 p1 p2 p3 M0 M1 M2 M3 : UInt256) (constant : UInt256)
    (site : GenericRoundSite artifact fork (quadBeforeJumpTemplate j constant))
    (s : State) (returnPC : UInt256) (working : EvmWorking) (rest : List UInt256)
    (hraw :
      runInstrSeq (quadBeforeJumpTemplate j constant)
        (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest) =
      some (quadAfterHelperBeforeJump s
        (pcAfter site.startPC (quadBeforeJumpTemplate j constant)) returnPC
        (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) rest))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest)
      (quadAfterHelperBeforeJump s site.endPC returnPC
        (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_quad_of_raw j hj p0 p1 p2 p3 M0 M1 M2 M3 constant site s returnPC
      working rest hraw
  · exact hrun
  · exact hnp

/-- Compose the ten-push call, the helper body, and the return. -/
def gasSteps_quad_of_helper {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (p0 p1 p2 p3 M0 M1 M2 M3 : UInt256) (w0 w1 w2 w3 : Fin 33)
    (constant : UInt256)
    (site : RoundSite artifact fork j p0 p1 p2 p3 M0 M1 M2 M3 w0 w1 w2 w3 constant)
    (s : State) (working : EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ghelper : GasSteps
      (quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC M0 M1 M2 M3
        working rest)
      (quadAfterHelperBeforeJump s site.helper.endPC site.returnPC
        (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) rest)) :
    GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d
        working.e rest)
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) ++
          rest} := by
  have helperValid :
      Decode.isValidJumpDest s.executionEnv.code site.helperPC.toNat = true := by
    rw [hcode]
    exact site.helper_valid
  have gc := QuadCallTrace.gasSteps_call site.returnPC p0 p1 p2 p3 site.helperPC
    M0 M1 M2 M3 w0 w1 w2 w3 site.call s working rest hstack hrun helperValid hcode hfork hnp
  have gc' : GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c working.d
        working.e rest)
      (quadHelperEntry s site.helper.startPC p0 p1 p2 p3 site.returnPC M0 M1 M2 M3
        working rest) := by
    apply gc.cast rfl
    rw [site.helper_start]
  let words : List UInt256 :=
    roundWords (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) ++ rest
  have wordsBound : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have returnValid :
      Decode.isValidJumpDest s.executionEnv.code site.returnSite.pc.toNat = true := by
    rw [hcode, site.return_at]
    exact site.return_valid
  have gr := SharedCallTrace.gasSteps_return site.helperJump site.returnSite
    site.helper_jump_instr site.return_instr s words wordsBound hrun returnValid hcode
    hfork hnp
  have before :
      quadAfterHelperBeforeJump s site.helper.endPC site.returnPC
        (quadWorking s working j p0 p1 p2 p3 M0 M1 M2 M3 constant) rest =
      {s with pc := site.helperJump.pc, stack := site.returnSite.pc :: words} := by
    rw [site.helper_end, site.return_at]
    rfl
  exact gc'.trans (ghelper.trans (gr.cast before.symm rfl))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

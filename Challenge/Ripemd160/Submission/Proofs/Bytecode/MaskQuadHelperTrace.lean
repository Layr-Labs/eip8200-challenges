import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskProjection
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Masked H30b four-round helper composition

This module lifts a concrete masked helper trace through its located site and
composes the masked quad call, helper, and return traces.  The helper body is
abstract here, so left and right helper certificates can provide their own
raw execution theorem and instruction-step premise.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskQuadHelperTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskProjection
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskCallTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (template : List Instr)
    (p0 p1 p2 p3 : UInt256)
    (w0 w1 w2 w3 : Fin 32)
    (c0 c1 c2 c3 : UInt256) where
  returnPC : UInt256
  helperPC : UInt256
  call : MaskCallTrace.CallSite artifact fork
    returnPC p0 p1 p2 p3 helperPC w0 w1 w2 w3 c0 c1 c2 c3
  helper : GenericRoundSite artifact fork template
  helper_start : helper.startPC = helperPC
  helperJump : LocatedSite artifact fork
  helper_jump_instr : helperJump.located.instruction = .op .JUMP
  helper_end : helperJump.pc = helper.endPC
  returnSite : LocatedSite artifact fork
  return_instr : returnSite.located.instruction = .op .JUMPDEST
  return_at : returnSite.pc = returnPC
  helper_valid : Decode.isValidJumpDest artifact.code helperPC.toNat = true
  return_valid : Decode.isValidJumpDest artifact.code returnPC.toNat = true

theorem runLocatedBlock_mask_of_raw
    {artifact : ProgramArtifact} {fork : Fork}
    {template : List Instr}
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256)
    (site : GenericRoundSite artifact fork template)
    (s : State) (returnPC : UInt256)
    (c0 c1 c2 c3 : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hadv : ∀ instruction ∈ template,
      PairMultiplyLift.Advances instruction)
    (hraw :
      runInstrSeq template
        (maskQuadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
          c0 c1 c2 c3 working rho) =
      some (maskQuadAfterHelperBeforeJump s
        (pcAfter site.startPC template) returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    Stepper.runLocatedBlock site.path
      (maskQuadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
        c0 c1 c2 c3 working rho) =
      some (maskQuadAfterHelperBeforeJump s site.endPC returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  have hend : site.endPC = pcAfter site.startPC template := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site hadv
    (maskQuadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
      c0 c1 c2 c3 working rho) rfl]
  rw [hraw, ← hend]

def gasSteps_helper_of_raw
    {artifact : ProgramArtifact} {fork : Fork}
    {template : List Instr}
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256)
    (site : GenericRoundSite artifact fork template)
    (s : State) (returnPC : UInt256)
    (c0 c1 c2 c3 : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hadv : ∀ instruction ∈ template,
      PairMultiplyLift.Advances instruction)
    (hraw :
      runInstrSeq template
        (maskQuadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
          c0 c1 c2 c3 working rho) =
      some (maskQuadAfterHelperBeforeJump s
        (pcAfter site.startPC template) returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (maskQuadHelperEntry s site.startPC p0 p1 p2 p3 returnPC
        c0 c1 c2 c3 working rho)
      (maskQuadAfterHelperBeforeJump s site.endPC returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_mask_of_raw j p0 p1 p2 p3 r0 r1 r2 r3
      constant site s returnPC c0 c1 c2 c3 working rho hadv hraw
  · exact hrun
  · exact hnp

def gasSteps_maskQuad_of_helper
    {artifact : ProgramArtifact} {fork : Fork}
    {template : List Instr}
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256)
    (w0 w1 w2 w3 : Fin 32)
    (c0 c1 c2 c3 : UInt256)
    (site : RoundSite artifact fork template p0 p1 p2 p3
      w0 w1 w2 w3 c0 c1 c2 c3)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (ghelper : GasSteps
      (maskQuadHelperEntry s site.helper.startPC
        p0 p1 p2 p3 site.returnPC c0 c1 c2 c3 working rho)
      (maskQuadAfterHelperBeforeJump s site.helper.endPC site.returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho)) :
    GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c
        working.d working.e (MaskProjection.mask :: factor :: rho))
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (quadWorking s working j p0 p1 p2 p3
            r0 r1 r2 r3 constant) ++ [MaskProjection.mask, factor] ++ rho
        activeWords :=
          quadActiveWordsAfterUInt256_4 s
            p0.toNat p1.toNat p2.toNat p3.toNat} := by
  have helperValid : Decode.isValidJumpDest s.executionEnv.code
      site.helperPC.toNat = true := by
    rw [hcode]
    exact site.helper_valid
  have gc := MaskCallTrace.gasSteps_call
    site.returnPC p0 p1 p2 p3 site.helperPC
    w0 w1 w2 w3 c0 c1 c2 c3 site.call s working rho (by omega) hrun
    helperValid hcode hfork hnp
  have gc' : GasSteps
      (roundEntry s site.call.pushes.startPC working.a working.b working.c
        working.d working.e (MaskProjection.mask :: factor :: rho))
      (maskQuadHelperEntry s site.helper.startPC
        p0 p1 p2 p3 site.returnPC c0 c1 c2 c3 working rho) := by
    apply gc.cast rfl
    rw [site.helper_start]
  let t : State :=
    {s with activeWords :=
      (quadActiveWordsAfterUInt256_4 s
        p0.toNat p1.toNat p2.toNat p3.toNat)}
  let words : List UInt256 := roundWords
      (quadWorking s working j p0 p1 p2 p3
        r0 r1 r2 r3 constant) ++ [MaskProjection.mask, factor] ++ rho
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
      maskQuadAfterHelperBeforeJump s site.helper.endPC site.returnPC
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho =
      {t with pc := site.helperJump.pc, stack := site.returnSite.pc :: words} := by
    rw [site.helper_end, site.return_at]
    rfl
  have after :
      {t with pc := site.returnSite.pc.succ, stack := words} =
      {s with
        pc := site.returnSite.pc.succ
        stack := roundWords
          (quadWorking s working j p0 p1 p2 p3
            r0 r1 r2 r3 constant) ++
          [MaskProjection.mask, factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
    rfl
  exact gc'.trans (ghelper.trans (gr.cast before.symm after))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskQuadHelperTrace

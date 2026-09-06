import Challenge.Ripemd160.Submission.Proofs.Bytecode.newMaskProjection
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Mask-cache quad call trace

The optimized wrappers pass four control words and enter a helper with the
mask cache below the five working words.  The push widths are parameters so
the same trace covers the minimal-width shifted-factor pushes in the left
lane and the one-byte controls in the right lane.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskCallTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskProjection
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

def nonemptyPushWidth (w : Fin 32) : Fin 33 :=
  ⟨w.val + 1, by omega⟩

def maskQuadCallPushes
    (w0 w1 w2 w3 : Fin 32)
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (c0 c1 c2 c3 : UInt256) : List Instr :=
  [.push (nonemptyPushWidth w3) c3, push2 p3,
    .push (nonemptyPushWidth w2) c2, push2 p2,
    .push (nonemptyPushWidth w1) c1, push2 p1,
    .push (nonemptyPushWidth w0) c0, push2 returnPC,
    push2 p0, push2 helperPC]

def maskQuadCallPushed (s : State) (pc returnPC p0 p1 p2 p3 helperPC : UInt256)
    (c0 c1 c2 c3 : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := pc
    stack := [helperPC, p0, returnPC, c0, p1, c1, p2, c2, p3, c3] ++
      roundWords working ++ [MaskProjection.mask, factor] ++ rho }

theorem maskQuadCallPushes_advances
    (w0 w1 w2 w3 : Fin 32)
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (c0 c1 c2 c3 : UInt256) :
    ∀ instruction ∈ maskQuadCallPushes w0 w1 w2 w3
      returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [maskQuadCallPushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_maskQuadCallPushes (s : State)
    (pc returnPC p0 p1 p2 p3 helperPC : UInt256)
    (w0 w1 w2 w3 : Fin 32)
    (c0 c1 c2 c3 : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    runInstrSeq (maskQuadCallPushes w0 w1 w2 w3
      returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (MaskProjection.mask :: factor :: rho)) =
    some (maskQuadCallPushed s
      (pcAfter pc (maskQuadCallPushes w0 w1 w2 w3
        returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3))
      returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3 working rho) := by
  have hcap (n : Nat) (hn : n ≤ 17) : rho.length + n < 1024 := by
    omega
  simp (discharger := omega)
    [maskQuadCallPushes, maskQuadCallPushed, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, push2, hrun, hcap, Nat.add_assoc,
      Instr.size_push, Instr.size_op, roundWords, nonemptyPushWidth,
      MaskProjection.mask, factor, Nat.add_comm, Nat.add_left_comm]

theorem runLocatedBlock_maskQuadCallPushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (w0 w1 w2 w3 : Fin 32)
    (c0 c1 c2 c3 : UInt256)
    (site : GenericRoundSite artifact fork
      (maskQuadCallPushes w0 w1 w2 w3
        returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d
        working.e (MaskProjection.mask :: factor :: rho)) =
      some (maskQuadCallPushed s site.endPC returnPC p0 p1 p2 p3 helperPC
        c0 c1 c2 c3 working rho) := by
  have hend : site.endPC = pcAfter site.startPC
      (maskQuadCallPushes w0 w1 w2 w3
        returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site
    (maskQuadCallPushes_advances w0 w1 w2 w3 returnPC p0 p1 p2 p3 helperPC
      c0 c1 c2 c3)
    (roundEntry s site.startPC working.a working.b working.c working.d
      working.e (MaskProjection.mask :: factor :: rho)) rfl]
  rw [runInstrSeq_maskQuadCallPushes s site.startPC returnPC p0 p1 p2 p3
    helperPC w0 w1 w2 w3 c0 c1 c2 c3 working rho hstack hrun, ← hend]

structure CallSite (artifact : ProgramArtifact) (fork : Fork)
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (w0 w1 w2 w3 : Fin 32) (c0 c1 c2 c3 : UInt256) where
  pushes : GenericRoundSite artifact fork
    (maskQuadCallPushes w0 w1 w2 w3
      returnPC p0 p1 p2 p3 helperPC c0 c1 c2 c3)
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = pushes.endPC

def CallSite.path {artifact : ProgramArtifact} {fork : Fork}
    {returnPC p0 p1 p2 p3 helperPC : UInt256}
    {w0 w1 w2 w3 : Fin 32} {c0 c1 c2 c3 : UInt256}
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      w0 w1 w2 w3 c0 c1 c2 c3) : List (Stepper.Located artifact fork) :=
  site.pushes.path ++ [site.jump.located]

theorem runLocatedBlock_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (w0 w1 w2 w3 : Fin 32)
    (c0 c1 c2 c3 : UInt256)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      w0 w1 w2 w3 c0 c1 c2 c3)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.pushes.startPC working.a working.b working.c
        working.d working.e (MaskProjection.mask :: factor :: rho)) =
      some (maskQuadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        c0 c1 c2 c3 working rho) := by
  apply Stepper.runLocatedBlock_append site.pushes.path [site.jump.located] _
    (maskQuadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
      c0 c1 c2 c3 working rho)
  · exact runLocatedBlock_maskQuadCallPushes returnPC p0 p1 p2 p3 helperPC
      w0 w1 w2 w3 c0 c1 c2 c3 site.pushes s working rho hstack hrun
  · exact hrun
  · have hcap :
        ([p0, returnPC, c0, p1, c1, p2, c2, p3, c3] ++
          roundWords working ++ [MaskProjection.mask, factor] ++ rho).length < 1023 := by
      simp [roundWords]
      omega
    have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr s
      helperPC
      ([p0, returnPC, c0, p1, c1, p2, c2, p3, c3] ++
        roundWords working ++ [MaskProjection.mask, factor] ++ rho) hcap hvalid
    have hlocated : Stepper.runLocated site.jump.located
        (maskQuadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC
          c0 c1 c2 c3 working rho) =
        some (maskQuadHelperEntry s helperPC p0 p1 p2 p3 returnPC
          c0 c1 c2 c3 working rho) := by
      simpa [maskQuadCallPushed, maskQuadHelperEntry, roundWords,
        site.jump_pc, MaskProjection.mask, factor] using h
    simp only [Stepper.runLocatedBlock, hlocated]

def gasSteps_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC : UInt256)
    (w0 w1 w2 w3 : Fin 32)
    (c0 c1 c2 c3 : UInt256)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC
      w0 w1 w2 w3 c0 c1 c2 c3)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s site.pushes.startPC working.a working.b working.c
        working.d working.e (MaskProjection.mask :: factor :: rho))
      (maskQuadHelperEntry s helperPC p0 p1 p2 p3 returnPC
        c0 c1 c2 c3 working rho) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_call returnPC p0 p1 p2 p3 helperPC
      w0 w1 w2 w3 c0 c1 c2 c3 site s working rho hstack hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskCallTrace

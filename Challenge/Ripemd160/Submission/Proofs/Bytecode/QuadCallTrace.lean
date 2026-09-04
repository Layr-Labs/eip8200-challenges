import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SharedCallTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-!
# Q4M quad-round call trace

The ten-push wrapper prefix and its helper jump.  The multiplier pushes have
symbolic widths (`PUSH5` or `PUSH6` in the artifact); only `width ≠ 0` matters.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

theorem quadCallPushes_advances (returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256)
    (w0 w1 w2 w3 : Fin 33) :
    ∀ instruction ∈ quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [quadCallPushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

private theorem one_add_val (w : Fin 33) : 1 + w.val = w.val + 1 := Nat.add_comm 1 w.val

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_quadCallPushes (s : State)
    (pc returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256) (w0 w1 w2 w3 : Fin 33)
    (hw0 : w0.val ≠ 0) (hw1 : w1.val ≠ 0) (hw2 : w2.val ≠ 0) (hw3 : w3.val ≠ 0)
    (working : EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1000) (hrun : s.halt = .Running) :
    runInstrSeq (quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3)
      (roundEntry s pc working.a working.b working.c working.d working.e rest) =
    some (quadCallPushed s
      (pcAfter pc (quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3))
      returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 working rest) := by
  have hcap (n : Nat) (hn : n ≤ 15) : rest.length + n < 1024 := by
    omega
  simp (discharger := omega)
    [quadCallPushes, quadCallPushed, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, push2, hrun, hcap, hw0, hw1, hw2, hw3,
      Nat.add_assoc, one_add_val, Instr.size_push, roundWords]

theorem runLocatedBlock_quadCallPushes {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256) (w0 w1 w2 w3 : Fin 33)
    (hw0 : w0.val ≠ 0) (hw1 : w1.val ≠ 0) (hw2 : w2.val ≠ 0) (hw3 : w3.val ≠ 0)
    (site : GenericRoundSite artifact fork
      (quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3))
    (s : State) (working : EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1000) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d working.e rest) =
      some (quadCallPushed s site.endPC
        returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 working rest) := by
  have hend : site.endPC = pcAfter site.startPC
      (quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site
    (quadCallPushes_advances _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (roundEntry s site.startPC working.a working.b working.c working.d working.e rest) rfl]
  rw [runInstrSeq_quadCallPushes s site.startPC returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3
    w0 w1 w2 w3 hw0 hw1 hw2 hw3 working rest hstack hrun, ← hend]

structure CallSite (artifact : ProgramArtifact) (fork : Fork)
    (returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256) (w0 w1 w2 w3 : Fin 33) where
  pushes : GenericRoundSite artifact fork
    (quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3)
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = pushes.endPC
  w0_ne : w0.val ≠ 0
  w1_ne : w1.val ≠ 0
  w2_ne : w2.val ≠ 0
  w3_ne : w3.val ≠ 0

def CallSite.path {artifact : ProgramArtifact} {fork : Fork}
    {returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256} {w0 w1 w2 w3 : Fin 33}
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3) :
    List (Stepper.Located artifact fork) :=
  site.pushes.path ++ [site.jump.located]

theorem runLocatedBlock_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256) (w0 w1 w2 w3 : Fin 33)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3)
    (s : State) (working : EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.pushes.startPC working.a working.b working.c working.d working.e rest) =
      some (quadHelperEntry s helperPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest) := by
  apply Stepper.runLocatedBlock_append site.pushes.path [site.jump.located] _
    (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3
      working rest)
  · exact runLocatedBlock_quadCallPushes returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3
      w0 w1 w2 w3 site.w0_ne site.w1_ne site.w2_ne site.w3_ne site.pushes
      s working rest hstack hrun
  · exact hrun
  · have hcap :
        ([p0, returnPC, M0, p1, M1, p2, M2, p3, M3] ++ roundWords working ++ rest).length
          < 1023 := by
      simp [roundWords]
      omega
    have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr s helperPC
      ([p0, returnPC, M0, p1, M1, p2, M2, p3, M3] ++ roundWords working ++ rest) hcap hvalid
    have hlocated : Stepper.runLocated site.jump.located
        (quadCallPushed s site.pushes.endPC returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3
          working rest) =
        some (quadHelperEntry s helperPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest) := by
      simpa [quadCallPushed, quadHelperEntry, roundWords, site.jump_pc] using h
    simp only [Stepper.runLocatedBlock, hlocated]

def gasSteps_call {artifact : ProgramArtifact} {fork : Fork}
    (returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 : UInt256) (w0 w1 w2 w3 : Fin 33)
    (site : CallSite artifact fork returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3)
    (s : State) (working : EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code helperPC.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (roundEntry s site.pushes.startPC working.a working.b working.c working.d
      working.e rest)
      (quadHelperEntry s helperPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 working rest) := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_call returnPC p0 p1 p2 p3 helperPC M0 M1 M2 M3 w0 w1 w2 w3 site
      s working rest hstack hrun hvalid
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace

import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Adjacent four-round helper calls

The fourth wrapper in each sixteen-round group omits the normal helper-target
push and call jump.  Its nine argument pushes end at the physically adjacent
helper entry.  The helper's existing dynamic return path is unchanged.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadFallthroughTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

def pushes (returnPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  [push1 (UInt256.ofNat (32 - r3)), push2 p3,
    push1 (UInt256.ofNat (32 - r2)), push2 p2,
    push1 (UInt256.ofNat (32 - r1)), push2 p1,
    push1 (UInt256.ofNat (32 - r0)), push2 returnPC,
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
    some (quadHelperEntry s
      (pcAfter pc (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3))
      p0 p1 p2 p3 returnPC r0 r1 r2 r3 working rho) := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  simp (discharger := omega)
    [pushes, quadHelperEntry, roundEntry, runInstrSeq,
      Stepper.runInstr, pcAfter, push1, push2, hrun, hcap,
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
      some (quadHelperEntry s site.endPC p0 p1 p2 p3 returnPC
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

structure RoundSite (artifact : ProgramArtifact) (fork : Fork)
    (j : Nat) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) where
  returnPC : UInt256
  callPushes : GenericRoundSite artifact fork
    (pushes returnPC p0 p1 p2 p3 r0 r1 r2 r3)
  helper : GenericRoundSite artifact fork
    (quadBeforeJumpTemplate j constant)
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
    (constant : UInt256)
    (site : RoundSite artifact fork j p0 p1 p2 p3 r0 r1 r2 r3 constant)
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadFallthroughTrace

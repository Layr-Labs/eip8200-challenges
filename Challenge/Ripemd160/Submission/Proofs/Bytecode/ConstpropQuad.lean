import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamCancel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Private generic proof for a physically inlined quad helper. No artifact
or scorer is changed. The dummy return word keeps the existing helper stack
layout, and a final POP removes it without a dynamic jump. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ConstpropQuad
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

def pushes (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat) : List Instr :=
  [push1 (UInt256.ofNat (32 - r3)), push2 p3,
   push1 (UInt256.ofNat (32 - r2)), push2 p2,
   push1 (UInt256.ofNat (32 - r1)), push2 p1,
   push1 (UInt256.ofNat (32 - r0)), .push ⟨0, by decide⟩ 0, push2 p0]

theorem pushes_advances (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat) :
    ∀ instruction ∈ pushes p0 p1 p2 p3 r0 r1 r2 r3,
      SharedCallTrace.Advances instruction := by
  intro instruction hmem
  simp only [pushes, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Or.inl (StraightLine.push _ _)

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_pushes (s : State) (pc p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (pushes p0 p1 p2 p3 r0 r1 r2 r3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (factor :: rho)) =
      some (quadHelperEntry s (pcAfter pc (pushes p0 p1 p2 p3 r0 r1 r2 r3))
        p0 p1 p2 p3 0 r0 r1 r2 r3 working rho) := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  simp (discharger := omega)
    [pushes, quadHelperEntry, roundEntry, runInstrSeq, Stepper.runInstr,
     pcAfter, push1, push2, hrun, hcap, Nat.add_assoc, Instr.size_push,
     roundWords, factor]
  exact ⟨rfl, rfl⟩

theorem runLocatedBlock_pushes {artifact : ProgramArtifact} {fork : Fork}
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (site : GenericRoundSite artifact fork (pushes p0 p1 p2 p3 r0 r1 r2 r3))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d
        working.e (factor :: rho)) =
      some (quadHelperEntry s site.endPC p0 p1 p2 p3 0
        r0 r1 r2 r3 working rho) := by
  have hend : site.endPC = pcAfter site.startPC (pushes p0 p1 p2 p3 r0 r1 r2 r3) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [SharedCallTrace.runLocatedBlock_eq_raw site (pushes_advances _ _ _ _ _ _ _ _)
    (roundEntry s site.startPC working.a working.b working.c working.d
      working.e (factor :: rho)) rfl]
  rw [runInstrSeq_pushes s site.startPC p0 p1 p2 p3 r0 r1 r2 r3
    working rho hstack hrun, ← hend]

private theorem predecessor_succ (pc : UInt256) : (pc - 1).succ = pc := by
  cases pc with
  | mk value =>
    apply congrArg UInt256.mk
    change (value - 1) + 1 = value
    exact sub_add_cancel value 1

theorem template_head (j : Nat) (hj : j < 5) (constant : UInt256) :
    quadBeforeJumpTemplate j constant =
      [op .JUMPDEST] ++ (quadBeforeJumpTemplate j constant).tail := by
  interval_cases j <;> rfl

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_body (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnWord : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (quadBeforeJumpTemplate j constant).tail
      (quadHelperEntry s startPC p0 p1 p2 p3 returnWord r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter startPC (quadBeforeJumpTemplate j constant).tail)
        returnWord j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  have hfull := QuadRoundTrace.runInstrSeq_quad j hj s (startPC - 1)
    p0 p1 p2 p3 returnWord r0 r1 r2 r3 working constant rho
    hzero hstack hrun hrot0 hrot1 hrot2 hrot3
  have hcap : rho.length + 15 < 1024 := by omega
  have hjd : runInstrSeq [op .JUMPDEST]
      (quadHelperEntry s (startPC - 1) p0 p1 p2 p3 returnWord
        r0 r1 r2 r3 working rho) =
      some (quadHelperEntry s startPC p0 p1 p2 p3 returnWord
        r0 r1 r2 r3 working rho) := by
    simp (discharger := omega) [runInstrSeq, op, Stepper.runInstr, quadHelperEntry, roundWords,
      hcap, predecessor_succ, Nat.add_assoc]
  have hprefix := QuadSeamCancel.runInstrSeq_prepend_running hjd hrun
    (quadBeforeJumpTemplate j constant).tail
  have heq := congrArg
    (fun program => runInstrSeq program
      (quadHelperEntry s (startPC - 1) p0 p1 p2 p3 returnWord
        r0 r1 r2 r3 working rho)) (template_head j hj constant)
  have hpc : pcAfter (startPC - 1) (quadBeforeJumpTemplate j constant) =
      pcAfter startPC (quadBeforeJumpTemplate j constant).tail := by
    calc
      _ = pcAfter (startPC - 1)
          ([op .JUMPDEST] ++ (quadBeforeJumpTemplate j constant).tail) :=
        congrArg (pcAfter (startPC - 1)) (template_head j hj constant)
      _ = _ := by
        rw [QuadRoundState.pcAfter_append]
        change pcAfter (startPC - 1).succ (quadBeforeJumpTemplate j constant).tail = _
        rw [predecessor_succ]
  rw [hpc] at hfull
  exact (heq.trans hprefix).symm.trans hfull

theorem body_advances (j : Nat) (hj : j < 5) (constant : UInt256) :
    ∀ instruction ∈ (quadBeforeJumpTemplate j constant).tail,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  exact QuadHelperTrace.template_advances j hj constant instruction
    (List.mem_of_mem_tail hmem)

theorem runLocatedBlock_body {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5)
    (p0 p1 p2 p3 returnWord : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256)
    (site : GenericRoundSite artifact fork (quadBeforeJumpTemplate j constant).tail)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    Stepper.runLocatedBlock site.path
      (quadHelperEntry s site.startPC p0 p1 p2 p3 returnWord
        r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s site.endPC returnWord j working
        p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  have hend : site.endPC = pcAfter site.startPC (quadBeforeJumpTemplate j constant).tail := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site (body_advances j hj constant)
    (quadHelperEntry s site.startPC p0 p1 p2 p3 returnWord
      r0 r1 r2 r3 working rho) rfl]
  rw [runInstrSeq_body j hj s site.startPC p0 p1 p2 p3 returnWord
    r0 r1 r2 r3 working constant rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3,
    ← hend]

theorem runLocated_pop {artifact : ProgramArtifact} {fork : Fork}
    (site : LocatedSite artifact fork) (hinstr : site.located.instruction = .op .POP)
    (s : State) (dummy : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1023) :
    Stepper.runLocated site.located {s with pc := site.pc, stack := dummy :: rest} =
      some {s with pc := site.pc.succ, stack := rest} := by
  simp [Stepper.runLocated, site.pc_eq, hinstr, Stepper.runInstr, hstack]

structure InlineSite (artifact : ProgramArtifact) (fork : Fork)
    (j : Nat) (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) where
  callPushes : GenericRoundSite artifact fork (pushes p0 p1 p2 p3 r0 r1 r2 r3)
  body : GenericRoundSite artifact fork (quadBeforeJumpTemplate j constant).tail
  body_start : body.startPC = callPushes.endPC
  pop : LocatedSite artifact fork
  pop_instr : pop.located.instruction = .op .POP
  pop_at : pop.pc = body.endPC

/-- One complete physically inline quad: nine argument pushes, the original
arithmetic helper with its entry JUMPDEST removed, and a dummy-word POP.
It requires no code jump-destination assumptions and works for every state
satisfying the inherited generic quad correctness premises. -/
def gasSteps_inline {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (site : InlineSite artifact fork j p0 p1 p2 p3 r0 r1 r2 r3 constant)
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s site.callPushes.startPC working.a working.b working.c
        working.d working.e (factor :: rho))
      {s with
        pc := site.pop.pc.succ
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  have gp : GasSteps
      (roundEntry s site.callPushes.startPC working.a working.b working.c
        working.d working.e (factor :: rho))
      (quadHelperEntry s site.body.startPC p0 p1 p2 p3 0
        r0 r1 r2 r3 working rho) := by
    apply Stepper.runLocatedBlock_sound artifact fork site.callPushes.path
    · exact hcode
    · exact hfork
    · rw [site.body_start]
      exact runLocatedBlock_pushes p0 p1 p2 p3 r0 r1 r2 r3 site.callPushes
        s working rho hstack hrun
    · exact hrun
    · exact hnp
  have gb : GasSteps
      (quadHelperEntry s site.body.startPC p0 p1 p2 p3 0
        r0 r1 r2 r3 working rho)
      (quadAfterHelperBeforeJump s site.body.endPC 0 j working
        p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
    apply Stepper.runLocatedBlock_sound artifact fork site.body.path
    · exact hcode
    · exact hfork
    · exact runLocatedBlock_body j hj p0 p1 p2 p3 0 r0 r1 r2 r3 constant site.body
        s working rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3
    · exact hrun
    · exact hnp
  let t : State :=
    {s with activeWords :=
      quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat}
  let words : List UInt256 := roundWords (quadWorking s working j p0 p1 p2 p3
    r0 r1 r2 r3 constant) ++ [factor] ++ rho
  have hwords : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have hp := runLocated_pop site.pop site.pop_instr t 0 words hwords
  have gr := Stepper.runLocated_sound
    (s := {t with pc := site.pop.pc, stack := 0 :: words})
    hcode hfork hp hrun hnp
  have before : quadAfterHelperBeforeJump s site.body.endPC 0 j working
      p0 p1 p2 p3 r0 r1 r2 r3 constant rho =
      {t with pc := site.pop.pc, stack := 0 :: words} := by
    rw [site.pop_at]
    rfl
  have after : {t with pc := site.pop.pc.succ, stack := words} =
      {s with
        pc := site.pop.pc.succ
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := rfl
  exact gp.trans (gb.trans (gr.cast before.symm after))


def specializedTemplate (j : Nat) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) : List Instr :=
  match j with
  | 0 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | 1 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨3, by decide⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨4, by decide⟩),
     .op .AND,
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨3, by decide⟩),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨4, by decide⟩),
     .op .AND,
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | 2 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨5, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨2, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | 3 =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .AND,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨2, by decide⟩),
     .op .AND,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨2, by decide⟩),
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨5, by decide⟩),
     .op .AND,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨3, by decide⟩),
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op (.Dup ⟨2, by decide⟩),
     .op .AND,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]
  | _ =>
    [.push 2 (p0),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r0)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p1),
     .op .MLOAD,
     .op (.Dup ⟨1, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r1)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩),
     .push 2 (p2),
     .op .MLOAD,
     .op (.Dup ⟨4, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨4, by decide⟩),
     .op .OR,
     .op (.Dup ⟨3, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r2)),
     .op .SHR,
     .op (.Dup ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨1, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .push 2 (p3),
     .op .MLOAD,
     .op (.Dup ⟨1, by decide⟩),
     .op .NOT,
     .op (.Dup ⟨3, by decide⟩),
     .op .OR,
     .op (.Dup ⟨4, by decide⟩),
     .op .XOR,
     .op .ADD,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Swap ⟨4, by decide⟩),
     .op .ADD,
     .push 4 (constant),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat (32 - r3)),
     .op .SHR,
     .op (.Dup ⟨3, by decide⟩),
     .op .ADD,
     .push 4 (UInt256.ofNat 4294967295),
     .op .AND,
     .op (.Swap ⟨0, by decide⟩),
     .op (.Dup ⟨5, by decide⟩),
     .op .MUL,
     .push 1 (UInt256.ofNat 22),
     .op .SHR,
     .op (.Swap ⟨2, by decide⟩)]

def originalInlineTemplate (j : Nat) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) : List Instr :=
  pushes p0 p1 p2 p3 r0 r1 r2 r3 ++
    ((quadBeforeJumpTemplate j constant).tail ++ [.op .POP])

set_option linter.unusedSimpArgs false in
theorem specialized_equiv (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    runInstrSeq (specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: rho)) =
    Option.map
      (fun out => {out with pc := pcAfter startPC (specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant)})
      (runInstrSeq (originalInlineTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant)
        (roundEntry s startPC working.a working.b working.c working.d working.e
          (factor :: rho))) := by
  have hcap (m : Nat) (hm : m ≤ 17) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  interval_cases j <;> simp (config := { maxSteps := 3000000 })
    [specializedTemplate, originalInlineTemplate, pushes,
     quadBeforeJumpTemplate, QuadGapTemplate.firstFTemplate,
     QuadRoundTemplate.cachedTailFTemplate, QuadGapTemplate.firstBoolean,
     QuadGapTemplate.secondBoolean, QuadGapTemplate.d, QuadGapTemplate.w,
     cachedQrot10, cachedCfold9, cachedQrot8, cachedCfold7,
     cachedDup10, cachedDup9, cachedDup8, cachedDup7,
     PairRoundTemplate.pairFirstBooleanOps, PairRoundTemplate.pairSecondBooleanOps,
     PairRoundTemplate.pairDup7, PairRoundTemplate.pairDup8,
     PairRoundTemplate.pairDup9, PairRoundTemplate.pairDup10,
     PairRoundTemplate.pairSwap5, PairRoundTemplate.pairSwap7,
     roundEntry, roundWords, op, push1, push2, push4, c22, mask,
     dup1, dup2, dup3, dup4, dup5, dup6, swap1, swap2, swap3, swap4,
     runInstrSeq, Stepper.runInstr, pcAfter, List.exchange,
     hrun, hcap, UInt256.succ, Instr.size, Instr.size_op, Instr.size_push,
     State.activeWordsAfterUInt256, hadd, Word.ofNat_add_mod,
     Word.word_toNat_ofNat, Nat.add_assoc, Word.word_add_comm]


theorem runInstrSeq_pop (s : State) (pc dummy : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1023) :
    runInstrSeq [.op .POP] {s with pc := pc, stack := dummy :: rest} =
      some {s with pc := pc.succ, stack := rest} := by
  have hcap : rest.length + 1 < 1024 := by omega
  simp [runInstrSeq, Stepper.runInstr, hcap]

attribute [local irreducible] runInstrSeq pushes quadBeforeJumpTemplate
/- Raw execution of the un-specialized inline quad, assembled compositionally
from the existing arbitrary-state quad theorem. -/
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 50000 in
set_option backward.isDefEq.respectTransparency true in
theorem runInstrSeq_original (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (working : Compression.EvmWorking) (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (originalInlineTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: rho)) =
      some {s with
        pc := pcAfter startPC (originalInlineTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant)
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  let pcP := pcAfter startPC (pushes p0 p1 p2 p3 r0 r1 r2 r3)
  let pcB := pcAfter pcP (quadBeforeJumpTemplate j constant).tail
  let t : State := {s with activeWords := quadActiveWordsAfterUInt256_4 s p0.toNat p1.toNat p2.toNat p3.toNat}
  let words := roundWords (quadWorking s working j p0 p1 p2 p3
    r0 r1 r2 r3 constant) ++ [factor] ++ rho
  have hp := runInstrSeq_pushes s startPC p0 p1 p2 p3 r0 r1 r2 r3
    working rho hstack hrun
  have hb := runInstrSeq_body j hj s pcP p0 p1 p2 p3 0 r0 r1 r2 r3
    working constant rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3
  have hwords : words.length < 1023 := by
    simp [words, roundWords]
    omega
  have hpop := runInstrSeq_pop t pcB 0 words hwords
  have hbodyeq := QuadSeamCancel.runInstrSeq_prepend_running hb hrun [.op .POP]
  have hbody := hbodyeq.trans hpop
  have hprun :
      (quadHelperEntry s (pcAfter startPC (pushes p0 p1 p2 p3 r0 r1 r2 r3))
        p0 p1 p2 p3 0 r0 r1 r2 r3 working rho).halt = .Running := by
    simpa only [quadHelperEntry] using hrun
  have hpusheq :
      runInstrSeq (pushes p0 p1 p2 p3 r0 r1 r2 r3 ++
          ((quadBeforeJumpTemplate j constant).tail ++ [.op .POP]))
        (roundEntry s startPC working.a working.b working.c working.d working.e
          (factor :: rho)) =
      runInstrSeq ((quadBeforeJumpTemplate j constant).tail ++ [.op .POP])
        (quadHelperEntry s (pcAfter startPC (pushes p0 p1 p2 p3 r0 r1 r2 r3))
          p0 p1 p2 p3 0 r0 r1 r2 r3 working rho) := by
    exact @QuadSeamCancel.runInstrSeq_prepend_running
      (pushes p0 p1 p2 p3 r0 r1 r2 r3)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: rho))
      (quadHelperEntry s (pcAfter startPC (pushes p0 p1 p2 p3 r0 r1 r2 r3))
        p0 p1 p2 p3 0 r0 r1 r2 r3 working rho) hp hprun
      ((quadBeforeJumpTemplate j constant).tail ++ [.op .POP])
  have hall := hpusheq.trans hbody
  have hpc : pcAfter startPC
      (originalInlineTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant) = pcB.succ := by
    rw [originalInlineTemplate, QuadRoundState.pcAfter_append,
      QuadRoundState.pcAfter_append]
    rfl
  rw [hpc]
  exact hall

/-- Constant-propagated quad arithmetic is correct for arbitrary inputs and
memory, not merely for concrete scored vectors. -/
theorem runInstrSeq_specialized (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (working : Compression.EvmWorking) (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant)
      (roundEntry s startPC working.a working.b working.c working.d working.e
        (factor :: rho)) =
      some {s with
        pc := pcAfter startPC (specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant)
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  rw [specialized_equiv j hj s startPC p0 p1 p2 p3 r0 r1 r2 r3
    constant working rho hstack hrun]
  rw [runInstrSeq_original j hj s startPC p0 p1 p2 p3 r0 r1 r2 r3
    working constant rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3]
  rfl

set_option linter.unusedSimpArgs false in
theorem specialized_advances (j : Nat) (hj : j < 5)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat) (constant : UInt256) :
    ∀ instruction ∈ specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant,
      PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  interval_cases j <;> simp [specializedTemplate] at hmem <;>
    simp_all [PairMultiplyLift.Advances, SharedCallTrace.Advances] <;>
    aesop (add safe constructors StraightLine)

theorem runLocatedBlock_specialized {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    Stepper.runLocatedBlock site.path
      (roundEntry s site.startPC working.a working.b working.c working.d working.e
        (factor :: rho)) =
      some {s with
        pc := site.endPC
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  have hend : site.endPC = pcAfter site.startPC
      (specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [PairMultiplyLift.runLocatedBlock_eq_raw site
    (specialized_advances j hj p0 p1 p2 p3 r0 r1 r2 r3 constant)
    (roundEntry s site.startPC working.a working.b working.c working.d working.e
      (factor :: rho)) rfl]
  rw [runInstrSeq_specialized j hj s site.startPC p0 p1 p2 p3 r0 r1 r2 r3
    working constant rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3, ← hend]

def gasSteps_specialized {artifact : ProgramArtifact} {fork : Fork}
    (j : Nat) (hj : j < 5) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256)
    (site : GenericRoundSite artifact fork
      (specializedTemplate j p0 p1 p2 p3 r0 r1 r2 r3 constant))
    (s : State) (working : Compression.EvmWorking) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      (roundEntry s site.startPC working.a working.b working.c working.d working.e
        (factor :: rho))
      {s with
        pc := site.endPC
        stack := roundWords (quadWorking s working j p0 p1 p2 p3
          r0 r1 r2 r3 constant) ++ [factor] ++ rho
        activeWords := quadActiveWordsAfterUInt256_4 s
          p0.toNat p1.toNat p2.toNat p3.toNat} := by
  exact Stepper.runLocatedBlock_sound artifact fork site.path hcode hfork
    (runLocatedBlock_specialized j hj p0 p1 p2 p3 r0 r1 r2 r3 constant
      site s working rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3) hrun hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ConstpropQuad

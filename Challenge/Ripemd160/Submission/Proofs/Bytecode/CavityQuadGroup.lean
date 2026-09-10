import Challenge.Ripemd160.Submission.Proofs.Bytecode.ConstpropQuad
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityQuadGroup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate

/-- All control parameters of one four-round computation, not message values. -/
structure Params where
  function : Fin 5
  address : Fin 4 → UInt256
  rotation : Fin 4 → Nat
  constant : UInt256
  rotations_bounded : ∀ i, rotation i ≤ 32
  constant_zero : function.val = 0 → constant = 0

def Params.template (q : Params) : List Instr :=
  ConstpropQuad.specializedTemplate q.function.val
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) q.constant

def Params.apply (q : Params) (s : State) (w : Compression.EvmWorking) :
    Compression.EvmWorking :=
  quadWorking s w q.function.val
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) q.constant

def Params.Fits (q : Params) (s : State) : Prop :=
  ∀ i, (q.address i).toNat + 32 ≤ s.activeWords.toNat * 32

def stateAt (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  roundEntry s pc w.a w.b w.c w.d w.e (factor :: rho)

theorem runInstrSeq_quad (q : Params) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : q.Fits s) (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    runInstrSeq q.template (stateAt s pc w rho) =
      some (stateAt s (pcAfter pc q.template) (q.apply s w) rho) := by
  have h := ConstpropQuad.runInstrSeq_specialized q.function.val q.function.isLt s pc
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    w q.constant rho q.constant_zero hstack hrun
    (q.rotations_bounded 0) (q.rotations_bounded 1)
    (q.rotations_bounded 2) (q.rotations_bounded 3)
  rw [QuadSemantic.quadActiveWordsAfterUInt256_4_eq_of_end_le s
    _ _ _ _ (hfit 0) (hfit 1) (hfit 2) (hfit 3)] at h
  exact h

def gasSteps_quad {artifact : ProgramArtifact} {fork : Fork}
    (q : Params) (site : GenericRoundSite artifact fork q.template)
    (s : State) (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : q.Fits s) (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s site.startPC w rho)
      (stateAt s site.endPC (q.apply s w) rho) := by
  have h := ConstpropQuad.gasSteps_specialized q.function.val q.function.isLt
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    q.constant site s w rho q.constant_zero hstack hrun
    (q.rotations_bounded 0) (q.rotations_bounded 1)
    (q.rotations_bounded 2) (q.rotations_bounded 3) hcode hfork hnp
  rw [QuadSemantic.quadActiveWordsAfterUInt256_4_eq_of_end_le s
    _ _ _ _ (hfit 0) (hfit 1) (hfit 2) (hfit 3)] at h
  exact h

def workingAfter (qs : Nat → Params) (s : State)
    (w : Compression.EvmWorking) : Nat → Compression.EvmWorking
  | 0 => w
  | n + 1 => (qs n).apply s (workingAfter qs s w n)

/-- Four exact quad certificates compose without changing the frame, memory,
active-word count, factor word, or arbitrary stack suffix. -/
def gasSteps_four {artifact : ProgramArtifact} {fork : Fork}
    (qs : Nat → Params)
    (sites : (k : Fin 4) → GenericRoundSite artifact fork (qs k.val).template)
    (pc : Nat → UInt256)
    (hstart : ∀ k, (sites k).startPC = pc k.val)
    (hend : ∀ k, (sites k).endPC = pc (k.val + 1))
    (s : State) (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : ∀ k : Fin 4, (qs k.val).Fits s)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (stateAt s (pc 0) w rho)
      (stateAt s (pc 4) (workingAfter qs s w 4) rho) := by
  let states := fun n => stateAt s (pc n) (workingAfter qs s w n) rho
  have step (n : Nat) (hn : n < 4) : GasSteps (states n) (states (n + 1)) := by
    let k : Fin 4 := ⟨n, hn⟩
    have g := gasSteps_quad (qs n) (sites k) s (workingAfter qs s w n) rho
      (hfit k) hstack hrun hcode hfork hnp
    rw [hstart k, hend k] at g
    exact g
  exact GasSteps.iterateBounded 4 step

/-- A certified transfer consumes its PUSH/JUMP and destination JUMPDEST. -/
structure Bridge (artifact : ProgramArtifact) (fork : Fork) where
  push : LocatedSite artifact fork
  jump : LocatedSite artifact fork
  destination : LocatedSite artifact fork
  push_instr : push.located.instruction = .push ⟨2, by decide⟩ destination.pc
  jump_instr : jump.located.instruction = .op .JUMP
  destination_instr : destination.located.instruction = .op .JUMPDEST
  jump_at : jump.pc = push.pc + 3

def Bridge.path {artifact : ProgramArtifact} {fork : Fork}
    (b : Bridge artifact fork) : List (Stepper.Located artifact fork) :=
  [b.push.located, b.jump.located, b.destination.located]

theorem run_bridge {artifact : ProgramArtifact} {fork : Fork}
    (b : Bridge artifact fork) (s : State) (stack : List UInt256)
    (hstack : stack.length < 1023) (hcode : s.executionEnv.code = artifact.code)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock b.path {s with pc := b.push.pc, stack := stack} =
      some {s with pc := b.destination.pc.succ, stack := stack} := by
  have hdest : Decode.isValidJumpDest s.executionEnv.code b.destination.pc.toNat = true := by
    rw [hcode, b.destination.pc_eq]
    apply artifact.isValidJumpDest_index
    simpa only [b.destination_instr] using b.destination.located.atIndex
  have hdest' : Decode.isValidJumpDest s.executionEnv.code
      (artifact.instructionPC b.destination.located.index) = true := by
    simpa only [b.destination.pc_eq] using hdest
  have hjump : (b.push.pc + UInt256.ofNat 3).toNat =
      artifact.instructionPC b.jump.located.index := by
    change (b.push.pc + 3).toNat = _
    rw [← b.jump_at]
    exact b.jump.pc_eq
  have hcap : stack.length < 1024 := by omega
  have hcapPush : stack.length + 1 < 1024 := by omega
  simp [Bridge.path, Stepper.runLocatedBlock, Stepper.runLocated,
    b.push_instr, b.jump_instr, b.destination_instr, Stepper.runInstr,
    b.push.pc_eq, b.destination.pc_eq, hjump,
    hrun, hdest', hcap, hcapPush]

def gasSteps_bridge {artifact : ProgramArtifact} {fork : Fork}
    (b : Bridge artifact fork) (s : State) (stack : List UInt256)
    (hstack : stack.length < 1023) (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := b.push.pc, stack := stack}
      {s with pc := b.destination.pc.succ, stack := stack} := by
  exact Stepper.runLocatedBlock_sound artifact fork b.path hcode hfork
    (run_bridge b s stack hstack hcode hrun) hrun hnp

/-- A degenerate `Bridge` whose target is the instruction that follows the
jump.  Replacing that `JUMP` with `POP` consumes the pushed target and then
falls through the destination `JUMPDEST`, preserving the endpoint. -/
structure PopBridge (artifact : ProgramArtifact) (fork : Fork) where
  push : LocatedSite artifact fork
  pop : LocatedSite artifact fork
  destination : LocatedSite artifact fork
  push_instr : push.located.instruction = .push ⟨2, by decide⟩ destination.pc
  pop_instr : pop.located.instruction = .op .POP
  destination_instr : destination.located.instruction = .op .JUMPDEST
  pop_at : pop.pc = push.pc + 3
  destination_at : destination.pc = pop.pc.succ

def PopBridge.path {artifact : ProgramArtifact} {fork : Fork}
    (b : PopBridge artifact fork) : List (Stepper.Located artifact fork) :=
  [b.push.located, b.pop.located, b.destination.located]

theorem run_popBridge {artifact : ProgramArtifact} {fork : Fork}
    (b : PopBridge artifact fork) (s : State) (stack : List UInt256)
    (hstack : stack.length < 1023) (_hcode : s.executionEnv.code = artifact.code)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock b.path {s with pc := b.push.pc, stack := stack} =
      some {s with pc := b.destination.pc.succ, stack := stack} := by
  have hpop : (b.push.pc + UInt256.ofNat 3).toNat =
      artifact.instructionPC b.pop.located.index := by
    change (b.push.pc + 3).toNat = _
    rw [← b.pop_at]
    exact b.pop.pc_eq
  have hchain : (b.push.pc + UInt256.ofNat 3).succ = b.destination.pc := by
    rw [b.destination_at, b.pop_at]
    rfl
  have hcap : stack.length < 1024 := by omega
  have hcapPush : stack.length + 1 < 1024 := by omega
  simp [PopBridge.path, Stepper.runLocatedBlock, Stepper.runLocated,
    b.push_instr, b.pop_instr, b.destination_instr, Stepper.runInstr,
    b.push.pc_eq, hpop, hchain, b.destination.pc_eq,
    hrun, hcap, hcapPush]

def gasSteps_popBridge {artifact : ProgramArtifact} {fork : Fork}
    (b : PopBridge artifact fork) (s : State) (stack : List UInt256)
    (hstack : stack.length < 1023) (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := b.push.pc, stack := stack}
      {s with pc := b.destination.pc.succ, stack := stack} := by
  exact Stepper.runLocatedBlock_sound artifact fork b.path hcode hfork
    (run_popBridge b s stack hstack hcode hrun) hrun hnp

#print axioms runInstrSeq_quad
#print axioms gasSteps_quad
#print axioms gasSteps_four
#print axioms run_bridge
#print axioms gasSteps_bridge
#print axioms run_popBridge
#print axioms gasSteps_popBridge

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityQuadGroup

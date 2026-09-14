import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

structure Paths (artifact : ProgramArtifact) (fork : Fork) extends WindowTwentyOneGasCore.Paths artifact fork where
  width : Block artifact fork 1752 WindowTwentyOneEntry.widthProgram
  miss : Block artifact fork 1771 WindowTwentyOneEntry.missProgram
  base : Block artifact fork 1774 WindowTwentyOneEntry.baseProgram
  normalize : Block artifact fork 1775 WindowTwentyOneEntry.normalizeProgram
  zeroReturn : Block artifact fork 2387 WindowTwentyOneReturn.zeroProgram
  hitJump : Decode.isValidJumpDest artifact.code 42 = true
  zeroJump : Decode.isValidJumpDest artifact.code 2387 = true
  trampJump : Decode.isValidJumpDest artifact.code 1905 = true
  missJump : Decode.isValidJumpDest artifact.code 143 = true

def context_env {artifact : ProgramArtifact} {fork : Fork} (template : State)
    (env : Environment artifact fork template) (input : ByteArray) :
    Environment artifact fork (context template input) where
  sizeBound := env.sizeBound
  code := env.code
  forkEq := env.forkEq
  running := env.running
  noPrecompile := env.noPrecompile

private def lift {artifact : ProgramArtifact} {fork : Fork} {pc : Nat} {instructions : List Instr}
    (block : Block artifact fork pc instructions) {s t : State}
    (hrun : runInstructions instructions s = some t) (env : Environment artifact fork s)
    (hpc : s.pc = UInt256.ofNat pc) : GasSteps s t := block.steps env hpc hrun

private theorem jump_env {artifact : ProgramArtifact} {fork : Fork} {template : State}
    (env : Environment artifact fork template) {pc : Nat}
    (hjump : Decode.isValidJumpDest artifact.code pc = true) :
    Decode.isValidJumpDest template.executionEnv.code pc = true := by
  rw [env.code]
  exact hjump

/-- The state at the core entry 2240 (0x8c0): the route frame with the modulus
word loaded by the special-modulus test still on top. -/
def entryState (template : State) (input : ByteArray) : State :=
  WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 1774)
    (WindowTwentyOneInput.modulusWord input :: routeStack input)

def positive_steps {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    GasSteps (entryState template input) (returned template input) := by
  let ctx := context template input
  have ec := context_env template env input
  have hb := WindowTwentyOneEntry.run_base ctx (WindowTwentyOneInput.modulusWord input)
    (routeStack input) (by simp [routeStack])
  have hn := WindowTwentyOneEntry.run_normalize ctx (WindowTwentyOneInput.modulusWord input)
    (UInt256.ofNat 96) (baseSize input) hmatch.1 (routeStack input) (by simp [routeStack]) rfl rfl
  have hn' : runInstructions WindowTwentyOneEntry.normalizeProgram
      (WindowTwentyOneEntry.framed ctx (UInt256.ofNat 1775)
        (WindowTwentyOneInput.modulusWord input :: routeStack input)) =
      some (normalized template input) := by
    simpa only [normalized, WindowTwentyOneTablePrelude.initial, WindowTwentyOneEntry.framed,
      WindowTwentyOneInput.baseWord, ctx, context, List.cons_append, List.nil_append,
      show (UInt256.ofNat 96).toNat = 96 by decide] using hn
  let gb := lift paths.base hb (ec.transfer rfl rfl) rfl
  let gn := lift paths.normalize hn' (ec.transfer rfl rfl) rfl
  have gc := WindowTwentyOneGasCore.steps_core paths.toPaths ctx ec
    (WindowTwentyOneInput.baseWord input) (WindowTwentyOneInput.modulusWord input)
    (exponentOffset input) (modulusOffset input) (routeStack input)
    (by simp [routeStack]) rfl rfl (modulus_at template input hmatch) (jump_env ec paths.trampJump)
  have gc' : GasSteps (normalized template input) (returned template input) := by
    simpa only [normalized, returned, ctx, exponent_at template input hmatch.1] using gc
  exact (gb.trans gn).trans gc'

def Handled (template : State) (input : ByteArray) : Prop :=
  ∃ final : State, Nonempty (GasSteps (entryState template input) final) ∧
    final.isDone = true ∧ final.toResult = .returned (spec input)

/-- Every accepted width, including a zero-width base, is handled by the main
path from 2240: there is no separate zero-base exit.  Since the zero-modulus
guard was removed, a zero modulus is handled by this same path too: every
`MULMOD` against a zero modulus returns zero, so the accumulator collapses and
the unchanged return path emits the 32 zero bytes the old handler returned. -/
def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    Handled template input := by
  refine ⟨returned template input, ⟨positive_steps paths template env input hmatch⟩, ?_,
    returned_spec template input hmatch⟩
  change (true && template.callStack.isEmpty) = true
  rw [hcall]
  rfl

private def widthTail (input : ByteArray) : List UInt256 := (routeStack input).drop 3

private theorem width_raw (template : State) (input : ByteArray)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 42 = true) :
    runInstructions WindowTwentyOneEntry.widthProgram (state template input (UInt256.ofNat 1752)) =
    some (state template input
      (if (WindowTwentyOneInput.guardDiff input).toNat = 0 then UInt256.ofNat 42 else UInt256.ofNat 1771)) := by
  have h := WindowTwentyOneEntry.run_width (context template input)
    (UInt256.ofNat (baseSize input)) (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
    (widthTail input) (by simp [widthTail, routeStack]) hjump
  have hd : WindowTwentyOneEntry.widthDiff
      (UInt256.ofNat (baseSize input)) (UInt256.ofNat (exponentSize input))
      (UInt256.ofNat (modulusSize input)) = WindowTwentyOneInput.guardDiff input := rfl
  rw [hd] at h
  simpa only [widthTail, routeStack, state, List.drop_succ_cons, List.drop_zero,
    List.cons_append, List.nil_append] using h

private theorem guard_zero_iff (input : ByteArray) :
    (WindowTwentyOneInput.guardDiff input).toNat = 0 ↔ WindowTwentyOneInput.Matches input := by
  rw [← WindowTwentyOneInput.guardDiff_eq_zero_iff]
  constructor
  · intro h
    apply Challenge.EvmProof.Word.word_ext
    exact h
  · intro h
    rw [h]
    rfl

def steps_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    GasSteps (state template input (UInt256.ofNat 1752)) (state template input (UInt256.ofNat 42)) := by
  have h := width_raw template input (jump_env env paths.hitJump)
  rw [if_pos ((guard_zero_iff input).mpr hmatch)] at h
  exact lift paths.width h ((context_env template env input).transfer rfl rfl) rfl

def steps_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hmatch : ¬ WindowTwentyOneInput.Matches input) :
    GasSteps (state template input (UInt256.ofNat 1752)) (state template input (UInt256.ofNat 143)) := by
  have h := width_raw template input (jump_env env paths.hitJump)
  have hn : (WindowTwentyOneInput.guardDiff input).toNat ≠ 0 := by
    intro hz
    exact hmatch ((guard_zero_iff input).mp hz)
  rw [if_neg hn] at h
  have hm := WindowTwentyOneEntry.run_miss (context template input) (routeStack input)
    (by simp [routeStack]) (jump_env env paths.missJump)
  have ec := context_env template env input
  exact (lift paths.width h (ec.transfer rfl rfl) rfl).trans
    (lift paths.miss hm (ec.transfer rfl rfl) rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

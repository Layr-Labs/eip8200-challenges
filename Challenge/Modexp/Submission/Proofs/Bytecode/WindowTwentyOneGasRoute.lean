import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

structure Paths (artifact : ProgramArtifact) (fork : Fork) extends WindowTwentyOneGasCore.Paths artifact fork where
  base : Block artifact fork 813 WindowTwentyOneEntry.baseProgram
  modulus : Block artifact fork 814 WindowTwentyOneEntry.modulusProgram
  normalize : Block artifact fork 817 WindowTwentyOneEntry.normalizeProgram
  genJump : Decode.isValidJumpDest artifact.code 103 = true
  missJump : Decode.isValidJumpDest artifact.code 135 = true

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

/-- The state at the core entry 872: the frame built at 24 or 103 with the
modulus word on top. -/
def entryState (template : State) (input : ByteArray) (tail : List UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 813)
    (WindowTwentyOneInput.modulusWord input :: coreStack input tail)

/-- Base, spare modulus copy, normalization and the whole window core.  No
modulus hypothesis: a zero modulus flows through the same instructions. -/
def core_steps {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590) :
    GasSteps (entryState template input tail) (returned template input tail) := by
  let ctx := context template input
  have ec := context_env template env input
  have hb := WindowTwentyOneEntry.run_base ctx (WindowTwentyOneInput.modulusWord input)
    (coreStack input tail) (by simp [coreStack]; omega)
  have hm := WindowTwentyOneEntry.run_modulus ctx (WindowTwentyOneInput.modulusWord input)
    (coreStack input tail) (by simp [coreStack]; omega)
  have hn := WindowTwentyOneEntry.run_normalize ctx (WindowTwentyOneInput.modulusWord input)
    (shiftWord input) (WindowTwentyOneInput.modulusWord input :: coreStack input tail)
    (by simp [coreStack]; omega) rfl
  have hn' : runInstructions WindowTwentyOneEntry.normalizeProgram
      (WindowTwentyOneEntry.framed ctx (UInt256.ofNat 817)
        (UInt256.ofNat 96 :: WindowTwentyOneInput.modulusWord input ::
          WindowTwentyOneInput.modulusWord input :: coreStack input tail)) =
      some (normalized template input tail) := by
    simpa only [normalized, WindowTwentyOneTablePrelude.initial, WindowTwentyOneEntry.framed,
      WindowTwentyOneInput.baseWord, shiftWord, ctx, context, List.cons_append,
      List.nil_append] using hn
  let gb := lift paths.base hb (ec.transfer rfl rfl) rfl
  let gm := lift paths.modulus hm (ec.transfer rfl rfl) rfl
  let gn := lift paths.normalize hn' (ec.transfer rfl rfl) rfl
  have gc := WindowTwentyOneGasCore.steps_core paths.toPaths ctx ec
    (WindowTwentyOneInput.baseWord input) (WindowTwentyOneInput.modulusWord input)
    (WindowTwentyOneInput.exponentWord input)
    (WindowTwentyOneInput.modulusWord input :: coreStack input tail)
    (by simp [coreStack]; omega) rfl rfl
  have gc' : GasSteps (normalized template input tail) (returned template input tail) := by
    simpa only [normalized, returned, ctx] using gc
  exact ((gb.trans gm).trans gn).trans gc'

def Handled (template : State) (input : ByteArray) (tail : List UInt256) : Prop :=
  ∃ final : State, Nonempty (GasSteps (entryState template input tail) final) ∧
    final.isDone = true ∧ final.toResult = .returned (spec input)

/-- Every accepted width and every modulus, including zero, is handled by the
single main path from 872. -/
def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray) (tail : List UInt256)
    (htail : tail.length ≤ 590) (hmatch : WindowTwentyOneInput.Matches input) :
    Handled template input tail := by
  refine ⟨returned template input tail, ⟨core_steps paths template env input tail htail⟩, ?_,
    returned_spec template input tail hmatch⟩
  change (true && template.callStack.isEmpty) = true
  rw [hcall]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

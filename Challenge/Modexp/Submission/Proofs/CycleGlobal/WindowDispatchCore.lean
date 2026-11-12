import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive

set_option warningAsError true

namespace CycleSubmission.Global.WindowDispatchCore

open Challenge.Modexp Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

structure Paths (artifact : ProgramArtifact) (fork : Fork) extends WindowTwentyOneGasCore.Paths artifact fork where
  base : Block artifact fork 717 WindowTwentyOneEntry.baseProgram
  modulus : Block artifact fork 718 WindowTwentyOneEntry.modulusProgram

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

def entryState (template : State) (input : ByteArray) (tail : List UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 717)
    (WindowTwentyOneInput.modulusWord input :: coreStack input tail)

def core_steps {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590) :
    GasSteps (entryState template input tail) (returned template input tail) := by
  let ctx := context template input
  have ec := context_env template env input
  have hb := WindowTwentyOneEntry.run_base ctx (WindowTwentyOneInput.modulusWord input)
    (coreStack input tail) (by simp [coreStack]; omega)
  have hm := WindowTwentyOneEntry.run_modulus ctx (WindowTwentyOneInput.modulusWord input)
    (shiftWord input) (coreStack input tail) (by simp [coreStack]; omega) rfl
  have hm' : runInstructions WindowTwentyOneEntry.modulusProgram
      (WindowTwentyOneEntry.framed ctx (UInt256.ofNat 718)
        (WindowTwentyOneInput.modulusWord input :: coreStack input tail)) =
      some (normalized template input tail) := by
    simpa only [normalized, WindowTwentyOneTablePrelude.initial, WindowTwentyOneEntry.framed,
      shiftWord, ctx, context, List.cons_append, List.nil_append] using hm
  let gb := lift paths.base hb (ec.transfer rfl rfl) rfl
  let gm := lift paths.modulus hm' (ec.transfer rfl rfl) rfl
  have gc := WindowTwentyOneGasCore.steps_core paths.toPaths ctx ec
    (WindowTwentyOneInput.baseWord input) (WindowTwentyOneInput.modulusWord input)
    (WindowTwentyOneInput.exponentWord input)
    (WindowTwentyOneInput.modulusWord input :: coreStack input tail)
    (by simp [coreStack]; omega) rfl rfl
  have gc' : GasSteps (normalized template input tail) (returned template input tail) := by
    simpa only [normalized, returned, ctx] using gc
  exact (gb.trans gm).trans gc'

def Handled (template : State) (input : ByteArray) (tail : List UInt256) : Prop :=
  ∃ final : State, Nonempty (GasSteps (entryState template input tail) final) ∧
    final.isDone = true ∧ final.toResult = .returned (spec input)

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

end CycleSubmission.Global.WindowDispatchCore

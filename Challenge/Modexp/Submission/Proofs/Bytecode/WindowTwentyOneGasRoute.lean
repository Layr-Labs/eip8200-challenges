import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

structure Paths (artifact : ProgramArtifact) (fork : Fork) extends WindowTwentyOneGasCore.Paths artifact fork where
  entryBridge : Block artifact fork 2613 WindowTwentyOneEntry.bridgeProgram
  entryJump : Decode.isValidJumpDest artifact.code 2416 = true
  width : Block artifact fork 2416 WindowTwentyOneEntry.widthProgram
  miss : Block artifact fork 2436 WindowTwentyOneEntry.missProgram
  base : Block artifact fork 2440 WindowTwentyOneEntry.baseProgram
  modulus : Block artifact fork 2447 WindowTwentyOneEntry.modulusProgram
  normalize : Block artifact fork 2455 WindowTwentyOneEntry.normalizeProgram
  emptyReturn : Block artifact fork 3095 WindowTwentyOneReturn.emptyProgram
  zeroReturn : Block artifact fork 3087 WindowTwentyOneReturn.zeroProgram
  hitJump : Decode.isValidJumpDest artifact.code 4873 = true
  emptyJump : Decode.isValidJumpDest artifact.code 3095 = true
  zeroJump : Decode.isValidJumpDest artifact.code 3087 = true
  loopJump : Decode.isValidJumpDest artifact.code 2618 = true
  missJump : Decode.isValidJumpDest artifact.code 517 = true

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

private theorem base_positive (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input)
    (hbase : 0 < baseSize input) : (UInt256.ofNat (baseSize input)).toNat ≠ 0 := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by have := hmatch.1; omega)]
  omega

def positive_steps {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : 0 < (WindowTwentyOneInput.modulusWord input).toNat) :
    GasSteps (state template input (UInt256.ofNat 2440)) (returned template input) := by
  let ctx := context template input
  have ec := context_env template env input
  have hb := WindowTwentyOneEntry.run_base ctx (UInt256.ofNat (baseSize input))
    (routeStack input) (by simp [routeStack]) rfl (jump_env ec paths.emptyJump)
  rw [if_neg (base_positive input hmatch hbase)] at hb
  have hm := WindowTwentyOneEntry.run_modulus ctx (modulusOffset input)
    (routeStack input) (by simp [routeStack]) rfl (jump_env ec paths.zeroJump)
  dsimp only at hm
  rw [modulus_at template input hmatch, if_neg (Nat.ne_of_gt hmodulus)] at hm
  have hn := WindowTwentyOneEntry.run_normalize ctx (WindowTwentyOneInput.modulusWord input)
    (UInt256.ofNat 96) (baseSize input) hmatch.1 (routeStack input) (by simp [routeStack]) rfl rfl
  have hn' : runInstructions WindowTwentyOneEntry.normalizeProgram
      (WindowTwentyOneEntry.framed ctx (UInt256.ofNat 2455)
        (WindowTwentyOneInput.modulusWord input :: routeStack input)) =
      some (normalized template input) := by
    simpa only [normalized, WindowTwentyOneTablePrelude.initial, WindowTwentyOneEntry.framed,
      WindowTwentyOneInput.baseWord, ctx, context, List.cons_append, List.nil_append,
      show (UInt256.ofNat 96).toNat = 96 by decide] using hn
  let gb := lift paths.base hb (ec.transfer rfl rfl) rfl
  let gm := lift paths.modulus hm (ec.transfer rfl rfl) rfl
  let gn := lift paths.normalize hn' (ec.transfer rfl rfl) rfl
  have gc := WindowTwentyOneGasCore.steps_core paths.toPaths ctx ec
    (WindowTwentyOneInput.baseWord input) (WindowTwentyOneInput.modulusWord input)
    (exponentOffset input) (modulusOffset input) (routeStack input)
    (by simp [routeStack]) rfl rfl (modulus_at template input hmatch) (jump_env ec paths.loopJump)
  have gc' : GasSteps (normalized template input) (returned template input) := by
    simpa only [normalized, returned, ctx, exponent_at template input hmatch.1] using gc
  exact ((gb.trans gm).trans gn).trans gc'

def Handled (template : State) (input : ByteArray) : Prop :=
  ∃ final : State, Nonempty (GasSteps (state template input (UInt256.ofNat 2440)) final) ∧
    final.isDone = true ∧ final.toResult = .returned (spec input)

def empty_handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray)
    (hmatch : WindowTwentyOneInput.Matches input) (hbase : baseSize input = 0) :
    Handled template input := by
  let ctx := context template input
  have ec := context_env template env input
  have hb := WindowTwentyOneEntry.run_base ctx (UInt256.ofNat (baseSize input))
    (routeStack input) (by simp [routeStack]) rfl (jump_env ec paths.emptyJump)
  have hz : (UInt256.ofNat (baseSize input)).toNat = 0 := by rw [hbase]; rfl
  rw [if_pos hz] at hb
  have hr := WindowTwentyOneReturn.run_empty ctx (exponentOffset input) (modulusOffset input)
    0 (by decide) rfl (routeStack input) (by simp [routeStack]) rfl rfl
  rw [exponent_at template input hmatch.1, modulus_at template input hmatch] at hr
  let final := WindowTwentyOneReturn.returned ctx (UInt256.ofNat 3110)
    (WindowTwentyOneReturn.emptyValue (WindowTwentyOneInput.exponentWord input) (WindowTwentyOneInput.modulusWord input))
    0 (routeStack input)
  have gas := (lift paths.base hb (ec.transfer rfl rfl) rfl).trans
    (lift paths.emptyReturn hr (ec.transfer rfl rfl) rfl)
  refine ⟨final, ⟨gas⟩, ?_, ?_⟩
  · change (true && template.callStack.isEmpty) = true
    rw [hcall]
    rfl
  · rw [WindowTwentyOneReturn.returned_result, WindowTwentyOneInput.emptyBase_spec input hmatch hbase]
    rfl

def zero_handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray)
    (hmatch : WindowTwentyOneInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : (WindowTwentyOneInput.modulusWord input).toNat = 0) :
    Handled template input := by
  let ctx := context template input
  have ec := context_env template env input
  have hb := WindowTwentyOneEntry.run_base ctx (UInt256.ofNat (baseSize input))
    (routeStack input) (by simp [routeStack]) rfl (jump_env ec paths.emptyJump)
  rw [if_neg (base_positive input hmatch hbase)] at hb
  have hm := WindowTwentyOneEntry.run_modulus ctx (modulusOffset input)
    (routeStack input) (by simp [routeStack]) rfl (jump_env ec paths.zeroJump)
  dsimp only at hm
  rw [modulus_at template input hmatch, if_pos hmodulus] at hm
  have hr := WindowTwentyOneReturn.run_zero ctx 0 (by decide) rfl
    (WindowTwentyOneInput.modulusWord input :: routeStack input) (by simp [routeStack])
  let final := WindowTwentyOneReturn.returned ctx (UInt256.ofNat 3094) (UInt256.ofNat 0)
    0 (WindowTwentyOneInput.modulusWord input :: routeStack input)
  have gas := ((lift paths.base hb (ec.transfer rfl rfl) rfl).trans
    (lift paths.modulus hm (ec.transfer rfl rfl) rfl)).trans
      (lift paths.zeroReturn hr (ec.transfer rfl rfl) rfl)
  refine ⟨final, ⟨gas⟩, ?_, ?_⟩
  · change (true && template.callStack.isEmpty) = true
    rw [hcall]
    rfl
  · have hm0 : WindowTwentyOneInput.modulusValue input = 0 := by
      rw [← WindowTwentyOneInput.modulusWord_toNat]
      exact hmodulus
    rw [WindowTwentyOneReturn.returned_result, WindowTwentyOneInput.spec_eq input hmatch,
      Algorithm.modPow_eq, hm0, if_pos rfl]
    rfl

def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    Handled template input := by
  by_cases hb : baseSize input = 0
  · exact empty_handled paths template env hcall input hmatch hb
  · have hp : 0 < baseSize input := Nat.pos_of_ne_zero hb
    by_cases hm : (WindowTwentyOneInput.modulusWord input).toNat = 0
    · exact zero_handled paths template env hcall input hmatch hp hm
    · have hmp := Nat.pos_of_ne_zero hm
      refine ⟨returned template input, ⟨positive_steps paths template env input hmatch hp hmp⟩, ?_,
        returned_spec template input hmatch hp hmp⟩
      change (true && template.callStack.isEmpty) = true
      rw [hcall]
      rfl

private def widthTail (input : ByteArray) : List UInt256 := (routeStack input).drop 3

private theorem width_raw (template : State) (input : ByteArray)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 4873 = true) :
    runInstructions WindowTwentyOneEntry.widthProgram (state template input (UInt256.ofNat 2416)) =
    some (state template input
      (if (WindowTwentyOneInput.guardDiff input).toNat = 0 then UInt256.ofNat 4873 else UInt256.ofNat 2436)) := by
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

def steps_bridge {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) :
    GasSteps (state template input (UInt256.ofNat 2613)) (state template input (UInt256.ofNat 2416)) := by
  have ec := context_env template env input
  have h := WindowTwentyOneEntry.run_bridge (context template input) (routeStack input)
    (by simp [routeStack]) (jump_env ec paths.entryJump)
  exact lift paths.entryBridge h (ec.transfer rfl rfl) rfl

def steps_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    GasSteps (state template input (UInt256.ofNat 2613)) (state template input (UInt256.ofNat 4873)) := by
  have h := width_raw template input (jump_env env paths.hitJump)
  rw [if_pos ((guard_zero_iff input).mpr hmatch)] at h
  exact (steps_bridge paths template env input).trans
    (lift paths.width h ((context_env template env input).transfer rfl rfl) rfl)

def steps_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hmatch : ¬ WindowTwentyOneInput.Matches input) :
    GasSteps (state template input (UInt256.ofNat 2613)) (state template input (UInt256.ofNat 517)) := by
  have h := width_raw template input (jump_env env paths.hitJump)
  have hn : (WindowTwentyOneInput.guardDiff input).toNat ≠ 0 := by
    intro hz
    exact hmatch ((guard_zero_iff input).mp hz)
  rw [if_neg hn] at h
  have hm := WindowTwentyOneEntry.run_miss (context template input) (routeStack input)
    (by simp [routeStack]) (jump_env env paths.missJump)
  have ec := context_env template env input
  exact (steps_bridge paths template env input).trans
    ((lift paths.width h (ec.transfer rfl rfl) rfl).trans
      (lift paths.miss hm (ec.transfer rfl rfl) rfl))

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

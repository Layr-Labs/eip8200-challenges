import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open WindowTwentyOneEntry WindowTwentyOneBinding EarlyWordProgram

private theorem jump_env {artifact : ProgramArtifact} {fork : Fork} {template : State}
    (env : Environment artifact fork template) {pc : Nat}
    (hjump : Decode.isValidJumpDest artifact.code pc = true) :
    Decode.isValidJumpDest template.executionEnv.code pc = true := by
  rw [env.code]
  exact hjump

/-- A width hit preserves the arbitrary carrier and creates the canonical frame. -/
def steps_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : WindowTwentyOneInput.Matches input) :
    GasSteps (framed template (UInt256.ofNat 5283) [])
      (framed template (UInt256.ofNat 5194) (WindowTwentyOnePositive.routeStack input)) := by
  have hg := run_guard template input hdata (jump_env env paths.missJump)
  rw [if_pos ((guard_zero_iff input).mpr hmatch)] at hg
  have hh := run_hit template input (jump_env env paths.hitJump)
  exact (paths.guard.steps
    (env.transfer (t := framed template (UInt256.ofNat 5283) []) rfl rfl) rfl hg).trans
    (paths.hit.steps
      (env.transfer (t := framed template (UInt256.ofNat 5310) (headerStack input)) rfl rfl) rfl hh)

/-- Every width miss reaches exactly the old entry with an empty stack. -/
def steps_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : ¬ WindowTwentyOneInput.Matches input) :
    GasSteps (framed template (UInt256.ofNat 5283) []) (framed template (UInt256.ofNat 1314) []) := by
  have hg := run_guard template input hdata (jump_env env paths.missJump)
  have hn : (WindowTwentyOneInput.guardDiff input).toNat ≠ 0 := by
    intro hz
    exact hmatch ((guard_zero_iff input).mp hz)
  rw [if_neg hn] at hg
  have hm := run_miss template input (jump_env env paths.legacyJump)
  exact (paths.guard.steps
    (env.transfer (t := framed template (UInt256.ofNat 5283) []) rfl rfl) rfl hg).trans
    (paths.miss.steps
      (env.transfer (t := framed template (UInt256.ofNat 5331) (headerStack input)) rfl rfl) rfl hm)

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

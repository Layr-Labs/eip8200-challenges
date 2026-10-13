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

/-- An exponent or modulus size other than 32 reaches the fixed-vector recogniser's
entry at 599 with an empty stack. -/
def steps_size_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmiss : ¬ (exponentSize input = 32 ∧ modulusSize input = 32)) :
    GasSteps (framed template (UInt256.ofNat 0) []) (framed template (UInt256.ofNat 599) []) := by
  have hs := run_size template input hdata (jump_env env paths.legacyJump)
  have hn : (sizeDiff input).toNat ≠ 0 := fun hz => hmiss ((sizeDiff_zero_iff input).mp hz)
  rw [if_neg hn] at hs
  exact paths.size.steps (env.transfer (t := framed template (UInt256.ofNat 0) []) rfl rfl) rfl hs

/-- Exponent and modulus sizes 32 reach the base size test at 16 with an empty stack. -/
def steps_size_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hsize : exponentSize input = 32 ∧ modulusSize input = 32) :
    GasSteps (framed template (UInt256.ofNat 0) []) (framed template (UInt256.ofNat 16) []) := by
  have hs := run_size template input hdata (jump_env env paths.legacyJump)
  rw [if_pos ((sizeDiff_zero_iff input).mpr hsize)] at hs
  exact paths.size.steps (env.transfer (t := framed template (UInt256.ofNat 0) []) rfl rfl) rfl hs

/-- Base size 32 falls through to the fast entry at 24. -/
def steps_width_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hb : baseSize input = 32) :
    GasSteps (framed template (UInt256.ofNat 16) []) (framed template (UInt256.ofNat 24) []) := by
  have hw := run_width template input hdata (jump_env env paths.genJump)
  rw [if_pos ((baseDiff_zero_iff input).mpr hb)] at hw
  exact paths.width.steps (env.transfer (t := framed template (UInt256.ofNat 16) []) rfl rfl) rfl hw

/-- Any other base size enters the general-width entry at 103. -/
def steps_width_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hb : baseSize input ≠ 32) :
    GasSteps (framed template (UInt256.ofNat 16) []) (framed template (UInt256.ofNat 103) []) := by
  have hw := run_width template input hdata (jump_env env paths.genJump)
  have hn : (baseDiff input).toNat ≠ 0 := fun hz => hb ((baseDiff_zero_iff input).mp hz)
  rw [if_neg hn] at hw
  exact paths.width.steps (env.transfer (t := framed template (UInt256.ofNat 16) []) rfl rfl) rfl hw

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

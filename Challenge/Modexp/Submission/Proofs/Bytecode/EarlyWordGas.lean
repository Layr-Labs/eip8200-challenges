import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open WindowTwentyOneEntry WindowTwentyOneBinding EarlyWordProgram
open WindowTwentyOnePositive (headerStack)

private theorem jump_env {artifact : ProgramArtifact} {fork : Fork} {template : State}
    (env : Environment artifact fork template) {pc : Nat}
    (hjump : Decode.isValidJumpDest artifact.code pc = true) :
    Decode.isValidJumpDest template.executionEnv.code pc = true := by
  rw [env.code]
  exact hjump

/-- A width hit preserves the arbitrary carrier and reaches the early entry at 25
with exactly the header stack. -/
def steps_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : WindowTwentyOneInput.Matches input) :
    GasSteps (framed template (UInt256.ofNat 0) [])
      (framed template (UInt256.ofNat 25) (headerStack input)) := by
  have hg := run_guard template input hdata (jump_env env paths.missJump)
  rw [if_pos ((guard_zero_iff input).mpr hmatch)] at hg
  exact paths.guard.steps
    (env.transfer (t := framed template (UInt256.ofNat 0) []) rfl rfl) rfl hg

/-- The common width-miss branch, before either return or positive resume. -/
def steps_missBranch {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : ¬ WindowTwentyOneInput.Matches input) :
    GasSteps (framed template (UInt256.ofNat 0) [])
      (framed template
        (if modulusSize input = 0 then UInt256.ofNat 132 else UInt256.ofNat 5439)
        (missStack input)) := by
  have hg := run_guard template input hdata (jump_env env paths.missJump)
  have hn : (WindowTwentyOneInput.guardDiff input).toNat ≠ 0 := by
    intro hz
    exact hmatch ((guard_zero_iff input).mp hz)
  rw [if_neg hn] at hg
  have hm := run_miss template input (jump_env env paths.resumeJump)
  exact (paths.guard.steps
    (env.transfer (t := framed template (UInt256.ofNat 0) []) rfl rfl) rfl hg).trans
    (paths.miss.steps
      (env.transfer (t := framed template (UInt256.ofNat 127) (headerStack input)) rfl rfl)
      rfl hm)

/-- Every positive-length width miss restores the old legacy entry exactly. -/
def steps_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : ¬ WindowTwentyOneInput.Matches input) (hpositive : 0 < modulusSize input) :
    GasSteps (framed template (UInt256.ofNat 0) []) (framed template (UInt256.ofNat 599) []) := by
  have hb := steps_missBranch paths template env input hdata hmatch
  rw [if_neg (Nat.ne_of_gt hpositive)] at hb
  exact hb.trans (paths.resume.steps
    (env.transfer (t := framed template (UInt256.ofNat 5439) (missStack input)) rfl rfl)
    rfl (run_resume template input (jump_env env paths.legacyJump)))

/-- Zero modulus length always misses the width guard and returns empty bytes. -/
def steps_zero {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hzero : modulusSize input = 0) :
    GasSteps (framed template (UInt256.ofNat 0) []) (zeroFinal template input) := by
  have hmiss : ¬ WindowTwentyOneInput.Matches input := by
    intro hm
    have heq := hm.2.2
    omega
  have hb := steps_missBranch paths template env input hdata hmiss
  rw [if_pos hzero] at hb
  exact hb.trans (paths.zero.steps
    (env.transfer (t := framed template (UInt256.ofNat 132) (missStack input)) rfl rfl)
    rfl (run_zero template input))

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

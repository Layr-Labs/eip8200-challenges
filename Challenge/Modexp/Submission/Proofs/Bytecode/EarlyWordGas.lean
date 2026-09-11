import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordSmallExp

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open WindowTwentyOneEntry WindowTwentyOneBinding EarlyWordProgram EarlyWordSmallExp

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
    GasSteps (framed template (UInt256.ofNat 5256) [])
      (framed template (UInt256.ofNat 4888) (WindowTwentyOnePositive.routeStack input)) := by
  have hg := run_guard template input hdata (jump_env env paths.smallExpJump)
  rw [if_pos ((guard_zero_iff input).mpr hmatch)] at hg
  have hh := run_hit template input (jump_env env paths.hitJump)
  exact (paths.guard.steps
    (env.transfer (t := framed template (UInt256.ofNat 5256) []) rfl rfl) rfl hg).trans
    (paths.hit.steps
      (env.transfer (t := framed template (UInt256.ofNat 5283) (headerStack input)) rfl rfl) rfl hh)

/-- Every width miss reaches exactly the old entry with an empty stack. -/
/-- A width miss that is not a zero-exponent hit still reaches the old
entry: the appended dispatcher bails to pc 5304 and the legacy miss block
restores the empty stack. -/
def steps_miss {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (zpaths : ZeroExpPaths artifact fork)
    (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : ¬ WindowTwentyOneInput.Matches input)
    (hzero : ¬ ZeroExpGuard input) :
    GasSteps (framed template (UInt256.ofNat 5256) []) (framed template (UInt256.ofNat 1233) []) := by
  have hg := run_guard template input hdata (jump_env env paths.smallExpJump)
  have hn : (WindowTwentyOneInput.guardDiff input).toNat ≠ 0 := by
    intro hz
    exact hmatch ((guard_zero_iff input).mp hz)
  rw [if_neg hn] at hg
  have hm := run_miss template input (jump_env env paths.legacyJump)
  have hmiss := paths.miss.steps
    (env.transfer (t := framed template (UInt256.ofNat 5304) (headerStack input)) rfl rfl) rfl hm
  have hzg := run_zeroExpGuard template (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
    (jump_env env zpaths.missJump)
  have hmlt : modulusSize input < 2 ^ 256 := by
    have := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 64 32
    have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
    omega
  have helt : exponentSize input < 2 ^ 256 := by
    have := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 32 32
    have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
    omega
  by_cases hm32 : 32 < modulusSize input
  · have hmp : 32 < (UInt256.ofNat (modulusSize input)).toNat := by
      rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmlt]
      exact hm32
    rw [if_pos hmp] at hzg
    exact (paths.guard.steps
      (env.transfer (t := framed template (UInt256.ofNat 5256) []) rfl rfl) rfl hg).trans
      ((zpaths.guard.steps
        (env.transfer (t := framed template (UInt256.ofNat 5312) (headerStack input)) rfl rfl) rfl hzg).trans
        hmiss)
  · by_cases he32 : 32 < exponentSize input
    · have hmn : ¬ 32 < (UInt256.ofNat (modulusSize input)).toNat := by
        rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmlt]
        exact hm32
      have hep : 32 < (UInt256.ofNat (exponentSize input)).toNat := by
        rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt helt]
        exact he32
      rw [if_neg hmn, if_pos hep] at hzg
      exact (paths.guard.steps
        (env.transfer (t := framed template (UInt256.ofNat 5256) []) rfl rfl) rfl hg).trans
        ((zpaths.guard.steps
          (env.transfer (t := framed template (UInt256.ofNat 5312) (headerStack input)) rfl rfl) rfl hzg).trans
          hmiss)
    · have hev : Precompile.bytesToNatPadded input (96 + baseSize input)
          (exponentSize input) ≠ 0 := by
        intro hz
        exact hzero ⟨by omega, by omega, hz⟩
      have hzl := run_zeroExpLoadE template (UInt256.ofNat (baseSize input))
        (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
        (jump_env env zpaths.missJump)
      have hmn : ¬ 32 < (UInt256.ofNat (modulusSize input)).toNat := by
        rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmlt]
        exact hm32
      have hen : ¬ 32 < (UInt256.ofNat (exponentSize input)).toNat := by
        rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt helt]
        exact he32
      rw [if_neg hmn, if_neg hen] at hzg
      have hne : (smallExpValue
          (MachineState.readWord template.executionEnv.calldata
            (UInt256.ofNat 96 + UInt256.ofNat (baseSize input)).toNat)
          (UInt256.ofNat (exponentSize input))).toNat ≠ 0 := by
        rw [hdata]
        have hoff : (UInt256.ofNat 96 + UInt256.ofNat (baseSize input)).toNat =
            96 + baseSize input := by
          rw [Word.ofNat_add_mod, Word.word_toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by
            have := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
            have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
            omega)]
        rw [hoff]
        rw [smallExpValue_toNat input (96 + baseSize input)
          (exponentSize input) (by omega)]
        exact hev
      rw [if_neg hne] at hzl
      exact (paths.guard.steps
        (env.transfer (t := framed template (UInt256.ofNat 5256) []) rfl rfl) rfl hg).trans
        ((zpaths.guard.steps
          (env.transfer (t := framed template (UInt256.ofNat 5312) (headerStack input)) rfl rfl) rfl hzg).trans
          ((zpaths.loadE.steps
            (env.transfer (t := framed template (UInt256.ofNat 5329) (headerStack input)) rfl rfl) rfl hzl).trans
            hmiss))

/-- A zero-exponent hit returns `1 < m` directly from the appended block. -/
def steps_smallExp_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (zpaths : ZeroExpPaths artifact fork)
    (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : ¬ WindowTwentyOneInput.Matches input)
    (hzero : ZeroExpGuard input)
    (hactive : template.activeWords = UInt256.ofNat 0) :
    GasSteps (framed template (UInt256.ofNat 5256) [])
      (zeroExpFinal template input 0
        [UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)]) := by
  obtain ⟨he32, hm32, hev⟩ := hzero
  have hg := run_guard template input hdata (jump_env env paths.smallExpJump)
  have hn : (WindowTwentyOneInput.guardDiff input).toNat ≠ 0 := by
    intro hz
    exact hmatch ((guard_zero_iff input).mp hz)
  rw [if_neg hn] at hg
  have hzg := run_zeroExpGuard template (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
    (jump_env env zpaths.missJump)
  have hmn : ¬ 32 < (UInt256.ofNat (modulusSize input)).toNat := by
    rw [Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : modulusSize input < 2 ^ 256)]
    omega
  have hen : ¬ 32 < (UInt256.ofNat (exponentSize input)).toNat := by
    rw [Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : exponentSize input < 2 ^ 256)]
    omega
  rw [if_neg hmn, if_neg hen] at hzg
  have hzl := run_zeroExpLoadE template (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
    (jump_env env zpaths.missJump)
  have heq : (smallExpValue
      (MachineState.readWord template.executionEnv.calldata
        (UInt256.ofNat 96 + UInt256.ofNat (baseSize input)).toNat)
      (UInt256.ofNat (exponentSize input))).toNat = 0 := by
    rw [hdata]
    have hoff : (UInt256.ofNat 96 + UInt256.ofNat (baseSize input)).toNat =
        96 + baseSize input := by
      rw [Word.ofNat_add_mod, Word.word_toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by
        have := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
        have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
        omega)]
    rw [hoff, smallExpValue_toNat input (96 + baseSize input)
      (exponentSize input) he32]
    exact hev
  rw [if_pos heq] at hzl
  have hzf := run_zeroExpFinish template (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
    0 (by norm_num) hactive
  have hfin : smallExpReturned template (UInt256.ofNat 5371)
      (UInt256.lt (UInt256.ofNat 1)
        (smallExpValue
          (MachineState.readWord template.executionEnv.calldata
            (UInt256.ofNat 96 + UInt256.ofNat (baseSize input) +
              UInt256.ofNat (exponentSize input)).toNat)
          (UInt256.ofNat (modulusSize input))))
      (UInt256.ofNat (modulusSize input)) 0
      [UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] =
    zeroExpFinal template input 0
      [UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] := by
    unfold zeroExpFinal zeroExpMvWord
    rw [hdata]
  rw [hfin] at hzf
  exact (paths.guard.steps
    (env.transfer (t := framed template (UInt256.ofNat 5256) []) rfl rfl) rfl hg).trans
    ((zpaths.guard.steps
      (env.transfer (t := framed template (UInt256.ofNat 5312) (headerStack input)) rfl rfl) rfl hzg).trans
      ((zpaths.loadE.steps
        (env.transfer (t := framed template (UInt256.ofNat 5329) (headerStack input)) rfl rfl) rfl hzl).trans
        (zpaths.finish.steps
          (env.transfer (t := framed template (UInt256.ofNat 5346) (headerStack input)) rfl rfl) rfl hzf)))

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

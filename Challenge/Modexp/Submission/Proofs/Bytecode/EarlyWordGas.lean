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

/-- Every width miss reaches the appended small-exponent dispatcher with the
three header words on the stack. -/
def steps_toSmallExp {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hmatch : ¬ WindowTwentyOneInput.Matches input) :
    GasSteps (framed template (UInt256.ofNat 5256) [])
      (framed template (UInt256.ofNat 5312) (headerStack input)) := by
  have hg := run_guard template input hdata (jump_env env paths.smallExpJump)
  have hn : (WindowTwentyOneInput.guardDiff input).toNat ≠ 0 := by
    intro hz
    exact hmatch ((guard_zero_iff input).mp hz)
  rw [if_neg hn] at hg
  exact paths.guard.steps
    (env.transfer (t := framed template (UInt256.ofNat 5256) []) rfl rfl) rfl hg

private theorem size_toNat (input : ByteArray) (offset : Nat) :
    (UInt256.ofNat
      (Precompile.bytesToNatPadded input offset 32)).toNat =
      Precompile.bytesToNatPadded input offset 32 := by
  rw [Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32)
    (by norm_num : (256:Nat) ^ 32 ≤ 2 ^ 256))

/-- A small-exponent miss restores the legacy entry exactly: every bail arm
rejoins the miss block at pc 5304 and lands at pc 1233 with an empty stack. -/
def steps_smallExp_bail {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (spaths : SmallExpPaths artifact fork)
    (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hsmall : ¬ SmallExpGuard input) :
    GasSteps (framed template (UInt256.ofNat 5312) (headerStack input))
      (framed template (UInt256.ofNat 1233) []) := by
  set mW := UInt256.ofNat (modulusSize input)
  set eW := UInt256.ofNat (exponentSize input)
  set bW := UInt256.ofNat (baseSize input)
  have hmW : mW.toNat = modulusSize input := size_toNat input 64
  have heW : eW.toNat = exponentSize input := size_toNat input 32
  have hbW : bW.toNat = baseSize input := size_toNat input 0
  have h1 := run_smallExpGuard1 template bW eW mW
    (jump_env env spaths.missJump)
  rw [hmW, heW, hbW] at h1
  by_cases hm : 32 < modulusSize input
  · rw [if_pos hm] at h1
    exact (spaths.guard.steps
      (env.transfer (t := framed template (UInt256.ofNat 5312)
        (headerStack input)) rfl rfl) rfl h1).trans
      (paths.miss.steps
        (env.transfer (t := framed template (UInt256.ofNat 5304)
          (headerStack input)) rfl rfl) rfl
        (run_miss template input (jump_env env paths.legacyJump)))
  · rw [if_neg hm] at h1
    by_cases he : 32 < exponentSize input
    · rw [if_pos he] at h1
      exact (spaths.guard.steps
        (env.transfer (t := framed template (UInt256.ofNat 5312)
          (headerStack input)) rfl rfl) rfl h1).trans
        (paths.miss.steps
          (env.transfer (t := framed template (UInt256.ofNat 5304)
            (headerStack input)) rfl rfl) rfl
          (run_miss template input (jump_env env paths.legacyJump)))
    · rw [if_neg he] at h1
      by_cases hb : 32 < baseSize input
      · rw [if_pos hb] at h1
        exact (spaths.guard.steps
          (env.transfer (t := framed template (UInt256.ofNat 5312)
            (headerStack input)) rfl rfl) rfl h1).trans
          (paths.miss.steps
            (env.transfer (t := framed template (UInt256.ofNat 5304)
              (headerStack input)) rfl rfl) rfl
            (run_miss template input (jump_env env paths.legacyJump)))
      · rw [if_neg hb] at h1
        have hle : modulusSize input ≤ 32 ∧ exponentSize input ≤ 32 ∧
            baseSize input ≤ 32 := ⟨by omega, by omega, by omega⟩
        have h2 := run_smallExpLoadE template bW eW mW
          (jump_env env spaths.bail4Jump)
        rw [hdata] at h2
        have hoff : (UInt256.ofNat 96 + bW).toNat = 96 + baseSize input := by
          rw [Word.ofNat_add_mod, Word.word_toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by
            have := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
            have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
            omega)]
        rw [hoff] at h2
        set evW := smallExpValue
          (MachineState.readWord input (96 + baseSize input)) eW
        have hevW : evW.toNat = Precompile.bytesToNatPadded input
            (96 + baseSize input) (exponentSize input) :=
          smallExpValue_toNat input (96 + baseSize input)
            (exponentSize input) hle.2.1
        rw [hevW] at h2
        by_cases hev : 1 < Precompile.bytesToNatPadded input
            (96 + baseSize input) (exponentSize input)
        · rw [if_pos hev] at h2
          exact (spaths.guard.steps
            (env.transfer (t := framed template (UInt256.ofNat 5312)
              (headerStack input)) rfl rfl) rfl h1).trans
            ((spaths.loadE.steps
              (env.transfer (t := framed template (UInt256.ofNat 5337)
                (headerStack input)) rfl rfl) rfl h2).trans
              ((spaths.bail4.steps
                (env.transfer (t := framed template (UInt256.ofNat 5427)
                  (evW :: headerStack input)) rfl rfl) rfl
                (run_smallExpBail4 template bW eW mW evW
                  (jump_env env spaths.missJump))).trans
                (paths.miss.steps
                  (env.transfer (t := framed template (UInt256.ofNat 5304)
                    (headerStack input)) rfl rfl) rfl
                  (run_miss template input
                    (jump_env env paths.legacyJump)))))
        · rw [if_neg hev] at h2
          have h3 := run_smallExpLoadM template bW eW mW evW
            (jump_env env spaths.oneJump)
          rw [hdata] at h3
          have hoffm : (UInt256.ofNat 96 + eW + bW).toNat =
              96 + baseSize input + exponentSize input := by
            rw [Word.ofNat_add_mod, Word.ofNat_add_mod,
              Word.word_toNat_ofNat]
            rw [Nat.mod_eq_of_lt (by
              have h1' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
                input 0 32
              have h2' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
                input 32 32
              have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
              omega)]
            omega
          have hoff96 : (UInt256.ofNat 96).toNat = 96 := by
            rw [Word.word_toNat_ofNat]
          rw [hoffm, hoff96] at h3
          set bvW := smallExpValue (MachineState.readWord input 96) bW
          set mvW := smallExpValue
            (MachineState.readWord input
              (96 + baseSize input + exponentSize input)) mW
          have hbvW : bvW.toNat = Precompile.bytesToNatPadded input 96
              (baseSize input) :=
            smallExpValue_toNat input 96 (baseSize input) hle.2.2
          have hmvW : mvW.toNat = Precompile.bytesToNatPadded input
              (96 + baseSize input + exponentSize input)
              (modulusSize input) :=
            smallExpValue_toNat input
              (96 + baseSize input + exponentSize input)
              (modulusSize input) hle.1
          by_cases hev0 : evW.toNat = 0
          · rw [if_pos hev0] at h3
            rw [hevW] at hev0
            exact absurd ⟨hle.2.2, hle.2.1, hle.1, Or.inl hev0⟩ hsmall
          · rw [if_neg hev0] at h3
            have h4 := run_smallExpOne template bW eW mW evW bvW mvW
              template.activeWords.toNat
              template.activeWords.val.isLt
              (Word.word_eq_ofNat_toNat template.activeWords)
              (jump_env env spaths.bail5Jump)
            rw [hmvW, hbvW] at h4
            by_cases hbm : Precompile.bytesToNatPadded input
                (96 + baseSize input + exponentSize input)
                (modulusSize input) ≤ Precompile.bytesToNatPadded input 96
                  (baseSize input)
            · rw [if_pos hbm] at h4
              exact (spaths.guard.steps
                (env.transfer (t := framed template (UInt256.ofNat 5312)
                  (headerStack input)) rfl rfl) rfl h1).trans
                ((spaths.loadE.steps
                  (env.transfer (t := framed template (UInt256.ofNat 5337)
                    (headerStack input)) rfl rfl) rfl h2).trans
                  ((spaths.loadM.steps
                    (env.transfer (t := framed template (UInt256.ofNat 5358)
                      (evW :: headerStack input)) rfl rfl) rfl h3).trans
                    ((spaths.one.steps
                      (env.transfer (t := framed template (UInt256.ofNat 5404)
                        [mvW, bvW, evW, mW, eW, bW]) rfl rfl) rfl h4).trans
                      ((spaths.bail5.steps
                        (env.transfer (t := framed template
                          (UInt256.ofNat 5424) [mvW, bvW, evW, mW, eW, bW])
                          rfl rfl) rfl
                        (run_smallExpBail5 template bW eW mW evW bvW mvW)).trans
                        ((spaths.bail4.steps
                          (env.transfer (t := framed template
                            (UInt256.ofNat 5427) [evW, mW, eW, bW]) rfl rfl)
                          rfl
                          (run_smallExpBail4 template bW eW mW evW
                            (jump_env env spaths.missJump))).trans
                          (paths.miss.steps
                            (env.transfer (t := framed template
                              (UInt256.ofNat 5304) (headerStack input))
                              rfl rfl) rfl
                            (run_miss template input
                              (jump_env env paths.legacyJump))))))))
            · rw [if_neg hbm] at h4
              have hev1 : Precompile.bytesToNatPadded input
                  (96 + baseSize input) (exponentSize input) = 1 := by
                have hle1 : Precompile.bytesToNatPadded input
                    (96 + baseSize input) (exponentSize input) ≤ 1 := by omega
                have hne0 : Precompile.bytesToNatPadded input
                    (96 + baseSize input) (exponentSize input) ≠ 0 := by
                  intro hz
                  exact hev0 (by rwa [hevW])
                omega
              exact absurd ⟨hle.2.2, hle.2.1, hle.1,
                Or.inr ⟨hev1, by omega⟩⟩ hsmall

/-- A small-exponent hit returns the decided word directly. -/
def steps_smallExp_hit {artifact : ProgramArtifact} {fork : Fork}
    (paths : Paths artifact fork) (spaths : SmallExpPaths artifact fork)
    (template : State) (env : Environment artifact fork template)
    (input : ByteArray) (hdata : template.executionEnv.calldata = input)
    (hactive : template.activeWords = UInt256.ofNat 0)
    (hsmall : SmallExpGuard input) :
    GasSteps (framed template (UInt256.ofNat 5312) (headerStack input))
      (smallExpFinal template input 0 (headerStack input)) := by
  obtain ⟨hb32, he32, hm32, hev⟩ := hsmall
  have hev_le : Precompile.bytesToNatPadded input (96 + baseSize input)
      (exponentSize input) ≤ 1 := by rcases hev with h | ⟨h, _⟩ <;> omega
  set mW := UInt256.ofNat (modulusSize input)
  set eW := UInt256.ofNat (exponentSize input)
  set bW := UInt256.ofNat (baseSize input)
  have hmW : mW.toNat = modulusSize input := size_toNat input 64
  have heW : eW.toNat = exponentSize input := size_toNat input 32
  have hbW : bW.toNat = baseSize input := size_toNat input 0
  have h1 := run_smallExpGuard1 template bW eW mW
    (jump_env env spaths.missJump)
  rw [hmW, heW, hbW] at h1
  rw [if_neg (by omega : ¬ 32 < modulusSize input),
    if_neg (by omega : ¬ 32 < exponentSize input),
    if_neg (by omega : ¬ 32 < baseSize input)] at h1
  have h2 := run_smallExpLoadE template bW eW mW
    (jump_env env spaths.bail4Jump)
  rw [hdata] at h2
  have hoff : (UInt256.ofNat 96 + bW).toNat = 96 + baseSize input := by
    rw [Word.ofNat_add_mod, Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      have := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
      have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
      omega)]
  rw [hoff] at h2
  set evW := smallExpValue
    (MachineState.readWord input (96 + baseSize input)) eW
  have hevW : evW.toNat = Precompile.bytesToNatPadded input
      (96 + baseSize input) (exponentSize input) :=
    smallExpValue_toNat input (96 + baseSize input)
      (exponentSize input) he32
  rw [hevW] at h2
  rw [if_neg (by omega : ¬ 1 < Precompile.bytesToNatPadded input
      (96 + baseSize input) (exponentSize input))] at h2
  have h3 := run_smallExpLoadM template bW eW mW evW
    (jump_env env spaths.oneJump)
  rw [hdata] at h3
  have hoffm : (UInt256.ofNat 96 + eW + bW).toNat =
      96 + baseSize input + exponentSize input := by
    rw [Word.ofNat_add_mod, Word.ofNat_add_mod,
      Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      have h1' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
      have h2' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 32 32
      have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
      omega)]
    omega
  have hoff96 : (UInt256.ofNat 96).toNat = 96 := by
    rw [Word.word_toNat_ofNat]
  rw [hoffm, hoff96] at h3
  set bvW := smallExpValue (MachineState.readWord input 96) bW
  set mvW := smallExpValue
    (MachineState.readWord input
      (96 + baseSize input + exponentSize input)) mW
  have hmvWeq : smallExpMvWord input = mvW := by
    unfold smallExpMvWord
    have hoff' : (UInt256.ofNat 96 + UInt256.ofNat (exponentSize input) +
        UInt256.ofNat (baseSize input)).toNat =
        96 + baseSize input + exponentSize input := by
      rw [Word.ofNat_add_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by
        have h1' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 0 32
        have h2' := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 32 32
        have h256 : (256:Nat) ^ 32 = 2 ^ 256 := by norm_num
        omega)]
      omega
    rw [hoff', hoff96]
  have hbvWeq : smallExpBvWord input = bvW := by
    unfold smallExpBvWord
    rw [hoff96]
  have hfront : Challenge.EvmProof.GasSteps
      (framed template (UInt256.ofNat 5312) (headerStack input))
      (framed template (UInt256.ofNat 5358) (evW :: headerStack input)) :=
    (spaths.guard.steps
      (env.transfer (t := framed template (UInt256.ofNat 5312)
        (headerStack input)) rfl rfl) rfl h1).trans
      (spaths.loadE.steps
        (env.transfer (t := framed template (UInt256.ofNat 5337)
          (headerStack input)) rfl rfl) rfl h2)
  rcases hev with hev0 | ⟨hev1, hbm⟩
  · rw [if_pos (show evW.toNat = 0 by rwa [hevW])] at h3
    have h4 := run_smallExpZero template bW eW mW evW bvW mvW 0
      (by norm_num) hactive
    have hgoal : smallExpFinal template input 0 (headerStack input) =
        smallExpReturned template (UInt256.ofNat 5404)
          (UInt256.lt (UInt256.ofNat 1) mvW)
          mW 0 (headerStack input) := by
      unfold smallExpFinal
      rw [if_pos hev0, hmvWeq]
    rw [hgoal]
    exact hfront.trans
      ((spaths.loadM.steps
        (env.transfer (t := framed template (UInt256.ofNat 5358)
          (evW :: headerStack input)) rfl rfl) rfl h3).trans
        (spaths.zero.steps
          (env.transfer (t := framed template (UInt256.ofNat 5389)
            [mvW, bvW, evW, mW, eW, bW]) rfl rfl) rfl h4))
  · rw [if_neg (show evW.toNat ≠ 0 by
        rw [hevW]; omega)] at h3
    have h4 := run_smallExpOne template bW eW mW evW bvW mvW 0
      (by norm_num) hactive
      (jump_env env spaths.bail5Jump)
    have hbvW : bvW.toNat = Precompile.bytesToNatPadded input 96
        (baseSize input) :=
      smallExpValue_toNat input 96 (baseSize input) hb32
    have hmvW : mvW.toNat = Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input)
        (modulusSize input) :=
      smallExpValue_toNat input
        (96 + baseSize input + exponentSize input)
        (modulusSize input) hm32
    rw [hmvW, hbvW] at h4
    rw [if_neg (show ¬ Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) ≤
          Precompile.bytesToNatPadded input 96 (baseSize input) by omega)] at h4
    have hgoal : smallExpFinal template input 0 (headerStack input) =
        smallExpReturned template (UInt256.ofNat 5424) bvW
          mW 0 (headerStack input) := by
      unfold smallExpFinal
      rw [if_neg (by omega : ¬ Precompile.bytesToNatPadded input
          (96 + baseSize input) (exponentSize input) = 0), hbvWeq]
    rw [hgoal]
    exact hfront.trans
      ((spaths.loadM.steps
        (env.transfer (t := framed template (UInt256.ofNat 5358)
          (evW :: headerStack input)) rfl rfl) rfl h3).trans
        (spaths.one.steps
          (env.transfer (t := framed template (UInt256.ofNat 5404)
            [mvW, bvW, evW, mW, eW, bW]) rfl rfl) rfl h4))

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas

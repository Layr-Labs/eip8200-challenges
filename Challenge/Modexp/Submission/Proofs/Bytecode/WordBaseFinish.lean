import Challenge.Modexp.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

/-- Initializing the accumulator needs only distinguish modulus zero, one, or larger.
`LT` produces the same word as `MOD` here, for two fewer gas. -/
private theorem one_lt_eq_mod (m : UInt256) :
    UInt256.lt (UInt256.ofNat 1) m = UInt256.ofNat 1 % m := by
  change UInt256.lt (UInt256.ofNat 1) m = UInt256.mod (UInt256.ofNat 1) m
  apply Challenge.EvmProof.Word.word_ext
  change (if 1 < m.toNat then UInt256.ofNat 1 else UInt256.ofNat 0).toNat = _
  rw [apply_ite UInt256.toNat]
  change (if 1 < m.toNat then 1 else 0) = UInt256.toNat (if m.toNat = 0 then _ else _)
  rw [apply_ite UInt256.toNat]
  change (if 1 < m.toNat then 1 else 0) = if m.toNat = 0 then 0 else 1 % m.toNat
  by_cases hzero : m.toNat = 0
  · simp [hzero]
  · by_cases hone : m.toNat = 1
    · simp [hone]
    · have hgt : 1 < m.toNat := by omega
      simp [hzero, hgt, Nat.mod_eq_of_lt hgt]

set_option linter.unusedSimpArgs false in
theorem run_baseFinishTail (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseFinishTailPath
      (baseFinishDispatchState input base) =
        some (expLoopState input 0
          (UInt256.ofNat 1 % UInt256.ofNat (modulusValue input)) base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hmval : modulusValue input < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)).trans_le (by
        have hp := pow_le_pow_right₀ (by omega : 1 ≤ (256 : Nat)) hword
        exact hp.trans (by norm_num))
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 150000 })
    [baseFinishTailPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseFinishDispatchState, baseLoopState, expLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, baseFinishPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hmval, hzeroWord, hzeroRaw, honeWord, one_lt_eq_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.Word

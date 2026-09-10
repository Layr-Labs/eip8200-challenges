import Challenge.Modexp.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

/-- `LT 1 x` and `MOD 1 x` agree on every `x`: both are `0` for `x ≤ 1` and
`1` for `x ≥ 2`. The rewritten opcode therefore produces the same stack word
the `MOD` trace certified. -/
private theorem lt_one_eq_mod_one (x : UInt256) :
    UInt256.lt (UInt256.ofNat 1) x = UInt256.ofNat 1 % x := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
  change (if 1 < x.toNat then 1 else 0) =
    (if x.toNat = 0 then (0 : UInt256)
     else UInt256.mk ((UInt256.ofNat 1).val % x.val)).toNat
  by_cases hzero : x.toNat = 0
  · rw [if_pos hzero]
    rw [if_neg (by omega)]
  · rw [if_neg hzero]
    change (if 1 < x.toNat then 1 else 0) =
      ((UInt256.ofNat 1).val % x.val).val
    rw [Fin.mod_val]
    have hv : (UInt256.ofNat 1).val.val = 1 := by decide
    rw [hv]
    have hx : x.val.val = x.toNat := rfl
    rw [hx]
    by_cases hone : x.toNat = 1
    · rw [hone]
      decide
    · have hgt : 1 < x.toNat := by omega
      rw [if_pos hgt]
      exact (Nat.mod_eq_of_lt hgt).symm

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
      hmval, hzeroWord, hzeroRaw, honeWord, lt_one_eq_mod_one]

end Challenge.Modexp.Submission.Proofs.Bytecode.Word

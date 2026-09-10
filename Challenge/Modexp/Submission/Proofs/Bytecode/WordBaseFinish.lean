import Challenge.Modexp.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

/-- `1 % x` is the `1 < x` predicate: `0` for `x ∈ {0, 1}`, `1` otherwise. -/
private theorem lt_one_eq_mod_one (x : UInt256) :
    UInt256.lt (UInt256.ofNat 1) x = UInt256.ofNat 1 % x := by
  by_cases h0 : x.toNat = 0
  · have hx : x = UInt256.ofNat 0 :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat x).trans
        (congrArg UInt256.ofNat h0)
    subst hx
    decide
  by_cases h1 : x.toNat = 1
  · have hx : x = UInt256.ofNat 1 :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat x).trans
        (congrArg UInt256.ofNat h1)
    subst hx
    decide
  by_cases h2 : x.toNat = 2
  · have hx : x = UInt256.ofNat 2 :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat x).trans
        (congrArg UInt256.ofNat h2)
    subst hx
    decide
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lt]
  have _h1t : (UInt256.ofNat 1).toNat = 1 := by decide
  rw [if_pos (by omega : (UInt256.ofNat 1).toNat < x.toNat)]
  change (1 : Nat) =
    (if x.toNat = 0 then (0 : UInt256) else
      UInt256.mk ((UInt256.ofNat 1).val % x.val)).toNat
  rw [if_neg h0]
  show (1 : Nat) = ((UInt256.ofNat 1).val % x.val).val
  rw [Fin.mod_val]
  have _hxv : x.val.val > 2 := by
    have h' : x.toNat > 2 := by omega
    exact h'
  rw [Fin.val_ofNat,
    Nat.mod_eq_of_lt (by decide : (1 : Nat) < UInt256.size),
    Nat.mod_eq_of_lt (by omega : (1 : Nat) < x.val.val)]

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

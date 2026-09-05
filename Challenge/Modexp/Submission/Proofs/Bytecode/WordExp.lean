import Challenge.Modexp.Submission.Proofs.Bytecode.WordDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# One-word MODEXP path: base-loop exit and exponent loop

Split out of `Word` so each certificate block elaborates in its own process.
-/
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

set_option linter.unusedSimpArgs false in
theorem run_baseFinishGuard (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseGuardPath
      (baseLoopState input (baseSize input) base) =
        some (baseFinishDispatchState input base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb256
  have h582 : (582 : UInt256).toNat = 582 := by decide
  have h582Word : (582 : UInt256) = UInt256.ofNat 582 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [baseGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseLoopState, baseFinishDispatchState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hb256, hbmod, hzeroFalse, h582, h582Word, jump582]

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
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      baseFinishPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hmval, hzeroWord, hzeroRaw, honeWord]

set_option linter.unusedSimpArgs false in
theorem run_expGuard (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expGuardPath
      (expLoopState input i acc base) = some (expGuardState input i acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have he256 : exponentSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he256
  have hilt : i % 2 ^ 256 < exponentSize input % 2 ^ 256 := by
    rw [himod, hemod]
    exact hi
  have hiltLiteral :
      i %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
        exponentSize input %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hilt ⊢
    exact hilt
  have hcondLiteral :
      (if i %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
          exponentSize input %
          115792089237316195423570985008687907853269984665640564039457584007913129639936
        then UInt256.ofNat 1 else UInt256.ofNat 0).isZero.toNat = 0 := by
    rw [if_pos hiltLiteral]
    decide
  have h598 : (598 : UInt256).toNat = 598 := by decide
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [expGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expLoopState, expGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hi, hi256, he256, himod, hemod, hilt, hiltLiteral, hcondLiteral,
      honeIsZero, h598]

set_option linter.unusedSimpArgs false in
theorem run_expLoad (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expLoadPath
      (expGuardState input i acc base) =
        some (bitLoopState input i 0 (byteWord input (expOffset input + i))
          (UInt256.ofNat (expOffset input + i)) acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hoff : expOffset input + i < 2 ^ 256 := by
    simp only [expOffset]
    omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := expOffset input) (b := i) hoff
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 175000 })
    [expLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expGuardState, expLoopState, bitLoopState, byteWord,
      Accessors.calldataByteValue,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hoff, hadd, hzeroWord, hzeroRaw]


end Challenge.Modexp.Submission.Proofs.Bytecode.Word

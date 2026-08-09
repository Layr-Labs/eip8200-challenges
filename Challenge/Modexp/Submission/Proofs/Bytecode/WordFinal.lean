import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Result and total-gas bridge for the one-word path

`WordExit` produces the final state and `WordCorrect` produces the arithmetic
(`wordResult_toNat`).  This module joins them into the two facts the top-level
composition consumes:

* `wordFinalState_result` — the returned bytes are `Spec.spec`;
* `gasSteps_wordNonzeroTotal` — a trace from the initial state to that final
  state, i.e. header ∘ dispatch ∘ `WordExit.gasSteps_wordTotal`.

Both belong with the word path rather than in `SubmissionCorrect`, which stays a
composition of per-path totals.

`outputShift_eq`, `outputWord_toNat` and `shifted_div` are carried over
**verbatim** from `Challenge/Modexp/Reference/Proofs/Bytecode/WordCorrect.lean`
lines 473, 482 and 516; `outputShift` and `outputWord` are defined identically in
this artifact's `WordExit`, so the proofs apply unchanged.

`outputMemory_readPadded` is that file's line 525 with one change: this
artifact's `WordExit.outputMemory` writes the return word on top of the window
table (`tableMem input base 16`) rather than on `ByteArray.empty`, so it carries
the extra `base` argument.  The proof is unaffected — every index it reads is
inside the 32 written bytes, where `writeBytes` does not consult the underlying
buffer.

`wordFinalState_result` is line 558 with the base/accumulator argument order of
the new `WordExit.wordFinalState`, and with `wordResult_correct` replaced by
`WordCorrect.wordResult_toNat`, which states the same fact about `.toNat`
instead of about the word.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordFinal

open EvmSemantics
open EvmSemantics.EVM
open Word
open WordLoops
open WordExit

theorem outputShift_eq (input : ByteArray) (hword : modulusSize input ≤ 32) :
    outputShift input = UInt256.ofNat ((32 - modulusSize input) * 8) := by
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  unfold outputShift
  rw [show (32 : UInt256) = UInt256.ofNat 32 by decide, hsub,
    Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
    norm_num [Nat.shiftLeft_eq] <;> omega

theorem outputWord_toNat (input : ByteArray) (n : Nat)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hn : n < 256 ^ modulusSize input) :
    (outputWord input (UInt256.ofNat n)).toNat =
      n * 256 ^ (32 - modulusSize input) := by
  have hfactor : 0 < 256 ^ (32 - modulusSize input) := pow_pos (by norm_num) _
  have hmul := Nat.mul_lt_mul_of_pos_right hn hfactor
  have hbound : n * 256 ^ (32 - modulusSize input) < 2 ^ 256 := by
    rw [show (2 : Nat) ^ 256 = 256 ^ 32 by norm_num]
    calc
      n * 256 ^ (32 - modulusSize input) <
          256 ^ (modulusSize input) * 256 ^ (32 - modulusSize input) := hmul
      _ = 256 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hn256 : n < 2 ^ 256 := by
    calc
      n < 256 ^ (modulusSize input) := hn
      _ ≤ 256 ^ 32 := pow_le_pow_right₀ (by omega) hword
      _ = 2 ^ 256 := by norm_num
  unfold outputWord
  rw [outputShift_eq input hword,
    Challenge.EvmProof.Word.shiftLeft_ofNat hn256 (by omega) (by
      simpa [show (2 : Nat) ^ ((32 - modulusSize input) * 8) =
          256 ^ (32 - modulusSize input) by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
        congr 1
        omega] using hbound),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [show (2 : Nat) ^ ((32 - modulusSize input) * 8) =
      256 ^ (32 - modulusSize input) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
    congr 1
    omega,
    Nat.mod_eq_of_lt hbound]

theorem shifted_div (n width k : Nat) (hwidth : width ≤ 32) (hk : k < width) :
    n * 256 ^ (32 - width) / 256 ^ (32 - 1 - k) =
      n / 256 ^ (width - 1 - k) := by
  have hexponent : 32 - 1 - k = (32 - width) + (width - 1 - k) := by
    omega
  rw [hexponent, Nat.pow_add, Nat.mul_comm (256 ^ (32 - width))]
  exact Nat.mul_div_mul_right n (256 ^ (width - 1 - k))
    (pow_pos (by norm_num) _)

theorem outputMemory_readPadded (input : ByteArray) (base : UInt256) (n : Nat)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hn : n < 256 ^ modulusSize input) :
    MachineState.readPadded (outputMemory input base (UInt256.ofNat n)) 6144
        (modulusSize input) =
      Precompile.natToBytes n (modulusSize input) := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    rw [Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < modulusSize input := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hk]
    unfold outputMemory
    rw [MachineState.writeBytes_getElem?_getD, if_pos (by
      constructor
      · omega
      · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
        omega)]
    rw [show 6144 + k - 6144 = k by omega,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ 32 k
        (by omega),
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _
        (modulusSize input) k hk,
      outputWord_toNat input n hmsize hword hn,
      shifted_div n (modulusSize input) k hword hk]

theorem wordFinalState_result (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) :
    (wordFinalState input (wordBase input) (wordResult input)).toResult =
      .returned (spec input) := by
  have hmodWidth : modulusValue input < 256 ^ modulusSize input :=
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)
  have hmodlt : modulusValue input < 2 ^ 256 := by
    calc
      modulusValue input < 256 ^ modulusSize input := hmodWidth
      _ ≤ 256 ^ 32 := pow_le_pow_right₀ (by omega) hword
      _ = 2 ^ 256 := by norm_num
  let result := Precompile.modPow
    (Precompile.bytesToNatPadded input 96 (baseSize input))
    (Precompile.bytesToNatPadded input (expOffset input) (exponentSize input))
    (modulusValue input)
  have hresult : result < 256 ^ modulusSize input :=
    (Algorithm.modPow_lt hmodpos).trans hmodWidth
  have hres : wordResult input = UInt256.ofNat result :=
    (WordCorrect.ofNat_toNat (wordResult input)).symm.trans
      (congrArg UInt256.ofNat
        (WordCorrect.wordResult_toNat input hvalid hmodpos hmodlt))
  rw [hres]
  change ExecutionResult.returned
      (MachineState.readPadded
        (outputMemory input (wordBase input) (UInt256.ofNat result))
        6144 (modulusSize input)) = ExecutionResult.returned (spec input)
  rw [outputMemory_readPadded input (wordBase input) result hmsize hword hresult]
  congr 1
  simp [spec, Nat.ne_of_gt hmsize, result, modulusValue, modulusOffset,
    expOffset, Nat.add_assoc]

/-- The whole non-zero-modulus word path: initial state to `RETURN`. -/
def gasSteps_wordNonzeroTotal (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodpos : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (wordFinalState input (wordBase input) (wordResult input)) :=
  ((Main.gasSteps_header input hvalid).trans
      (Dispatch.gasSteps_wordEntry input hvalid hmsize hword)).trans
    (gasSteps_wordTotal input hvalid hmsize hword hmodpos)

end Challenge.Modexp.Submission.Proofs.Bytecode.WordFinal

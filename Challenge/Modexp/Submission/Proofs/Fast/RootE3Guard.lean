import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
import Challenge.EvmProof.Bytes

/-!
# The E5 exponent-byte spec (surviving slice)

The phase-10 regen carried the old pc-2733 entry-guard block here (`run_guard`: a
20-instruction symbolic `simp` whose land/eq/isZero chain over abstract words is a
multi-hour whnf grind).  The guard itself moved INTO E5 in the phase-17 restructure
(`RootE3Bindings` no longer walks pc 2733 — the entryGuard field was deleted as dead
code), so the run theorem and the `guardWord`/`result` family had no consumers left.
This file keeps exactly the two spec lemmas `RootE3Bindings` reuses:
`exponentByte_spec` (the E5 guard's exponent byte = `FixedExponentRoute.exponentValue`)
and `exponentValue_one_lt` (that byte is < 256).
-/

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000

namespace RootE3Guard
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

/-- The E5 guard's exponent byte: byte 0 of the calldata word the kernel reads at
the header's exponent offset (the word `mem 2816` points at). -/
def exponentByte (mem input : ByteArray) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat 0)
    (MachineState.readWord input (MachineState.readWord mem 2816).toNat)

theorem exponentByte_spec (mem input : ByteArray) (bsize : Nat) (hb : bsize ≤ 1024)
    (heoff : MachineState.readWord mem 2816 = UInt256.ofNat (96 + bsize)) :
    exponentByte mem input = UInt256.ofNat (FixedExponentRoute.exponentValue input bsize 1) := by
  have hoff : 96 + bsize < 2 ^ 256 := by omega
  rw [exponentByte, heoff, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from Exp.push0_word.symm,
    Challenge.EvmProof.Bytes.byteAt_zero_readWord]
  congr 1
  symm
  simpa [FixedExponentRoute.exponentValue] using
    Challenge.EvmProof.Bytes.bytesToNatPadded_succ input (96 + bsize) 0

theorem exponentValue_one_lt (input : ByteArray) (bsize : Nat) :
    FixedExponentRoute.exponentValue input bsize 1 < 256 := by
  simpa [FixedExponentRoute.exponentValue] using
    Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input (96 + bsize) 1

end RootE3Guard

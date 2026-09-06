import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

def expectedWord (off : Nat) : UInt32 :=
  (expectedByte off).toUInt32 |||
    ((expectedByte (off + 1)).toUInt32 <<< UInt32.ofNat 8) |||
    ((expectedByte (off + 2)).toUInt32 <<< UInt32.ofNat 16) |||
    ((expectedByte (off + 3)).toUInt32 <<< UInt32.ofNat 24)

theorem read_patterned (off i : Nat) (hoff : off + 64 ≤ 1000) (hi : i < 16) :
    Ripemd160.readLE32 patternedInput (off + i * 4) =
      expectedWord (off + i * 4) := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : off + i * 4 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : off + i * 4 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : off + i * 4 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : off + i * 4 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0, patternedInput_getElem _ h1,
    patternedInput_getElem _ h2, patternedInput_getElem _ h3]
  simp [expectedWord]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

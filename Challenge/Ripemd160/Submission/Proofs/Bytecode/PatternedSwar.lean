import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-!
# The word recurrence the guard evaluates

The guard never stores the thirty-two expected words.  Byte `j` of word `k` is
`(160k + 37j + 7 + c) mod 256`, so each word is the fixed word `P` with one
scalar added to every byte, and a bytewise add of `y` to `x` is

```
((x &&& m7) + (y &&& m7)) ^^^ ((x ^^^ y) &&& m8)
```

The four words whose offset satisfies `o &&& 255 = 224` straddle a step of
`i / 251` and take one further add whose constant is shifted out of `M`.  The
definitions below are exactly what the bytecode computes; the theorems tie each
one to the word of the vector proved in `PatternedWordLogic`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar

open EvmSemantics
open EvmSemantics.EVM

def M   : UInt256 := UInt256.ofNat 0x0101010101010101010101010101010101010101010101010101010101010101
def m7  : UInt256 := UInt256.ofNat 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f
def m8  : UInt256 := UInt256.ofNat 0x8080808080808080808080808080808080808080808080808080808080808080
def P   : UInt256 := UInt256.ofNat 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82
def P7  : UInt256 := UInt256.land m7 P

/-- The running scalar, advanced by 160 a word and by 11 at each boundary. -/
def scalarAt : Nat -> Nat
  | 0 => 0
  | k + 1 =>
      (scalarAt k + (if (32 * k) % 256 == 224 then 11 else 0) + 160) % 256

/-- The word the guard derives before any correction, exactly as it computes
it: `S = M * s`, then `(m8 &&& (P ^^^ S)) ^^^ (P7 + (m7 &&& S))`. -/
def rawWord (k : Nat) : UInt256 :=
  UInt256.xor
    (UInt256.land m8 (UInt256.xor P (UInt256.mul M (UInt256.ofNat (scalarAt k)))))
    (P7 + UInt256.land m7 (UInt256.mul M (UInt256.ofNat (scalarAt k))))

/-- The correction constant, shifted out of `M` and scaled by eleven. -/
def straddleCorrection (o : UInt256) : UInt256 :=
  UInt256.mul (UInt256.ofNat 11)
    (UInt256.shiftRight M
      (UInt256.mul (UInt256.ofNat 8)
        (UInt256.ofNat 27 -
          UInt256.mul (UInt256.ofNat 5) (UInt256.shiftRight o (UInt256.ofNat 8)))))

/-- The correction add.  The constant's high bits are clear, so the guard masks
`E` itself rather than `E ^^^ C`. -/
def straddleAdd (E C : UInt256) : UInt256 :=
  UInt256.xor (UInt256.land m8 E) (C + UInt256.land m7 E)

/-- The word the guard compares against. -/
def guardWord (k : Nat) : UInt256 :=
  if (32 * k) % 256 == 224 then
    straddleAdd (rawWord k) (straddleCorrection (UInt256.ofNat (32 * k)))
  else rawWord k

@[simp] theorem guardWord_0 : guardWord 0 = PatternedWordData.expectedWordAt 0 := by
  decide

@[simp] theorem guardWord_1 : guardWord 1 = PatternedWordData.expectedWordAt 1 := by
  decide

@[simp] theorem guardWord_2 : guardWord 2 = PatternedWordData.expectedWordAt 2 := by
  decide

@[simp] theorem guardWord_3 : guardWord 3 = PatternedWordData.expectedWordAt 3 := by
  decide

@[simp] theorem guardWord_4 : guardWord 4 = PatternedWordData.expectedWordAt 4 := by
  decide

@[simp] theorem guardWord_5 : guardWord 5 = PatternedWordData.expectedWordAt 5 := by
  decide

@[simp] theorem guardWord_6 : guardWord 6 = PatternedWordData.expectedWordAt 6 := by
  decide

@[simp] theorem guardWord_7 : guardWord 7 = PatternedWordData.expectedWordAt 7 := by
  decide

@[simp] theorem guardWord_8 : guardWord 8 = PatternedWordData.expectedWordAt 8 := by
  decide

@[simp] theorem guardWord_9 : guardWord 9 = PatternedWordData.expectedWordAt 9 := by
  decide

@[simp] theorem guardWord_10 : guardWord 10 = PatternedWordData.expectedWordAt 10 := by
  decide

@[simp] theorem guardWord_11 : guardWord 11 = PatternedWordData.expectedWordAt 11 := by
  decide

@[simp] theorem guardWord_12 : guardWord 12 = PatternedWordData.expectedWordAt 12 := by
  decide

@[simp] theorem guardWord_13 : guardWord 13 = PatternedWordData.expectedWordAt 13 := by
  decide

@[simp] theorem guardWord_14 : guardWord 14 = PatternedWordData.expectedWordAt 14 := by
  decide

@[simp] theorem guardWord_15 : guardWord 15 = PatternedWordData.expectedWordAt 15 := by
  decide

@[simp] theorem guardWord_16 : guardWord 16 = PatternedWordData.expectedWordAt 16 := by
  decide

@[simp] theorem guardWord_17 : guardWord 17 = PatternedWordData.expectedWordAt 17 := by
  decide

@[simp] theorem guardWord_18 : guardWord 18 = PatternedWordData.expectedWordAt 18 := by
  decide

@[simp] theorem guardWord_19 : guardWord 19 = PatternedWordData.expectedWordAt 19 := by
  decide

@[simp] theorem guardWord_20 : guardWord 20 = PatternedWordData.expectedWordAt 20 := by
  decide

@[simp] theorem guardWord_21 : guardWord 21 = PatternedWordData.expectedWordAt 21 := by
  decide

@[simp] theorem guardWord_22 : guardWord 22 = PatternedWordData.expectedWordAt 22 := by
  decide

@[simp] theorem guardWord_23 : guardWord 23 = PatternedWordData.expectedWordAt 23 := by
  decide

@[simp] theorem guardWord_24 : guardWord 24 = PatternedWordData.expectedWordAt 24 := by
  decide

@[simp] theorem guardWord_25 : guardWord 25 = PatternedWordData.expectedWordAt 25 := by
  decide

@[simp] theorem guardWord_26 : guardWord 26 = PatternedWordData.expectedWordAt 26 := by
  decide

@[simp] theorem guardWord_27 : guardWord 27 = PatternedWordData.expectedWordAt 27 := by
  decide

@[simp] theorem guardWord_28 : guardWord 28 = PatternedWordData.expectedWordAt 28 := by
  decide

@[simp] theorem guardWord_29 : guardWord 29 = PatternedWordData.expectedWordAt 29 := by
  decide

@[simp] theorem guardWord_30 : guardWord 30 = PatternedWordData.expectedWordAt 30 := by
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar

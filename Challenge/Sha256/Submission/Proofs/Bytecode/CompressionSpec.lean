import Challenge.Sha256.Submission.Proofs.Bytecode.Compression
import Challenge.Sha256.Submission.Proofs.Bytecode.ScheduleCorrect

set_option warningAsError true

namespace Challenge.Sha256.Submission.Proofs.Bytecode.CompressionCorrect

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM

/-- The eight SHA-256 working variables, in `a` through `h` order. -/
structure Working where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32
deriving DecidableEq

/-- One mathematical SHA-256 compression round. -/
def round (x : Working) (k w : UInt32) : Working :=
  let t1 := x.h + Sha256.bigSigma1 x.e + Sha256.Ch x.e x.f x.g + k + w
  let t2 := Sha256.bigSigma0 x.a + Sha256.Maj x.a x.b x.c
  { a := t1 + t2, b := x.a, c := x.b, d := x.c
    e := x.d + t1, f := x.e, g := x.f, h := x.g }

/-- The bytecode's working-memory region represents `x`. -/
def Represents (s : State) (x : Working) : Prop :=
  Compression.hValue s 0 = Challenge.EvmProof.Word.ofUInt32 x.a ∧
  Compression.hValue s 1 = Challenge.EvmProof.Word.ofUInt32 x.b ∧
  Compression.hValue s 2 = Challenge.EvmProof.Word.ofUInt32 x.c ∧
  Compression.hValue s 3 = Challenge.EvmProof.Word.ofUInt32 x.d ∧
  Compression.hValue s 4 = Challenge.EvmProof.Word.ofUInt32 x.e ∧
  Compression.hValue s 5 = Challenge.EvmProof.Word.ofUInt32 x.f ∧
  Compression.hValue s 6 = Challenge.EvmProof.Word.ofUInt32 x.g ∧
  Compression.hValue s 7 = Challenge.EvmProof.Word.ofUInt32 x.h

/-- Functional working state after `n` SHA-256 rounds. -/
def rounds (initial : Working) (padded : ByteArray) (blockOff : Nat) :
    Nat → Working
  | 0 => initial
  | n + 1 => round (rounds initial padded blockOff n) Sha256.K[n]!
      (ScheduleCorrect.scheduleWord padded blockOff n)

end Challenge.Sha256.Submission.Proofs.Bytecode.CompressionCorrect

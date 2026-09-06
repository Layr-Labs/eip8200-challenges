import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationParameter

set_option warningAsError true
set_option maxRecDepth 30000

/-!
# Mask-cache stack projection

The masked helpers keep one extra word, `M = 0xffffffff`, immediately before
the cached factor.  This file records the ABI and the only non-structural
word identity used by the left-lane rotation rewrite.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskProjection

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.EvmProof.Word
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationParameter

def mask : UInt256 := UInt256.ofNat 0xffffffff

def physicalStack (logical suffix : List UInt256) : List UInt256 :=
  logical ++ [mask] ++ suffix

theorem physicalStack_drop_cache (logical suffix : List UInt256) :
    (physicalStack logical suffix).drop logical.length = mask :: suffix := by
  simp [physicalStack]

def maskQuadHelperEntry (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (c0 c1 c2 c3 : UInt256) (working : Compression.EvmWorking)
    (rho : List UInt256) : State :=
  { s with
    pc := startPC
    stack := [p0, returnPC, c0, p1, c1, p2, c2, p3, c3] ++
      roundWords working ++ [mask, factor] ++ rho }

def maskQuadAfterHelperBeforeJump (s : State) (endPC returnPC : UInt256)
    (j : Nat) (working : Compression.EvmWorking)
    (p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat)
    (constant : UInt256) (rho : List UInt256) : State :=
  { s with
    pc := endPC
    stack := returnPC :: roundWords
      (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant) ++
      [mask, factor] ++ rho
    memory := s.memory
    activeWords := quadActiveWordsAfterUInt256_4 s
      p0.toNat p1.toNat p2.toNat p3.toNat }

theorem left_factor_shift_eq (u : UInt256) (r : Nat)
    (hu : u.toNat < 2 ^ 32) (hr0 : 0 < r) (hr32 : r < 32) :
    UInt256.shiftRight
        (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) u)
        (UInt256.ofNat (32 - r)) =
      UInt256.shiftRight
        (UInt256.mul u
          (UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
            (UInt256.ofNat r)))
        (UInt256.ofNat 32) := by
  exact factor_shift_eq u r hu hr0 hr32

theorem left_raw_rotation_eq (u : UInt256) (r : Nat)
    (hu : u.toNat < 2 ^ 32) (hr0 : 0 < r) (hr32 : r < 32) :
    UInt256.shiftRight
        (UInt256.mul u
          (UInt256.shiftLeft (UInt256.ofNat (0x100000001 : Nat))
            (UInt256.ofNat r)))
        (UInt256.ofNat 32) = StackRound.stackRawRot u r := by
  exact rawRot_mul_shifted u r hu hr0 hr32

end Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskProjection

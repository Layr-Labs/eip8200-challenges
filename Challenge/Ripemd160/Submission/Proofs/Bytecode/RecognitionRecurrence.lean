import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSwar

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionRecurrence
open EvmSemantics
open EvmSemantics.EVM

def advance (c : Nat) (w : UInt256) : UInt256 :=
  UInt256.xor
    (UInt256.add (UInt256.land w PatternedSwar.m7)
      (UInt256.mul (UInt256.ofNat c) PatternedSwar.M))
    (UInt256.land (UInt256.lnot w) PatternedSwar.m8)

def boundary (k : Nat) : Bool := k == 7 || k == 15 || k == 23

def baseWord : Nat → UInt256
  | 0 => PatternedSwar.P
  | k + 1 => advance (if boundary k then 43 else 32) (baseWord k)

def correction (off : UInt256) : UInt256 :=
  UInt256.mul
    (UInt256.shiftRight PatternedSwar.M
      (UInt256.ofNat 216 - UInt256.mul (UInt256.ofNat 40)
        (UInt256.shiftRight off (UInt256.ofNat 8))))
    (UInt256.ofNat 11)

def compareWord (k : Nat) : UInt256 :=
  if boundary k then
    PatternedSwar.straddleAdd (baseWord k) (correction (UInt256.ofNat (32 * k)))
  else baseWord k

private theorem baseWords : ∀ k : Fin 32,
    baseWord k.val = PatternedSwar.rawWord k.val := by decide

theorem baseWord_eq_rawWord (k : Nat) (hk : k < 32) :
    baseWord k = PatternedSwar.rawWord k := baseWords ⟨k, hk⟩

private theorem corrections : ∀ k : Fin 31,
    correction (UInt256.ofNat (32 * k.val)) =
      PatternedSwar.straddleCorrection (UInt256.ofNat (32 * k.val)) := by decide

theorem correction_eq_original (k : Nat) (hk : k < 31) :
    correction (UInt256.ofNat (32 * k)) =
      PatternedSwar.straddleCorrection (UInt256.ofNat (32 * k)) := corrections ⟨k, hk⟩

private theorem fullWords : ∀ k : Fin 31,
    compareWord k.val = PatternedWordData.expectedWordAt k.val := by decide

theorem compareWord_eq_expected (k : Nat) (hk : k < 31) :
    compareWord k = PatternedWordData.expectedWordAt k := fullWords ⟨k, hk⟩

/-- The final load observes only bytes992..999, not the fourth straddle. -/
theorem partial31 :
    UInt256.shiftRight (baseWord 31) (UInt256.ofNat 192) =
      UInt256.shiftRight (PatternedWordData.expectedWordAt 31) (UInt256.ofNat 192) := by
  decide

#print axioms baseWord_eq_rawWord
#print axioms correction_eq_original
#print axioms compareWord_eq_expected
#print axioms partial31

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionRecurrence

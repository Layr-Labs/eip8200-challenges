import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCryptoBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Core
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactGap

set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
open EvmSemantics PairedLaneUInt256Bridge Paired144Core
abbrev WordLane := PairedLaneWordRound.WordLane
abbrev CryptoLane := PairedLaneCryptoBridge.CryptoLane

def pairWord : UInt256 := word pairMask
def lowerWord : UInt256 := word (pack (BitVec.allOnes 32) 0#32)
def upperWord : UInt256 := word (pack 0#32 (BitVec.allOnes 32))
def compactMaskWord : UInt256 := UInt256.ofNat ((2 ^ 32 - 1) * (1 + 2 ^ 72))
def coefficientWord (u v : Nat) : UInt256 := word (Paired144CompactGap.coefficient u v)
def factorWord : UInt256 := coefficientWord 6 0

def wordF (j : Nat) (b c d : UInt256) : UInt256 :=
  match j with
  | 0 => UInt256.xor (UInt256.xor b c) d
  | 1 => UInt256.xor (UInt256.land (UInt256.xor c d) b) d
  | 2 => UInt256.xor (UInt256.lor (UInt256.xor c pairWord) b) d
  | 3 => UInt256.xor (UInt256.land (UInt256.xor b c) d) c
  | _ => UInt256.xor (UInt256.lor (UInt256.xor d pairWord) c) b

def booleanPair (j : Nat) (b c d : UInt256) : UInt256 :=
  match j with
  | 0 => UInt256.xor (wordF 0 b c d)
      (UInt256.land (UInt256.lor (UInt256.lnot c) d) upperWord)
  | 1 => UInt256.xor (wordF 1 b c d)
      (UInt256.land (UInt256.xor (wordF 1 b c d) (wordF 3 b c d)) upperWord)
  | 2 => wordF 2 b c d
  | 3 => UInt256.xor (wordF 3 b c d)
      (UInt256.land (UInt256.xor (wordF 3 b c d) (wordF 1 b c d)) upperWord)
  | _ => UInt256.xor (wordF 0 b c d)
      (UInt256.land (UInt256.lor (UInt256.lnot c) d) lowerWord)

/-- Deliberately unmasked: compact rotation consumes this exact physical sum. -/
def wordSum (j : Nat) (a b c d message k : UInt256) : UInt256 :=
  UInt256.add (UInt256.add (UInt256.add a (booleanPair j b c d)) message) k

def wordShift (x : UInt256) (n : Nat) : UInt256 :=
  UInt256.shiftRight (UInt256.mul x factorWord) (UInt256.ofNat n)
def wordScale (x mask : UInt256) (d : Nat) : UInt256 :=
  UInt256.add (UInt256.mul (UInt256.ofNat (2 ^ d - 1)) (UInt256.land mask x)) x

def wordCompact (x : UInt256) : UInt256 :=
  UInt256.land (UInt256.lor x (UInt256.shiftRight x (UInt256.ofNat 72))) compactMaskWord

def usesCompact (r s : Nat) : Prop := s < r ∧ (r - s = 2 ∨ r - s = 3 ∨ r - s = 6)
instance (r s : Nat) : Decidable (usesCompact r s) := inferInstanceAs (Decidable (_ ∧ _))

def wordRotate (x : UInt256) (r s : Nat) : UInt256 :=
  if usesCompact r s then
    UInt256.shiftRight (UInt256.mul (wordCompact x) (coefficientWord (r - s) 0))
      (UInt256.ofNat (32 - s))
  else
    let y := UInt256.land x pairWord
    if r = s then wordShift y (38 - r)
    else if s < r then wordShift (wordScale y lowerWord (r - s)) (38 - s)
    else wordShift (wordScale y upperWord (s - r)) (38 - r)

def wordT (j r s : Nat) (a b c d e message k : UInt256) : UInt256 :=
  UInt256.land (UInt256.add (wordRotate (wordSum j a b c d message k) r s) e) pairWord

def wordStep (j r s : Nat) (message k : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, wordT j r s q.a q.b q.c q.d q.e message k, q.b,
    UInt256.land (wordShift q.c 28) pairWord, q.d⟩

def adjustedK (k : UInt256) : UInt256 :=
  UInt256.add (UInt256.add k pairWord) (UInt256.ofNat 1)
def hoistedBoolean (b c d : UInt256) : UInt256 :=
  UInt256.xor (UInt256.lor (UInt256.lnot c) b) d
def rawHoistedBoolean (b c d : UInt256) : UInt256 :=
  UInt256.xor d (UInt256.lor b (UInt256.lnot c))
def hoistedSum (a b c d message cachedK : UInt256) : UInt256 :=
  UInt256.add (UInt256.add (UInt256.add a (hoistedBoolean b c d)) message) cachedK

def rawWordStep2 (r s : Nat) (message cachedK : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, UInt256.land (UInt256.add
      (wordRotate (hoistedSum q.a q.b q.c q.d message cachedK) r s) q.e) pairWord,
    q.b, UInt256.land (wordShift q.c 28) pairWord, q.d⟩

/-- The last physical round leaves both updated words unmasked. -/
def rawFinish (r s : Nat) (message k : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, UInt256.add (wordRotate (wordSum 4 q.a q.b q.c q.d message k) r s) q.e,
    q.b, wordShift q.c 28, q.d⟩

def packCrypto (l q : CryptoLane) : WordLane :=
  ⟨word (pack l.a.toBitVec q.a.toBitVec), word (pack l.b.toBitVec q.b.toBitVec),
    word (pack l.c.toBitVec q.c.toBitVec), word (pack l.d.toBitVec q.d.toBitVec),
    word (pack l.e.toBitVec q.e.toBitVec)⟩
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound

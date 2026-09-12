import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Algorithm
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound
open PairedLaneCryptoBridge (cryptoStep)
def packed32 (lo hi : UInt32) : UInt256 := word (pack lo.toBitVec hi.toBitVec)
def key (i : Nat) : UInt256 :=
  packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!
def physicalKey (i : Nat) : UInt256 := if i / 16 = 2 then adjustedK (key i) else key i
def step (i : Nat) (message : UInt256) (q : WordLane) : WordLane :=
  if i / 16 = 2 then
    rawWordStep2 Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]! message (physicalKey i) q
  else wordStep (i / 16) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]! message (key i) q
def fold (message : Nat → UInt256) : Nat → WordLane → WordLane
  | 0, q => q
  | i + 1, q => step i (message i) (fold message i q)
def leftFold (words : Nat → UInt32) : Nat → CryptoLane → CryptoLane
  | 0, q => q
  | i + 1, q => cryptoStep (i / 16) Crypto.Ripemd160.s[i]!
      (words Crypto.Ripemd160.r[i]!) Crypto.Ripemd160.K[i / 16]! (leftFold words i q)
def rightFold (words : Nat → UInt32) : Nat → CryptoLane → CryptoLane
  | 0, q => q
  | i + 1, q => cryptoStep (4 - i / 16) Crypto.Ripemd160.sP[i]!
      (words Crypto.Ripemd160.rP[i]!) Crypto.Ripemd160.KP[i / 16]! (rightFold words i q)
def MessageReady (message : Nat → UInt256) (words : Nat → UInt32) (count : Nat) : Prop :=
  ∀ i < count, message i = packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!)
def finish (message : Nat → UInt256) (q : WordLane) : WordLane :=
  rawFinish Crypto.Ripemd160.s[79]! Crypto.Ripemd160.sP[79]! (message 79) (key 79) q
def finalLane (message : Nat → UInt256) (q : WordLane) : WordLane :=
  finish message (fold message 79 q)
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Algorithm

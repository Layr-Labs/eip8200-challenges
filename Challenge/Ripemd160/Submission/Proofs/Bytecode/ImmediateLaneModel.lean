import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateIteration
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateStateFacts

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneModel

open EvmSemantics EvmSemantics.EVM
open ImmediateIteration

theorem leftConstant_eq (j : Nat) (hj : j < 5) :
    UInt256.ofNat (leftConstant j) =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!) := by
  interval_cases j <;> decide

theorem rightConstant_eq (j : Nat) (hj : j < 5) :
    UInt256.ofNat (rightConstant j) =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!) := by
  interval_cases j <;> decide

theorem leftSite_roundReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x620 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) :
    RoundTrace.roundReturned s (leftSite i).base (leftSite i).j.toNat
        (leftSite i).wordIndex (leftSite i).rotation (leftSite i).k (leftSite i).ret
        ([messageOffset, returnDest] ++ rest) =
      {CompressionTrace.leftRoundState s messageOffset returnDest rest i with
        pc := (leftSite i).ret
        stack := [messageOffset, returnDest] ++ rest} := by
  have hj : (UInt256.ofNat (i / 16)).toNat = i / 16 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk := leftConstant_eq (i / 16) (by omega)
  have h := (ImmediateModelMatch.leftRoundState_pinned s messageOffset returnDest
    rest i hi hactive tables constants (leftSite i).ret
      ([messageOffset, returnDest] ++ rest)).symm
  change RoundTrace.roundReturned s (UInt256.ofNat 192)
      (UInt256.ofNat (i / 16)).toNat
      (UInt256.ofNat (Crypto.Ripemd160.r[i]!))
      (UInt256.ofNat (Crypto.Ripemd160.s[i]!))
      (UInt256.ofNat (leftConstant (i / 16))) (leftSite i).ret
      ([messageOffset, returnDest] ++ rest) = _
  rw [hj, hk]
  exact h

theorem rightSite_roundReturned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x6c0 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!)) :
    RoundTrace.roundReturned s (rightSite i).base (rightSite i).j.toNat
        (rightSite i).wordIndex (rightSite i).rotation (rightSite i).k (rightSite i).ret
        ([messageOffset, returnDest] ++ rest) =
      {CompressionRightTrace.rightRoundState s messageOffset returnDest rest i with
        pc := (rightSite i).ret
        stack := [messageOffset, returnDest] ++ rest} := by
  have hj : (UInt256.ofNat (4 - i / 16)).toNat = 4 - i / 16 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk := rightConstant_eq (i / 16) (by omega)
  have h := (ImmediateModelMatch.rightRoundState_pinned s messageOffset returnDest
    rest i hi hactive tables constants (rightSite i).ret
      ([messageOffset, returnDest] ++ rest)).symm
  change RoundTrace.roundReturned s (UInt256.ofNat 352)
      (UInt256.ofNat (4 - i / 16)).toNat
      (UInt256.ofNat (Crypto.Ripemd160.rP[i]!))
      (UInt256.ofNat (Crypto.Ripemd160.sP[i]!))
      (UInt256.ofNat (rightConstant (i / 16))) (rightSite i).ret
      ([messageOffset, returnDest] ++ rest) = _
  rw [hj, hk]
  exact h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneModel

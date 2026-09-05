import Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 100000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundActiveWords

open EvmSemantics EvmSemantics.EVM
open ScheduleActiveWords

open private afterLoads xReturnedState afterFirstStores genericAfterThirdStore
  genericReturned from
  Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundTrace

private theorem ofNat_toNat (w : UInt256) : UInt256.ofNat w.toNat = w :=
  (Challenge.EvmProof.Word.word_eq_ofNat_toNat w).symm

private theorem slotAddress_toNat (base : Nat) (i : UInt256)
    (hi : i.toNat < 16) (hbase : base + 32 * i.toNat < 2 ^ 256) :
    (TableTrace.slotAddress (UInt256.ofNat base) i).toNat =
      base + 32 * i.toNat := by
  have hshift : UInt256.shiftLeft i (UInt256.ofNat 5) =
      UInt256.ofNat (32 * i.toNat) := by
    conv_lhs => rw [← ofNat_toNat i]
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
        (by omega : i.toNat * 2 ^ 5 < 2 ^ 256)]
    congr 1
    omega
  unfold TableTrace.slotAddress
  rw [hshift]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem addWord_toNat (base off : Nat)
    (hlt : base + off < 2 ^ 256) :
    (UInt256.ofNat base + UInt256.ofNat off).toNat = base + off := by
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat hlt,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]

private theorem afterLoads_activeWords (s : State) (base : Nat)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 0x80 + 32 ≤ 67 * 32) :
    (afterLoads s (UInt256.ofNat base)).activeWords = s.activeWords := by
  let q₀ := { s with activeWords :=
    s.activeWordsAfterUInt256 (UInt256.ofNat base).toNat 32 }
  let q₁ := { q₀ with activeWords := (q₀.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x20).toNat 32) }
  let q₂ := { q₁ with activeWords := (q₁.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x40).toNat 32) }
  let q₃ := { q₂ with activeWords := (q₂.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x60).toNat 32) }
  have h₀ : q₀.activeWords = s.activeWords := by
    apply activeWordsAfterUInt256_eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : base < 2 ^ 256)]
    omega
  have h₁ : q₁.activeWords = s.activeWords := by
    apply Eq.trans (activeWordsAfterUInt256_eq q₀ _ 32 (by
      rw [addWord_toNat base 0x20 (by omega), h₀]
      omega)) h₀
  have h₂ : q₂.activeWords = s.activeWords := by
    apply Eq.trans (activeWordsAfterUInt256_eq q₁ _ 32 (by
      rw [addWord_toNat base 0x40 (by omega), h₁]
      omega)) h₁
  have h₃ : q₃.activeWords = s.activeWords := by
    apply Eq.trans (activeWordsAfterUInt256_eq q₂ _ 32 (by
      rw [addWord_toNat base 0x60 (by omega), h₂]
      omega)) h₂
  unfold afterLoads
  change (q₃.activeWordsAfterUInt256
    (UInt256.ofNat base + UInt256.ofNat 0x80).toNat 32) = _
  exact (activeWordsAfterUInt256_eq q₃ _ 32 (by
    rw [addWord_toNat base 0x80 (by omega), h₃]
    omega)).trans h₃

private theorem storedWord_activeWords (s : State) (base index : Nat)
    (hindex : index < 16) (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 32 * index + 32 ≤ 67 * 32) (value : UInt256) :
    (TableTrace.storedWord s (UInt256.ofNat base) (UInt256.ofNat index)
      value).activeWords = s.activeWords := by
  unfold TableTrace.storedWord
  apply activeWordsAfterUInt256_eq
  rw [slotAddress_toNat base (UInt256.ofNat index)
    (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : index < 2 ^ 256)]
      exact hindex)
    (by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : index < 2 ^ 256)]
      omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : index < 2 ^ 256)]
  omega

/-- A compiled round only touches fixed scratch words, provided its X selector
is one of the sixteen schedule entries. -/
theorem roundReturned_activeWords (s : State) (base : Nat)
    (hbase : base + 0x80 + 32 ≤ 67 * 32) (j : Nat)
    (wordIndex rotation k returnDest : UInt256) (hword : wordIndex.toNat < 16)
    (rest : List UInt256) (hactive : 67 ≤ s.activeWords.toNat) :
    (RoundTrace.roundReturned s (UInt256.ofNat base) j wordIndex rotation k
      returnDest rest).activeWords = s.activeWords := by
  let loaded := afterLoads s (UInt256.ofNat base)
  have hloaded : loaded.activeWords = s.activeWords :=
    afterLoads_activeWords s base hactive hbase
  let xret := xReturnedState s (UInt256.ofNat base) j wordIndex rotation k
    returnDest rest
  have hx : xret.activeWords = s.activeWords := by
    unfold xret xReturnedState TableTrace.atReturned
    apply Eq.trans (activeWordsAfterUInt256_eq loaded _ 32 (by
      rw [slotAddress_toNat 0x2a0 wordIndex hword (by omega), hloaded]
      omega)) hloaded
  let first := afterFirstStores xret (UInt256.ofNat base)
  have hfirst : first.activeWords = s.activeWords := by
    unfold first afterFirstStores
    have h₀ := storedWord_activeWords xret base 0 (by omega)
      (by rw [hx]; exact hactive) (by omega) (RoundTrace.loadedE xret (UInt256.ofNat base))
    exact (storedWord_activeWords
      (TableTrace.storedWord xret (UInt256.ofNat base) (UInt256.ofNat 0)
        (RoundTrace.loadedE xret (UInt256.ofNat base)))
      base 4 (by omega) (by rw [h₀, hx]; exact hactive) (by omega)
      (RoundTrace.loadedD xret (UInt256.ofNat base))).trans (h₀.trans hx)
  have hthird : (genericAfterThirdStore first (UInt256.ofNat base)
      (RoundTrace.loadedC s (UInt256.ofNat base))).activeWords = s.activeWords := by
    unfold genericAfterThirdStore
    exact (storedWord_activeWords first base 3 (by omega)
      (by rw [hfirst]; exact hactive) (by omega) _).trans hfirst
  unfold RoundTrace.roundReturned genericReturned
  dsimp only
  have h₂ := storedWord_activeWords
    (genericAfterThirdStore first (UInt256.ofNat base)
      (RoundTrace.loadedC s (UInt256.ofNat base)))
    base 2 (by omega) (by rw [hthird]; exact hactive) (by omega)
    (RoundTrace.loadedB s (UInt256.ofNat base))
  exact (storedWord_activeWords
    (TableTrace.storedWord
      (genericAfterThirdStore first (UInt256.ofNat base)
        (RoundTrace.loadedC s (UInt256.ofNat base)))
      (UInt256.ofNat base) (UInt256.ofNat 2)
      (RoundTrace.loadedB s (UInt256.ofNat base)))
    base 1 (by omega) (by rw [h₂, hthird]; exact hactive) (by omega) _).trans
      (h₂.trans hthird)


end Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundActiveWords


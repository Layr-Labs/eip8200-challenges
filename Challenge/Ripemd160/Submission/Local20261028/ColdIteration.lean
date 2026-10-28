import Challenge.Ripemd160.Submission.Local20261028.ColdPadSkipEntry
import Challenge.Ripemd160.Submission.Local20261028.NormalIteration
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Iteration
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open NormalPrepare
abbrev entry := PadSkipEntry.entryState
abbrev states (input : ByteArray) := NormalIteration.states (entry input) 1056
abbrev hashes (input : ByteArray) := NormalIteration.hashes (entry input) 1056 StackRunBridge.initialHashState

theorem clear (input : ByteArray) (hfit : CalldataFits input) : Clear (entry input).memory := by
  have bounds : RipemdTableOrder20261027.clearAddresses.all (fun a => decide (a < 1056 ∧ a ≠ 165 ∧ a ≠ 188)) = true := by decide +kernel
  intro a ha
  have b : a < 1056 ∧ a ≠ 165 ∧ a ≠ 188 := of_decide_eq_true ((List.all_eq_true.mp bounds) a ha)
  exact PadSkipEntry.entryState_zero_below input hfit a b.1 b.2

theorem word_active (current : UInt256) (address : Nat)
    (ha : (address+63)/32 ≤ current.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32:Nat) ≠ 0)]
  rw [show (address+32-1)/32+1 = (address+63)/32 by omega]
  change UInt256.ofNat (max current.toNat ((address+63)/32)) = current
  rw [Nat.max_eq_left ha]
  exact (Word.word_eq_ofNat_toNat current).symm

theorem scheduled_active (s : State) (p : Nat) (hb : p+64 < 2^256)
    (ha : (p+95)/32 ≤ s.activeWords.toNat) :
    (scheduled s p).activeWords = s.activeWords := by
  have a : DenseScheduleTemplate.activeAfterWord s.activeWords (UInt256.ofNat p) = s.activeWords := by
    unfold DenseScheduleTemplate.activeAfterWord
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    exact word_active _ p (by omega)
  change DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p) = s.activeWords
  unfold DenseScheduleTemplate.loadedActiveWords
  rw [a]
  unfold DenseScheduleTemplate.activeAfterWord
  rw [Word.ofNat_add_ofNat (by omega), Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact word_active _ (p+32) (by simpa only [Nat.add_assoc] using ha)

theorem active (input : ByteArray) (hfit : CalldataFits input) (count : Nat)
    (hc : count ≤ DriverTrace.blockCount input)
    (hnopad : ∀ i, i < count → ¬ (input.size = DriverTrace.blockOffset i ∧ input.size < 256)) :
    (states input count).activeWords = (entry input).activeWords := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hi := ih (by omega) (fun i hi => hnopad i (by omega))
    have ha := PadSkipEntry.entryState_allocated input hfit count (by omega) (hnopad count (by omega))
    have hb : 1056+64*count+64 < 2^256 := by
      have := Padding.paddedLength_lt input.size
      have := DriverTrace.paddedLength_eq_blockCount input
      unfold CalldataFits at hfit
      omega
    change (scheduled (states input count) (1056+64*count)).activeWords = _
    rw [scheduled_active _ _ hb,hi]
    rw [hi]
    simpa only [PersistentStaggerTable.messagePointer,DriverTrace.blockOffset,Padding.messageOffset,Nat.mul_comm] using ha

theorem hash_spec (input : ByteArray) (hfit : CalldataFits input) (count : Nat)
    (hc : count ≤ DriverTrace.blockCount input)
    (hnopad : ∀ i, i < count → ¬ (input.size = DriverTrace.blockOffset i ∧ input.size < 256)) :
    CompressionCorrect.hashArray (hashes input count) = CompressionSeamBridge.hashAfter input count := by
  have hb : 1056+64*count < 2^256 := by
    have := Padding.paddedLength_lt input.size
    have := DriverTrace.paddedLength_eq_blockCount input
    unfold CalldataFits at hfit
    omega
  exact NormalIteration.hash_spec (entry input) 1056 0 count (Padding.paddedMessage input)
    StackRunBridge.initialHashState (by decide) hb (clear input hfit)
    (fun i hi => by
      have h := PadSkipEntry.entryState_blockAt input hfit i (by omega) (hnopad i hi)
      simpa only [Nat.zero_add,Nat.mul_comm,DriverTrace.messageOffsetWord,DriverTrace.blockOffset,Padding.messageOffset] using h)

theorem last (input : ByteArray) (hfit : CalldataFits input)
    (hcold : ¬ (input.size % 64 = 0 ∧ input.size < 256))
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    (UInt256.ofNat (32 * (states input (i+1)).activeWords.toNat)).toNat <
      (UInt256.ofNat (1056+64*i) + UInt256.ofNat 128).toNat ↔
      i+1 = DriverTrace.blockCount input := by
  have hnopad : ∀ j, ¬ (input.size = DriverTrace.blockOffset j ∧ input.size < 256) := by
    intro j hj
    apply hcold
    unfold DriverTrace.blockOffset at hj
    exact ⟨by omega,hj.2⟩
  rw [active input hfit (i+1) (by omega) (fun j _ => hnopad j)]
  have hentry : entry input = PaddingTrace.padReturned input := PaddingTrace.entryState_miss input hcold
  rw [hentry]
  have hlo := PaddingTrace.padReturned_allocated input hfit
  have hup := PaddingTrace.padReturned_active_upper input hfit
  have hP := DriverTrace.paddedLength_eq_blockCount input
  have hPlt := Padding.paddedLength_lt input.size
  unfold Padding.messageOffset at hlo hup
  unfold CalldataFits at hfit
  have hm : (UInt256.ofNat (32 * (PaddingTrace.padReturned input).activeWords.toNat)).toNat =
      32 * (PaddingTrace.padReturned input).activeWords.toNat := by
    rw [Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ho : (UInt256.ofNat (1056+64*i)+UInt256.ofNat 128).toNat = 1056+64*i+128 := by
    rw [Word.ofNat_add_ofNat (by omega),Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hm,ho]
  omega
#print axioms clear
#print axioms active
#print axioms hash_spec
#print axioms last
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Iteration

import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPaddingMemory
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable ColdHighPaddingMemory

def tableMemory (input : ByteArray) (i : Nat) : ByteArray :=
  StaggerTableLayout.resultMemory (finalMemory input i)
    (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i))

theorem extracted_words (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i<DriverTrace.blockCount input) (hh : input.size=DriverTrace.blockOffset i)
    (k : Nat) (hk : k<16) :
    PairedScheduleData.extractedWord (finalMemory input i) (messagePointer i) k = Word.ofUInt32 (blockWords input i k) := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk
    (messagePointer_bound input hfit i hi)]
  change ScheduleCorrect.expectedWord (finalMemory input i) (DriverTrace.messageOffsetWord i) k = _
  rw [finalMemory_blockAt input hfit i hi hh k hk,blockWords_eq_readLE32 input i k hk]

theorem ready (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i<DriverTrace.blockCount input) (hh : input.size=DriverTrace.blockOffset i) :
    StaggerMessage.Ready (tableMemory input i) (blockWords input i) := by
  have hsplit (k : Nat) := StaggerScratch.dirtyWord_split (finalMemory input i) (messagePointer i) k
  exact StaggerMessage.ready_junk (finalMemory input i) (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i)) (blockWords input i)
    (fun k => (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat / 2 ^ 32)
    (fun k hk => by
      show (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat = _
      conv_lhs => rw [(hsplit k).1]
      rw [extracted_words input hfit i hi hh k hk, Word.ofUInt32_toNat])
    (fun k _ => (hsplit k).2.1)
    (fun k _ h2 => Nat.lt_trans ((hsplit k).2.2.1 h2) (by decide))
    (fun k _ h2 _ => (hsplit k).2.2.1 h2)
    (fun k _ hd => by
      have hd' : ¬ (k = 1 ∨ k = 2) := fun h =>
        hd (h.elim (fun h1 => Or.inl h1) (fun h2 => Or.inr (Or.inl h2)))
      have h0 : (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat / 2 ^ 32 = 0 := (hsplit k).2.2.2 hd'
      exact ⟨by show (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat / 2 ^ 32 < 2 ^ 23; rw [h0]; decide, fun _ => h0⟩)

#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady

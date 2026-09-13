import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Ghost
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def actualMemory (memory : ByteArray) (low : UInt256) : ByteArray :=
  Source32Memory.writeWord (Source32Memory.source32Memory memory) 28 low

def ghostMemory (memory : ByteArray) (low : UInt256) : ByteArray :=
  StaggerScratch.scratchMemory memory low Source32Memory.source32Word

/-- The source-loading window agrees; the two complete memories need not agree. -/
theorem window (m g : ByteArray) (low : UInt256)
    (hprefix : ∀ a, a < 28 → m[a]?.getD 0 = g[a]?.getD 0)
    (hzero : ∀ a, 88 ≤ a → a < 92 → m[a]?.getD 0 = 0)
    (a : Nat) (ha : a < 92) :
    (actualMemory m low)[a]?.getD 0 = (ghostMemory g low)[a]?.getD 0 := by
  by_cases hlow : a < 28
  · simp only [actualMemory, ghostMemory, Source32Memory.source32Memory,
      Source32Memory.writeWord, StaggerScratch.scratchMemory, PairedScheduleMemory.writeWord,
      MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hprefix a hlow
  · by_cases hmid : a < 60
    · simp only [actualMemory, ghostMemory, Source32Memory.writeWord,
        StaggerScratch.scratchMemory, PairedScheduleMemory.writeWord,
        MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      rw [if_pos (by omega), if_pos (by omega)]
    · have ha60 : 60 ≤ a := by omega
      rw [actualMemory, Source32Memory.write28_frame60 _ low a ha60]
      have hs := Source32Memory.read60_bytes m hzero (a - 60) (by omega)
      rw [show 60 + (a - 60) = a by omega] at hs
      rw [hs]
      simp only [ghostMemory, StaggerScratch.scratchMemory, PairedScheduleMemory.writeWord,
        MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      rw [if_neg (by omega), if_pos (by omega)]

theorem readWord_window (m g : ByteArray) (low : UInt256)
    (hprefix : ∀ a, a < 28 → m[a]?.getD 0 = g[a]?.getD 0)
    (hzero : ∀ a, 88 ≤ a → a < 92 → m[a]?.getD 0 = 0)
    (start : Nat) (hstart : start + 32 ≤ 92) :
    MachineState.readWord (actualMemory m low) start =
      MachineState.readWord (ghostMemory g low) start := by
  have hr : MachineState.readPadded (actualMemory m low) start 32 =
      MachineState.readPadded (ghostMemory g low) start 32 := by
    apply Memory.readPadded_congr
    intro i hi
    exact window m g low hprefix hzero _ (by omega)
  unfold MachineState.readWord
  rw [hr]

theorem poolWordD_eq (m g : ByteArray) (low : UInt256)
    (hprefix : ∀ a, a < 28 → m[a]?.getD 0 = g[a]?.getD 0)
    (hzero : ∀ a, 88 ≤ a → a < 92 → m[a]?.getD 0 = 0)
    (i : Nat) (hi : i < 16) :
    StaggerScratch.poolWordD (actualMemory m low) i =
      StaggerScratch.poolWordD (ghostMemory g low) i := by
  have hr := readWord_window m g low hprefix hzero (4 * i) (by omega)
  unfold StaggerScratch.poolWordD StaggerScratch.poolWord
  rw [hr]

/-- The table certificate accepts an arbitrary physical base memory and a ghost message. -/
theorem tableReady (tableBase actual ghost : ByteArray) (p : Nat) (scalar : Nat → UInt32)
    (hpool : ∀ k, k < 16 → StaggerScratch.poolWordD actual k = StaggerScratch.dirtyWord ghost p k)
    (hscalar : ∀ k, k < 16 → PairedScheduleData.extractedWord ghost p k = Word.ofUInt32 (scalar k)) :
    StaggerMessage.Ready
      (StaggerTableLayout.resultMemory tableBase (StaggerScratch.poolWordD actual)) scalar := by
  have hsplit (k : Nat) := StaggerScratch.dirtyWord_split ghost p k
  exact StaggerMessage.ready_junk tableBase (StaggerScratch.poolWordD actual) scalar
    (fun k => (StaggerScratch.dirtyWord ghost p k).toNat / 2 ^ 32)
    (fun k hk => by
      rw [hpool k hk]
      conv_lhs => rw [(hsplit k).1]
      rw [hscalar k hk, Word.ofUInt32_toNat])
    (fun k _ => (hsplit k).2.1)
    (fun k _ h2 => Nat.lt_trans ((hsplit k).2.2.1 h2) (by decide))
    (fun k _ h2 _ => (hsplit k).2.2.1 h2)
    (fun k _ hd => by
      have hd' : ¬ (k = 1 ∨ k = 2) := fun h =>
        hd (h.elim (fun h1 => Or.inl h1) (fun h2 => Or.inr (Or.inl h2)))
      have h0 : (StaggerScratch.dirtyWord ghost p k).toNat / 2 ^ 32 = 0 := (hsplit k).2.2.2 hd'
      exact ⟨by rw [h0]; decide, fun _ => h0⟩)

#print axioms window
#print axioms readWord_window
#print axioms poolWordD_eq
#print axioms tableReady
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Ghost

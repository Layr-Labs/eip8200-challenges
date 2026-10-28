import Challenge.Ripemd160.Submission.Local20261028.PadTailRaw
import Challenge.Ripemd160.Submission.Local20261028.Return32Output
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTailMath
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RipemdTerminalMaskWindows20261027 RipemdTerminalMasks20261027

private theorem raw_toUInt32_add (x y : UInt256) :
    Word.toUInt32 (UInt256.add x y) = Word.toUInt32 x + Word.toUInt32 y :=
  Word.toUInt32_add x y

theorem masked_words (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (m8 m16 : UInt256) :
    let f := PadTailRaw.fields (ScheduledTailFrame.bind h q) m8 m16
    let result := ScheduledTailFrame.combine h q
    mask (a f) = Word.ofUInt32 result.h4 ∧
    mask (b f) = Word.ofUInt32 result.h3 ∧
    mask (c f) = Word.ofUInt32 result.h2 ∧
    mask (d f) = Word.ofUInt32 result.h1 ∧
    e f = Word.ofUInt32 result.h0 := by
  change Word.mask32 (UInt256.add (Word.ofUInt32 h.h0)
      (UInt256.add (UInt256.shiftRight q.rc (UInt256.ofNat 144)) q.lb)) = _ ∧
    Word.mask32 (UInt256.add (UInt256.add (Word.ofUInt32 h.h4) q.la)
      (UInt256.shiftRight q.rb (UInt256.ofNat 144))) = _ ∧
    Word.mask32 (UInt256.add (UInt256.add (Word.ofUInt32 h.h3) q.le)
      (UInt256.shiftRight q.ra (UInt256.ofNat 144))) = _ ∧
    Word.mask32 (UInt256.add (Word.ofUInt32 h.h2)
      (UInt256.add (UInt256.shiftRight (UInt256.mul Paired144WordRound.factorPlusWord q.ld) (UInt256.ofNat 23))
        (UInt256.shiftRight q.re (UInt256.ofNat 144)))) = _ ∧
    Word.mask32 (UInt256.add (Word.ofUInt32 h.h1)
      (UInt256.add (UInt256.shiftRight q.rd (UInt256.ofNat 144)) q.lc)) = _
  simp only [ScheduledTailFrame.combine,ScheduledTailFrame.high,
    Paired144WordRound.wordShift, RawExpressionAC.mul_comm]
  simp only [Word.mask32_eq_ofUInt32, raw_toUInt32_add, Word.toUInt32_ofUInt32]
  repeat' apply And.intro
  all_goals congr 1
  all_goals try trivial
  all_goals apply UInt32.eq_of_toBitVec_eq
  all_goals simp only [UInt32.toBitVec_add]
  all_goals ac_rfl

theorem memory_eq (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (m8 m16 : UInt256) :
    (prepared s (PadTailRaw.fields (ScheduledTailFrame.bind h q) m8 m16)).memory =
      MemoryPackedOutput.memory s.memory (ScheduledTailFrame.combine h q) := by
  let f := PadTailRaw.fields (ScheduledTailFrame.bind h q) m8 m16
  change stores s.memory (a f) (b f) (c f) (d f) (e f) = _
  rw [← stores_eq]
  obtain ⟨ha,hb,hc,hd,he⟩ := masked_words h q m8 m16
  change mask (a f) = _ at ha
  change mask (b f) = _ at hb
  change mask (c f) = _ at hc
  change mask (d f) = _ at hd
  change e f = _ at he
  rw [ha,hb,hc,hd,he]
  simp only [stores, MemoryPackedOutput.memory, MemoryPackedOutput.store,
    PairedScheduleMemory.writeWord, Word.ofUInt32_toNat]

theorem read_eq (s : State) (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (m8 m16 : UInt256) :
    MachineState.readWord (prepared s (PadTailRaw.fields (ScheduledTailFrame.bind h q) m8 m16)).memory 16 =
      Return32Output.packedHash (ScheduledTailFrame.combine h q) := by
  rw [memory_eq, MemoryPackedOutput.readWord_eq]
  simp only [PackedOutputMath.pack5, PackedOutputMath.append32, Return32Output.packedHash, Word.lor_comm]

#print axioms masked_words
#print axioms memory_eq
#print axioms read_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTailMath

import Challenge.Sha256.Submission.Proofs.Bytecode.ResidentBridge
import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionSpec
import Challenge.Sha256.Submission.Proofs.Bytecode.PaddedBlockBridge
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.PairCorrectTest

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

theorem t10_eq (s : State) (j : Nat)
    (x : CompressionCorrect.Working) (k w : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k)
    (hw : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w) :
    Compression.t10 s j = Challenge.EvmProof.Word.ofUInt32
      (x.h + Sha256.bigSigma1 x.e + Sha256.Ch x.e x.f x.g + k + w) := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.t10
  rw [he, hf, hg, hh, hk, hw, Word.evmBigSigma1_ofUInt32,
    Word.evmCh_ofUInt32]
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32]
  congr 1
  simp only [Challenge.EvmProof.Word.toUInt32_add,
    Challenge.EvmProof.Word.toUInt32_ofUInt32]
  ac_rfl

theorem t20_eq (s : State) (x : CompressionCorrect.Working)
    (hx : CompressionCorrect.Represents s x) :
    Compression.t20 s = Challenge.EvmProof.Word.ofUInt32
      (Sha256.bigSigma0 x.a + Sha256.Maj x.a x.b x.c) := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.t20
  rw [ha, hb, hc, Word.evmBigSigma0_ofUInt32, Word.evmMaj_ofUInt32,
    Challenge.EvmProof.Word.mask32_add]

theorem pairA1_eq (s : State) (j : Nat)
    (x : CompressionCorrect.Working) (k w : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k)
    (hw : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w) :
    Compression.pairA1 s j = Challenge.EvmProof.Word.ofUInt32
      (CompressionCorrect.round x k w).a := by
  unfold Compression.pairA1
  rw [t20_eq s x hx, t10_eq s j x k w hx hk hw,
    Challenge.EvmProof.Word.mask32_add]
  simp only [CompressionCorrect.round]
  congr 1
  ac_rfl

theorem pairE1_eq (s : State) (j : Nat)
    (x : CompressionCorrect.Working) (k w : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k)
    (hw : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w) :
    Compression.pairE1 s j = Challenge.EvmProof.Word.ofUInt32
      (CompressionCorrect.round x k w).e := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.pairE1
  rw [t10_eq s j x k w ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ hk hw, hd,
    Challenge.EvmProof.Word.mask32_add]
  simp only [CompressionCorrect.round]

theorem t11_eq (s : State) (j : Nat)
    (x : CompressionCorrect.Working) (k0 w0 k1 w1 : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk0 : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k0)
    (hw0 : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w0)
    (hk1 : Compression.kValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 k1)
    (hw1 : Compression.wValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 w1) :
    Compression.t11 s j = Challenge.EvmProof.Word.ofUInt32
      ((CompressionCorrect.round x k0 w0).h +
        Sha256.bigSigma1 (CompressionCorrect.round x k0 w0).e +
        Sha256.Ch (CompressionCorrect.round x k0 w0).e
          (CompressionCorrect.round x k0 w0).f
          (CompressionCorrect.round x k0 w0).g + k1 + w1) := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.t11
  rw [pairE1_eq s j x k0 w0 ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ hk0 hw0,
    he, hf, hg, hk1, hw1, Word.evmBigSigma1_ofUInt32,
    Word.evmCh_ofUInt32]
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32]
  congr 1
  simp only [Challenge.EvmProof.Word.toUInt32_add,
    Challenge.EvmProof.Word.toUInt32_ofUInt32, CompressionCorrect.round]
  ac_rfl

theorem t21_eq (s : State) (j : Nat)
    (x : CompressionCorrect.Working) (k w : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k)
    (hw : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w) :
    Compression.t21 s j = Challenge.EvmProof.Word.ofUInt32
      (Sha256.bigSigma0 (CompressionCorrect.round x k w).a +
        Sha256.Maj (CompressionCorrect.round x k w).a
          (CompressionCorrect.round x k w).b
          (CompressionCorrect.round x k w).c) := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.t21
  rw [pairA1_eq s j x k w ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ hk hw,
    ha, hb, Word.evmBigSigma0_ofUInt32, Word.evmMaj_ofUInt32,
    Challenge.EvmProof.Word.mask32_add]
  rfl

theorem pairA2_eq (s : State) (j : Nat)
    (x : CompressionCorrect.Working) (k0 w0 k1 w1 : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk0 : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k0)
    (hw0 : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w0)
    (hk1 : Compression.kValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 k1)
    (hw1 : Compression.wValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 w1) :
    Compression.pairA2 s j = Challenge.EvmProof.Word.ofUInt32
      (CompressionCorrect.round (CompressionCorrect.round x k0 w0) k1 w1).a := by
  unfold Compression.pairA2
  rw [t21_eq s j x k0 w0 hx hk0 hw0,
    t11_eq s j x k0 w0 k1 w1 hx hk0 hw0 hk1 hw1,
    Challenge.EvmProof.Word.mask32_add]
  simp only [CompressionCorrect.round]
  congr 1
  ac_rfl

theorem pairE2_eq (s : State) (j : Nat)
    (x : CompressionCorrect.Working) (k0 w0 k1 w1 : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk0 : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k0)
    (hw0 : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w0)
    (hk1 : Compression.kValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 k1)
    (hw1 : Compression.wValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 w1) :
    Compression.pairE2 s j = Challenge.EvmProof.Word.ofUInt32
      (CompressionCorrect.round (CompressionCorrect.round x k0 w0) k1 w1).e := by
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  unfold Compression.pairE2
  rw [t11_eq s j x k0 w0 k1 w1 ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
      hk0 hw0 hk1 hw1,
    hc, Challenge.EvmProof.Word.mask32_add]
  simp only [CompressionCorrect.round]

private theorem hSlot_eq (i : Nat) (hi : i < 8) :
    Accessors.slotOffset 288 (UInt256.ofNat i) = 288 + i * 32 := by
  unfold Accessors.slotOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private def writeH (memory : ByteArray) (i : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) (288 + i * 32)

private theorem readH_writeH_same (memory : ByteArray) (i : Nat)
    (value : UInt256) :
    MachineState.readWord (writeH memory i value) (288 + i * 32) = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory (288 + i * 32) value

private theorem readH_writeH_ne (memory : ByteArray) (read write : Nat)
    (value : UInt256) (hne : read ≠ write) :
    MachineState.readWord (writeH memory write value) (288 + read * 32) =
      MachineState.readWord memory (288 + read * 32) := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  have hsize : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  by_cases hlt : read < write
  · left
    omega
  · right
    omega

private theorem hValue_eq_readH (s : State) (i : Nat) (hi : i < 8) :
    Compression.hValue s i = MachineState.readWord s.memory (288 + i * 32) := by
  unfold Compression.hValue
  rw [hSlot_eq i hi]

private theorem hValue_of_write_same (before after : State) (i : Nat)
    (hi : i < 8) (value : UInt256)
    (hmemory : after.memory = writeH before.memory i value) :
    Compression.hValue after i = value := by
  rw [hValue_eq_readH after i hi, hmemory, readH_writeH_same]

private theorem hValue_of_write_ne (before after : State) (read write : Nat)
    (hread : read < 8) (hne : read ≠ write) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.hValue after read = Compression.hValue before read := by
  rw [hValue_eq_readH after read hread, hmemory,
    readH_writeH_ne _ _ _ _ hne, ← hValue_eq_readH before read hread]

private theorem storedWord_memory (q : State) (i : Nat) (value : UInt256) :
    (Compression.storedWord q (288 + i * 32) value).memory =
      writeH q.memory i value := by
  rfl

theorem afterPair_represents (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat)
    (x : CompressionCorrect.Working) (k0 w0 k1 w1 : UInt32)
    (hx : CompressionCorrect.Represents s x)
    (hk0 : Compression.kValue s j = Challenge.EvmProof.Word.ofUInt32 k0)
    (hw0 : Compression.wValue s j = Challenge.EvmProof.Word.ofUInt32 w0)
    (hk1 : Compression.kValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 k1)
    (hw1 : Compression.wValue s (j + 1) = Challenge.EvmProof.Word.ofUInt32 w1) :
    CompressionCorrect.Represents
      (Compression.afterPair s msgOff returnDest rest j)
      (CompressionCorrect.round (CompressionCorrect.round x k0 w0) k1 w1) := by
  let q0 := Compression.afterPairT21 s msgOff returnDest rest j
  let q1 := Compression.storedWord q0 288 (Compression.pairA2 s j)
  let q2 := Compression.storedWord q1 320 (Compression.pairA1 s j)
  let q3 := Compression.storedWord q2 352 (Compression.hValue s 0)
  let q4 := Compression.storedWord q3 384 (Compression.hValue s 1)
  let q5 := Compression.storedWord q4 416 (Compression.pairE2 s j)
  let q6 := Compression.storedWord q5 448 (Compression.pairE1 s j)
  let q7 := Compression.storedWord q6 480 (Compression.hValue s 4)
  let q8 := Compression.storedWord q7 512 (Compression.hValue s 5)
  have hm1 : q1.memory = writeH q0.memory 0 (Compression.pairA2 s j) := by
    exact storedWord_memory q0 0 _
  have hm2 : q2.memory = writeH q1.memory 1 (Compression.pairA1 s j) := by
    exact storedWord_memory q1 1 _
  have hm3 : q3.memory = writeH q2.memory 2 (Compression.hValue s 0) := by
    exact storedWord_memory q2 2 _
  have hm4 : q4.memory = writeH q3.memory 3 (Compression.hValue s 1) := by
    exact storedWord_memory q3 3 _
  have hm5 : q5.memory = writeH q4.memory 4 (Compression.pairE2 s j) := by
    exact storedWord_memory q4 4 _
  have hm6 : q6.memory = writeH q5.memory 5 (Compression.pairE1 s j) := by
    exact storedWord_memory q5 5 _
  have hm7 : q7.memory = writeH q6.memory 6 (Compression.hValue s 4) := by
    exact storedWord_memory q6 6 _
  have hm8 : q8.memory = writeH q7.memory 7 (Compression.hValue s 5) := by
    exact storedWord_memory q7 7 _
  have p8 (i : Nat) (hi : i < 8) (hne : i ≠ 7) :
      Compression.hValue q8 i = Compression.hValue q7 i :=
    hValue_of_write_ne q7 q8 i 7 hi hne _ hm8
  have p7 (i : Nat) (hi : i < 8) (hne : i ≠ 6) :
      Compression.hValue q7 i = Compression.hValue q6 i :=
    hValue_of_write_ne q6 q7 i 6 hi hne _ hm7
  have p6 (i : Nat) (hi : i < 8) (hne : i ≠ 5) :
      Compression.hValue q6 i = Compression.hValue q5 i :=
    hValue_of_write_ne q5 q6 i 5 hi hne _ hm6
  have p5 (i : Nat) (hi : i < 8) (hne : i ≠ 4) :
      Compression.hValue q5 i = Compression.hValue q4 i :=
    hValue_of_write_ne q4 q5 i 4 hi hne _ hm5
  have p4 (i : Nat) (hi : i < 8) (hne : i ≠ 3) :
      Compression.hValue q4 i = Compression.hValue q3 i :=
    hValue_of_write_ne q3 q4 i 3 hi hne _ hm4
  have p3 (i : Nat) (hi : i < 8) (hne : i ≠ 2) :
      Compression.hValue q3 i = Compression.hValue q2 i :=
    hValue_of_write_ne q2 q3 i 2 hi hne _ hm3
  have p2 (i : Nat) (hi : i < 8) (hne : i ≠ 1) :
      Compression.hValue q2 i = Compression.hValue q1 i :=
    hValue_of_write_ne q1 q2 i 1 hi hne _ hm2
  have hs0 : Compression.hValue q8 0 = Compression.pairA2 s j := by
    rw [p8 0 (by decide) (by decide), p7 0 (by decide) (by decide),
      p6 0 (by decide) (by decide), p5 0 (by decide) (by decide),
      p4 0 (by decide) (by decide), p3 0 (by decide) (by decide),
      p2 0 (by decide) (by decide),
      hValue_of_write_same q0 q1 0 (by decide) _ hm1]
  have hs1 : Compression.hValue q8 1 = Compression.pairA1 s j := by
    rw [p8 1 (by decide) (by decide), p7 1 (by decide) (by decide),
      p6 1 (by decide) (by decide), p5 1 (by decide) (by decide),
      p4 1 (by decide) (by decide), p3 1 (by decide) (by decide),
      hValue_of_write_same q1 q2 1 (by decide) _ hm2]
  have hs2 : Compression.hValue q8 2 = Compression.hValue s 0 := by
    rw [p8 2 (by decide) (by decide), p7 2 (by decide) (by decide),
      p6 2 (by decide) (by decide), p5 2 (by decide) (by decide),
      p4 2 (by decide) (by decide),
      hValue_of_write_same q2 q3 2 (by decide) _ hm3]
  have hs3 : Compression.hValue q8 3 = Compression.hValue s 1 := by
    rw [p8 3 (by decide) (by decide), p7 3 (by decide) (by decide),
      p6 3 (by decide) (by decide), p5 3 (by decide) (by decide),
      hValue_of_write_same q3 q4 3 (by decide) _ hm4]
  have hs4 : Compression.hValue q8 4 = Compression.pairE2 s j := by
    rw [p8 4 (by decide) (by decide), p7 4 (by decide) (by decide),
      p6 4 (by decide) (by decide),
      hValue_of_write_same q4 q5 4 (by decide) _ hm5]
  have hs5 : Compression.hValue q8 5 = Compression.pairE1 s j := by
    rw [p8 5 (by decide) (by decide), p7 5 (by decide) (by decide),
      hValue_of_write_same q5 q6 5 (by decide) _ hm6]
  have hs6 : Compression.hValue q8 6 = Compression.hValue s 4 := by
    rw [p8 6 (by decide) (by decide),
      hValue_of_write_same q6 q7 6 (by decide) _ hm7]
  have hs7 : Compression.hValue q8 7 = Compression.hValue s 5 := by
    exact hValue_of_write_same q7 q8 7 (by decide) _ hm8
  have hq (i : Nat) :
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) i =
        Compression.hValue q8 i := by
    rfl
  rcases hx with ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
  constructor
  · rw [hq 0, hs0,
      pairA2_eq s j x k0 w0 k1 w1 ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
        hk0 hw0 hk1 hw1]
  constructor
  · rw [hq 1, hs1,
      pairA1_eq s j x k0 w0 ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ hk0 hw0]
    rfl
  constructor
  · rw [hq 2, hs2, ha]
    rfl
  constructor
  · rw [hq 3, hs3, hb]
    rfl
  constructor
  · rw [hq 4, hs4,
      pairE2_eq s j x k0 w0 k1 w1 ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
        hk0 hw0 hk1 hw1]
  constructor
  · rw [hq 5, hs5,
      pairE1_eq s j x k0 w0 ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ hk0 hw0]
    rfl
  constructor
  · rw [hq 6, hs6, he]
    rfl
  · rw [hq 7, hs7, hf]
    rfl

private theorem wValue_of_writeH (before after : State) (read write : Nat)
    (hread : read < 64) (hwrite : write < 8) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.wValue after read = Compression.wValue before read := by
  unfold Compression.wValue
  have hoff : Accessors.slotOffset 800 (UInt256.ofNat read) =
      800 + read * 32 := by
    unfold Accessors.slotOffset
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
      (by omega)]
    rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hmemory, hoff]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  omega

private theorem foldl_congr_on {α β : Type} (xs : List α)
    (left right : β → α → β) (init : β)
    (h : ∀ acc x, x ∈ xs → left acc x = right acc x) :
    xs.foldl left init = xs.foldl right init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h init x (by simp)]
      apply ih
      intro acc y hy
      exact h acc y (by simp [hy])

private theorem readBE32_eq_of_byte (left right : ByteArray)
    (leftOff rightOff : Nat)
    (hbyte : ∀ i < 4,
      (if h : leftOff + i < left.size then left[leftOff + i].toUInt32 else 0) =
        (if h : rightOff + i < right.size then
          right[rightOff + i].toUInt32 else 0)) :
    Sha256.readBE32 left leftOff = Sha256.readBE32 right rightOff := by
  unfold Sha256.readBE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl]
  simp only [Id.run_pure]
  apply foldl_congr_on
  intro w i hi
  have hlt : i < 4 := by simpa using hi
  rw [hbyte i hlt]

private theorem kOffset_eq (j : Nat) (hj : j < 64) :
    (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
      UInt256.ofNat 32).toNat = 32 + 4 * j := by
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem readBE32_writeH (memory : ByteArray) (j write : Nat)
    (value : UInt256) (hj : j < 64) :
    Sha256.readBE32 (writeH memory write value) (32 + 4 * j) =
      Sha256.readBE32 memory (32 + 4 * j) := by
  apply readBE32_eq_of_byte
  intro i hi
  let idx := 32 + 4 * j + i
  have hidx : idx < 288 + write * 32 := by
    dsimp only [idx]
    omega
  have hbytes : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  by_cases hm : idx < memory.size
  · have hw : idx < (writeH memory write value).size := by
      unfold writeH
      rw [MachineState.writeBytes_size, if_neg (by simp [hbytes]), hbytes]
      omega
    rw [dif_pos hw, dif_pos hm]
    apply congrArg UInt8.toUInt32
    have hg := MachineState.writeBytes_getElem?_getD memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (288 + write * 32) idx
    rw [if_neg (by simp only [hbytes]; omega)] at hg
    change (writeH memory write value)[idx]?.getD 0 = memory[idx]?.getD 0 at hg
    rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hw,
      Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hm] at hg
    exact hg
  · by_cases hw : idx < (writeH memory write value).size
    · rw [dif_pos hw, dif_neg hm]
      have hg := MachineState.writeBytes_getElem?_getD memory
        (Data.Bytes.natToBytesPadded value.toNat 32) (288 + write * 32) idx
      rw [if_neg (by simp only [hbytes]; omega)] at hg
      change (writeH memory write value)[idx]?.getD 0 = memory[idx]?.getD 0 at hg
      rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hw,
        Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _
          (by omega)] at hg
      simpa using congrArg UInt8.toUInt32 hg
    · rw [dif_neg hw, dif_neg hm]

private theorem kValue_of_writeH (before after : State) (read write : Nat)
    (hread : read < 64) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.kValue after read = Compression.kValue before read := by
  unfold Compression.kValue
  rw [kOffset_eq read hread]
  dsimp only
  rw [hmemory, PaddedBlockBridge.shiftRight_readWord_224,
    PaddedBlockBridge.shiftRight_readWord_224,
    readBE32_writeH before.memory read write value hread]

/-- A pair mutates only the eight working-state slots. -/
theorem afterPair_preserves_inputs (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j read : Nat) (hread : read < 64) :
    Compression.kValue (Compression.afterPair s msgOff returnDest rest j) read =
        Compression.kValue s read ∧
      Compression.wValue (Compression.afterPair s msgOff returnDest rest j) read =
        Compression.wValue s read := by
  let q0 := Compression.afterPairT21 s msgOff returnDest rest j
  let q1 := Compression.storedWord q0 288 (Compression.pairA2 s j)
  let q2 := Compression.storedWord q1 320 (Compression.pairA1 s j)
  let q3 := Compression.storedWord q2 352 (Compression.hValue s 0)
  let q4 := Compression.storedWord q3 384 (Compression.hValue s 1)
  let q5 := Compression.storedWord q4 416 (Compression.pairE2 s j)
  let q6 := Compression.storedWord q5 448 (Compression.pairE1 s j)
  let q7 := Compression.storedWord q6 480 (Compression.hValue s 4)
  let q8 := Compression.storedWord q7 512 (Compression.hValue s 5)
  have hm1 : q1.memory = writeH q0.memory 0 (Compression.pairA2 s j) :=
    storedWord_memory q0 0 _
  have hm2 : q2.memory = writeH q1.memory 1 (Compression.pairA1 s j) :=
    storedWord_memory q1 1 _
  have hm3 : q3.memory = writeH q2.memory 2 (Compression.hValue s 0) :=
    storedWord_memory q2 2 _
  have hm4 : q4.memory = writeH q3.memory 3 (Compression.hValue s 1) :=
    storedWord_memory q3 3 _
  have hm5 : q5.memory = writeH q4.memory 4 (Compression.pairE2 s j) :=
    storedWord_memory q4 4 _
  have hm6 : q6.memory = writeH q5.memory 5 (Compression.pairE1 s j) :=
    storedWord_memory q5 5 _
  have hm7 : q7.memory = writeH q6.memory 6 (Compression.hValue s 4) :=
    storedWord_memory q6 6 _
  have hm8 : q8.memory = writeH q7.memory 7 (Compression.hValue s 5) :=
    storedWord_memory q7 7 _
  constructor
  · change Compression.kValue q8 read = Compression.kValue s read
    rw [kValue_of_writeH q7 q8 read 7 hread _ hm8,
      kValue_of_writeH q6 q7 read 6 hread _ hm7,
      kValue_of_writeH q5 q6 read 5 hread _ hm6,
      kValue_of_writeH q4 q5 read 4 hread _ hm5,
      kValue_of_writeH q3 q4 read 3 hread _ hm4,
      kValue_of_writeH q2 q3 read 2 hread _ hm3,
      kValue_of_writeH q1 q2 read 1 hread _ hm2,
      kValue_of_writeH q0 q1 read 0 hread _ hm1]
    rfl
  · change Compression.wValue q8 read = Compression.wValue s read
    rw [wValue_of_writeH q7 q8 read 7 hread (by decide) _ hm8,
      wValue_of_writeH q6 q7 read 6 hread (by decide) _ hm7,
      wValue_of_writeH q5 q6 read 5 hread (by decide) _ hm6,
      wValue_of_writeH q4 q5 read 4 hread (by decide) _ hm5,
      wValue_of_writeH q3 q4 read 3 hread (by decide) _ hm4,
      wValue_of_writeH q2 q3 read 2 hread (by decide) _ hm3,
      wValue_of_writeH q1 q2 read 1 hread (by decide) _ hm2,
      wValue_of_writeH q0 q1 read 0 hread (by decide) _ hm1]
    rfl

private theorem savedOffset_eq (i : Nat) (hi : i < 8) :
    Compression.savedOffset i = 544 + i * 32 := by
  unfold Compression.savedOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem savedValue_of_writeH (before after : State) (read write : Nat)
    (hread : read < 8) (hwrite : write < 8) (value : UInt256)
    (hmemory : after.memory = writeH before.memory write value) :
    Compression.savedValue after read = Compression.savedValue before read := by
  unfold Compression.savedValue
  rw [hmemory, savedOffset_eq read hread]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  right
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  omega

theorem afterPair_preserves_saved (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j read : Nat) (hread : read < 8) :
    Compression.savedValue (Compression.afterPair s msgOff returnDest rest j) read =
      Compression.savedValue s read := by
  let q0 := Compression.afterPairT21 s msgOff returnDest rest j
  let q1 := Compression.storedWord q0 288 (Compression.pairA2 s j)
  let q2 := Compression.storedWord q1 320 (Compression.pairA1 s j)
  let q3 := Compression.storedWord q2 352 (Compression.hValue s 0)
  let q4 := Compression.storedWord q3 384 (Compression.hValue s 1)
  let q5 := Compression.storedWord q4 416 (Compression.pairE2 s j)
  let q6 := Compression.storedWord q5 448 (Compression.pairE1 s j)
  let q7 := Compression.storedWord q6 480 (Compression.hValue s 4)
  let q8 := Compression.storedWord q7 512 (Compression.hValue s 5)
  have hm1 : q1.memory = writeH q0.memory 0 (Compression.pairA2 s j) :=
    storedWord_memory q0 0 _
  have hm2 : q2.memory = writeH q1.memory 1 (Compression.pairA1 s j) :=
    storedWord_memory q1 1 _
  have hm3 : q3.memory = writeH q2.memory 2 (Compression.hValue s 0) :=
    storedWord_memory q2 2 _
  have hm4 : q4.memory = writeH q3.memory 3 (Compression.hValue s 1) :=
    storedWord_memory q3 3 _
  have hm5 : q5.memory = writeH q4.memory 4 (Compression.pairE2 s j) :=
    storedWord_memory q4 4 _
  have hm6 : q6.memory = writeH q5.memory 5 (Compression.pairE1 s j) :=
    storedWord_memory q5 5 _
  have hm7 : q7.memory = writeH q6.memory 6 (Compression.hValue s 4) :=
    storedWord_memory q6 6 _
  have hm8 : q8.memory = writeH q7.memory 7 (Compression.hValue s 5) :=
    storedWord_memory q7 7 _
  change Compression.savedValue q8 read = Compression.savedValue s read
  rw [savedValue_of_writeH q7 q8 read 7 hread (by decide) _ hm8,
    savedValue_of_writeH q6 q7 read 6 hread (by decide) _ hm7,
    savedValue_of_writeH q5 q6 read 5 hread (by decide) _ hm6,
    savedValue_of_writeH q4 q5 read 4 hread (by decide) _ hm5,
    savedValue_of_writeH q3 q4 read 3 hread (by decide) _ hm4,
    savedValue_of_writeH q2 q3 read 2 hread (by decide) _ hm3,
    savedValue_of_writeH q1 q2 read 1 hread (by decide) _ hm2,
    savedValue_of_writeH q0 q1 read 0 hread (by decide) _ hm1]
  rfl

theorem pairLoopState_inputs (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n read : Nat) (hread : read < 64) :
    Compression.kValue
        (ResidentBridge.ghostLoopState s msgOff returnDest rest n) read =
        Compression.kValue s read ∧
      Compression.wValue
        (ResidentBridge.ghostLoopState s msgOff returnDest rest n) read =
        Compression.wValue s read := by
  induction n with
  | zero => constructor <;> rfl
  | succ n ih =>
      rw [ResidentBridge.ghostLoopState]
      have hp := afterPair_preserves_inputs
        (ResidentBridge.ghostLoopState s msgOff returnDest rest n)
        msgOff returnDest rest (2 * n) read hread
      exact ⟨hp.1.trans ih.1, hp.2.trans ih.2⟩

theorem pairLoopState_saved (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (n read : Nat) (hread : read < 8) :
    Compression.savedValue
        (ResidentBridge.ghostLoopState s msgOff returnDest rest n) read =
      Compression.savedValue s read := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ResidentBridge.ghostLoopState]
      exact (afterPair_preserves_saved
        (ResidentBridge.ghostLoopState s msgOff returnDest rest n)
        msgOff returnDest rest (2 * n) read hread).trans ih

def PairInputsCorrect (s : State) (padded : ByteArray) (blockOff : Nat) : Prop :=
  ∀ n, n < 64 →
    Compression.kValue s n =
        Challenge.EvmProof.Word.ofUInt32 Sha256.K[n]! ∧
      Compression.wValue s n = Challenge.EvmProof.Word.ofUInt32
        (ScheduleCorrect.scheduleWord padded blockOff n)

theorem pairLoopState_represents (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (padded : ByteArray) (blockOff : Nat)
    (initial : CompressionCorrect.Working)
    (hinitial : CompressionCorrect.Represents s initial)
    (hinputs : PairInputsCorrect s padded blockOff) :
    ∀ n, n ≤ 32 →
      CompressionCorrect.Represents
        (ResidentBridge.ghostLoopState s msgOff returnDest rest n)
        (CompressionCorrect.rounds initial padded blockOff (2 * n)) := by
  intro n hn
  induction n with
  | zero =>
      simpa [ResidentBridge.ghostLoopState, Compression.pairAt,
        CompressionCorrect.Represents, Compression.hValue,
        CompressionCorrect.rounds] using hinitial
  | succ n ih =>
      let q := ResidentBridge.ghostLoopState s msgOff returnDest rest n
      have hprev : CompressionCorrect.Represents q
          (CompressionCorrect.rounds initial padded blockOff (2 * n)) :=
        ih (by omega)
      have hp0 := pairLoopState_inputs s msgOff returnDest rest n (2 * n)
        (by omega)
      have hp1 := pairLoopState_inputs s msgOff returnDest rest n (2 * n + 1)
        (by omega)
      have hstep := afterPair_represents q msgOff returnDest rest (2 * n)
        (CompressionCorrect.rounds initial padded blockOff (2 * n))
        Sha256.K[2 * n]! (ScheduleCorrect.scheduleWord padded blockOff (2 * n))
        Sha256.K[2 * n + 1]!
        (ScheduleCorrect.scheduleWord padded blockOff (2 * n + 1)) hprev
        (hp0.1.trans (hinputs (2 * n) (by omega)).1)
        (hp0.2.trans (hinputs (2 * n) (by omega)).2)
        (hp1.1.trans (hinputs (2 * n + 1) (by omega)).1)
        (hp1.2.trans (hinputs (2 * n + 1) (by omega)).2)
      rw [ResidentBridge.ghostLoopState]
      have hr : CompressionCorrect.rounds initial padded blockOff (2 * (n + 1)) =
          CompressionCorrect.round
            (CompressionCorrect.round
              (CompressionCorrect.rounds initial padded blockOff (2 * n))
              Sha256.K[2 * n]!
              (ScheduleCorrect.scheduleWord padded blockOff (2 * n)))
            Sha256.K[2 * n + 1]!
            (ScheduleCorrect.scheduleWord padded blockOff (2 * n + 1)) := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          CompressionCorrect.rounds,
          show 2 * n + 1 = 2 * n + 1 by rfl,
          CompressionCorrect.rounds]
      rw [hr]
      exact hstep

end Challenge.Sha256.Submission.Proofs.Bytecode.PairCorrectTest

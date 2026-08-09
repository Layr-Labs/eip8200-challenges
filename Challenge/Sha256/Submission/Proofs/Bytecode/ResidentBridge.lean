import Challenge.Sha256.Submission.Proofs.Bytecode.ResidentComposition

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.ResidentBridge

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

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

theorem afterPair_hValues (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) :
    Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 0 =
        Compression.pairA2 s j ∧
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 1 =
        Compression.pairA1 s j ∧
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 2 =
        Compression.hValue s 0 ∧
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 3 =
        Compression.hValue s 1 ∧
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 4 =
        Compression.pairE2 s j ∧
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 5 =
        Compression.pairE1 s j ∧
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 6 =
        Compression.hValue s 4 ∧
      Compression.hValue (Compression.afterPair s msgOff returnDest rest j) 7 =
        Compression.hValue s 5 := by
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
        Compression.hValue q8 i := by rfl
  exact ⟨(hq 0).trans hs0, (hq 1).trans hs1, (hq 2).trans hs2,
    (hq 3).trans hs3, (hq 4).trans hs4, (hq 5).trans hs5,
    (hq 6).trans hs6, (hq 7).trans hs7⟩

theorem residentAfterPair_eq_next (base ghost : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (j : Nat) :
    Compression.residentAfterPair base ghost msgOff returnDest rest j =
      Compression.residentAt
        (Compression.residentAfterPair base ghost msgOff returnDest rest j)
        (Compression.afterPair ghost msgOff returnDest rest j)
        msgOff returnDest rest (j + 2) := by
  rcases afterPair_hValues ghost msgOff returnDest rest j with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  simp [Compression.residentAt, Compression.residentAfterPair,
    h0, h1, h2, h3, h4, h5, h6, h7]

def ghostLoopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => Compression.pairAt s msgOff returnDest rest 0
  | n + 1 => Compression.afterPair
      (ghostLoopState s msgOff returnDest rest n)
      msgOff returnDest rest (2 * n)

end Challenge.Sha256.Submission.Proofs.Bytecode.ResidentBridge

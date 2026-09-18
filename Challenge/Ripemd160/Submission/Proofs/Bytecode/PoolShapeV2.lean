import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShape

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Byte-source model of the v2m builder (the ACTUAL image)

`PoolShape.resultMemory true` stays the clean reference image.  The artifact's builder now
stages the low word at `46` and `28`, copies sixteen bytes `28 → 10` with a third `MCOPY`, and
masks only words 4, 5, 6, 7 and 11; this file describes that image byte for byte with the same
`Source` terms so the certificates can be checked by `decide` against the reference.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShapeV2
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory PoolShape

theorem scratchV2_getD (memory : ByteArray) (low high : UInt256) (a : Nat) :
    (Pair13Endian.scratchV2 memory low high)[a]?.getD 0 =
      if 616 ≤ a ∧ a < 648 then (Data.Bytes.natToBytesPadded low.toNat 32)[a - 616]?.getD 0
      else if 28 ≤ a ∧ a < 60 then (Data.Bytes.natToBytesPadded high.toNat 32)[a - 28]?.getD 0
      else memory[a]?.getD 0 := by
  rw [Pair13Endian.scratchV2, Shared32Scratch.writeWord_getD, Shared32Scratch.writeWord_getD]

theorem copyV2_getD (m : ByteArray) (src dst a : Nat) :
    (Pair13PoolRaw.copyV2 m src dst)[a]?.getD 0 =
      if dst ≤ a ∧ a < dst + 16 then m[a - dst + src]?.getD 0 else m[a]?.getD 0 := by
  rw [Pair13PoolRaw.copyV2, MachineState.writeBytes_getElem?_getD, Memory.readPadded_size]
  by_cases ha : dst ≤ a ∧ a < dst + 16
  · rw [if_pos ha, if_pos (by omega), Memory.readPadded_getElem?_getD,
      if_pos (by omega : a - dst < 16), show src + (a - dst) = a - dst + src by omega]
  · rw [if_neg ha, if_neg (by omega)]

/-- Every copy source lies outside every earlier copy's destination, so the four copies
compose to a single address map. -/
def copiedAddressV2 (a : Nat) : Nat :=
  if 650 ≤ a ∧ a < 666 then a-18
  else if 598 ≤ a ∧ a < 614 then a+18
  else if 62 ≤ a ∧ a < 78 then a-18
  else if 10 ≤ a ∧ a < 26 then a+18 else a

theorem copiedV2_getD (m : ByteArray) (a : Nat) :
    (Pair13PoolRaw.copiedV2 m)[a]?.getD 0 = m[copiedAddressV2 a]?.getD 0 := by
  simp only [Pair13PoolRaw.copiedV2, copyV2_getD, copiedAddressV2]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

def scratchSourceV2 (a : Nat) : Source :=
  if 616 ≤ a ∧ a < 648 then .low (a-616)
  else if 28 ≤ a ∧ a < 60 then .high (a-28)
  else incoming a

def fanSourceV2 (a : Nat) : Source := scratchSourceV2 (copiedAddressV2 a)

/-- The actual fan image: four copies over the two single stores. -/
def fanMemoryV2 (memory : ByteArray) (low high : UInt256) : ByteArray :=
  Pair13PoolRaw.copiedV2 (Pair13Endian.scratchV2 memory low high)

theorem scratchV2_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (a : Nat) :
    (Pair13Endian.scratchV2 m lo hi)[a]?.getD 0 = (scratchSourceV2 a).eval m lo hi := by
  rw [scratchV2_getD]
  unfold scratchSourceV2
  split_ifs <;> simp (discharger := omega) only [Source.eval, PoolByte.encoded, eval_incoming m lo hi hc]

theorem fanV2_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (a : Nat) :
    (fanMemoryV2 m lo hi)[a]?.getD 0 = (fanSourceV2 a).eval m lo hi := by
  rw [fanMemoryV2, copiedV2_getD, fanSourceV2]
  exact scratchV2_shape m lo hi hc _

def loadSourceV2 (i j : Nat) : Source := fanSourceV2 (Pair13PoolRaw.poolAddrV2 i+j)

/-- Only words 6 and 11 are masked; everything else is stored raw. -/
def poolSourceV2 (i j : Nat) : Source :=
  if decide (i ∈ [6,11]) then maskSource j (loadSourceV2 i j) else loadSourceV2 i j

theorem poolV2_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m)
    (i j : Nat) (hi16 : i < 16) (hj : j < 32) :
    PoolByte.byte (Pair13PoolRaw.poolWordV2 (fanMemoryV2 m lo hi) i) j =
      (poolSourceV2 i j).eval m lo hi := by
  have hr (i j : Nat) (hj : j < 32) :
      PoolByte.byte (Pair13PoolRaw.rawLoadV2 (fanMemoryV2 m lo hi) i) j =
        (loadSourceV2 i j).eval m lo hi := by
    rw [Pair13PoolRaw.rawLoadV2, PoolByte.read _ _ _ hj, fanV2_shape m lo hi hc]
    rfl
  interval_cases i <;> interval_cases j <;>
    simp (config := { maxSteps := 200000 }) (discharger := omega) [poolSourceV2, Pair13PoolRaw.poolWordV2,
      byte_mask, hr, maskSource, laneByte, Source.eval]

def resultSourceV2 : Nat → Source := storeSources poolSourceV2 fanSourceV2 writes

def resultMemoryV2 (m : ByteArray) (lo hi : UInt256) : ByteArray :=
  PoolRawWriter.writerMemory (fanMemoryV2 m lo hi) (Pair13PoolRaw.poolWordV2 (fanMemoryV2 m lo hi))

theorem resultV2_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (a : Nat) :
    (resultMemoryV2 m lo hi)[a]?.getD 0 = (resultSourceV2 a).eval m lo hi := by
  rw [resultMemoryV2, PoolRawWriter.writerMemory, rawWrites_eq]
  have hindices : ∀ x ∈ writes, x.2 < 16 := by decide
  exact writeChain_shape _ m lo hi _ _ _ writes (fanV2_shape m lo hi hc)
    (fun x hx j hj => poolV2_shape m lo hi hc x.2 j (hindices x hx) hj) a

#print axioms poolV2_shape
#print axioms resultV2_shape
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShapeV2

import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShape

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Byte-source model of the mask1 builder (the ACTUAL image)

`PoolShape.resultMemory true` stays the clean reference image.  The artifact's builder now
stores the high word once at `162` and the low word once at `252`, fans them out with four
sixteen-byte `MCOPY`s (`162 → 144`, `178 → 196`, `252 → 234`, `268 → 286`) and masks only
word 11; this file describes that image byte for byte with the same
`Source` terms so the certificates can be checked by `decide` against the reference.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShapeV2
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory PoolShape

/-- The actual image's OWN zero set: bytes the next block's raw loads carry into a table gap
byte (`18*j+k`, `14 ≤ k < 18`) that a certificate needs to be zero.  Unlike the reference's
`PoolShape.zeroAddresses` it contains nothing below byte 50: the first memory word may hold
anything, which is what lets the layout drop the mask on schedule word 6. -/
def zeroAddressesV2 : List Nat := [50,51,52,53,160,161,194,195,250,251,284,285,320,321,322,323,356,357,358,359,392,393,394,395,446,447,448,449,590,591,592,593,716,717,718,719,788,789,790,791,824,825,826,827,932,933,934,935,968,969,970,971,1004,1005,1006,1007,1040,1041,1042,1043]

theorem zeroAddressesV2_band : ∀ a ∈ zeroAddressesV2, 36 ≤ a ∧ a < 1056 ∧ 14 ≤ a % 18 := by
  decide

def ClearV2 (memory : ByteArray) : Prop :=
  ∀ a, a ∈ zeroAddressesV2 → memory[a]?.getD 0 = 0

def incomingV2 (a : Nat) : Source := if a ∈ zeroAddressesV2 then .zero else .memory a

theorem eval_incomingV2 (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (a : Nat) :
    m[a]?.getD 0 = (incomingV2 a).eval m lo hi := by
  unfold incomingV2
  split
  · exact hc a ‹_›
  · rfl

/-- A term with no `.memory` leaf evaluates the same over every memory. -/
def Source.memFree : Source → Bool
  | .zero => true
  | .memory _ => false
  | .low _ => true
  | .high _ => true
  | .join a b => Source.memFree a && Source.memFree b

theorem eval_memFree (m m' : ByteArray) (lo hi : UInt256) (s : Source)
    (h : Source.memFree s = true) : s.eval m lo hi = s.eval m' lo hi := by
  induction s with
  | zero => rfl
  | memory a => simp [Source.memFree] at h
  | low i => rfl
  | high i => rfl
  | join a b iha ihb =>
    simp only [Source.memFree, Bool.and_eq_true] at h
    simp only [Source.eval, iha h.1, ihb h.2]

theorem scratchV2_getD (memory : ByteArray) (low high : UInt256) (a : Nat) :
    (Pair13Endian.scratchV2 memory low high)[a]?.getD 0 =
      if 252 ≤ a ∧ a < 284 then (Data.Bytes.natToBytesPadded low.toNat 32)[a - 252]?.getD 0
      else if 162 ≤ a ∧ a < 194 then (Data.Bytes.natToBytesPadded high.toNat 32)[a - 162]?.getD 0
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
  if 286 ≤ a ∧ a < 302 then a-18
  else if 234 ≤ a ∧ a < 250 then a+18
  else if 196 ≤ a ∧ a < 212 then a-18
  else if 144 ≤ a ∧ a < 160 then a+18 else a

theorem copiedV2_getD (m : ByteArray) (a : Nat) :
    (Pair13PoolRaw.copiedV2 m)[a]?.getD 0 = m[copiedAddressV2 a]?.getD 0 := by
  simp only [Pair13PoolRaw.copiedV2, copyV2_getD, copiedAddressV2]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

def scratchSourceV2 (a : Nat) : Source :=
  if 252 ≤ a ∧ a < 284 then .low (a-252)
  else if 162 ≤ a ∧ a < 194 then .high (a-162)
  else incomingV2 a

def fanSourceV2 (a : Nat) : Source := scratchSourceV2 (copiedAddressV2 a)

/-- The actual fan image: four copies over the two single stores. -/
def fanMemoryV2 (memory : ByteArray) (low high : UInt256) : ByteArray :=
  Pair13PoolRaw.copiedV2 (Pair13Endian.scratchV2 memory low high)

theorem scratchV2_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (a : Nat) :
    (Pair13Endian.scratchV2 m lo hi)[a]?.getD 0 = (scratchSourceV2 a).eval m lo hi := by
  rw [scratchV2_getD]
  unfold scratchSourceV2
  split_ifs <;> simp (discharger := omega) only [Source.eval, PoolByte.encoded, eval_incomingV2 m lo hi hc]

theorem fanV2_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (a : Nat) :
    (fanMemoryV2 m lo hi)[a]?.getD 0 = (fanSourceV2 a).eval m lo hi := by
  rw [fanMemoryV2, copiedV2_getD, fanSourceV2]
  exact scratchV2_shape m lo hi hc _

def loadSourceV2 (i j : Nat) : Source := fanSourceV2 (Pair13PoolRaw.poolAddrV2 i+j)

/-- All pool words are stored raw. The terminal round restores its lane mask at the load site. -/
def poolSourceV2 (i j : Nat) : Source := loadSourceV2 i j

theorem poolV2_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m)
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

/-- The builder ends with `PUSH0 PUSH2 0x262 MSTORE8`: byte 610 (byte 16 of the terminal
round's slot 594) is cleared after the 45 table stores, so the terminal round can read its
message word unmasked (bits 120..143 of the slot are then provably zero). -/
def clearTerminal (m : ByteArray) : ByteArray :=
  MachineState.writeBytes m (ByteArray.mk #[(0 : UInt8)]) 610

theorem clearTerminal_getD (m : ByteArray) (a : Nat) :
    (clearTerminal m)[a]?.getD 0 = if a = 610 then 0 else m[a]?.getD 0 := by
  rw [clearTerminal, MachineState.writeBytes_getElem?_getD]
  have hs : (ByteArray.mk #[(0 : UInt8)]).size = 1 := rfl
  rw [hs]
  by_cases ha : a = 610
  · subst ha
    rw [if_pos (by omega), if_pos rfl]
    rfl
  · rw [if_neg (by omega), if_neg ha]

def resultSourceV2 (a : Nat) : Source :=
  if a = 610 then .zero else storeSources poolSourceV2 fanSourceV2 writes a

def resultMemoryV2 (m : ByteArray) (lo hi : UInt256) : ByteArray :=
  clearTerminal
    (PoolRawWriter.writerMemory (fanMemoryV2 m lo hi) (Pair13PoolRaw.poolWordV2 (fanMemoryV2 m lo hi)))

theorem resultV2_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (a : Nat) :
    (resultMemoryV2 m lo hi)[a]?.getD 0 = (resultSourceV2 a).eval m lo hi := by
  rw [resultMemoryV2, clearTerminal_getD, resultSourceV2]
  by_cases ha : a = 610
  · rw [if_pos ha, if_pos ha]
    rfl
  rw [if_neg ha, if_neg ha, PoolRawWriter.writerMemory, rawWrites_eq]
  have hindices : ∀ x ∈ writes, x.2 < 16 := by decide
  exact writeChain_shape _ m lo hi _ _ _ writes (fanV2_shape m lo hi hc)
    (fun x hx j hj => poolV2_shape m lo hi hc x.2 j (hindices x hx) hj) a

#print axioms poolV2_shape
#print axioms resultV2_shape
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShapeV2

import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolFacts

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PoolShape PoolShapeV2

theorem clear_low (m : ByteArray) (hc : Clear m) :
    (MachineState.readWord m 0).toNat % 2^144 < 2^32 := by
  apply PoolFacts.low_clear
  intro k hl hu
  apply hc
  rw [zeroAddresses, List.mem_cons]
  right
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl ⟨k-14, by omega, by omega⟩)

theorem clear_gap (m : ByteArray) (hc : Clear m) : PairStoreGap.GapClear m := by
  intro j hj k hl hu
  apply hc
  rw [zeroAddresses, List.mem_cons]
  right
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inr ⟨j,hj,k-14,by omega,by omega⟩

theorem clear_of_zero (m : ByteArray) (hz : ∀ a, a < 1056 → m[a]?.getD 0 = 0) : Clear m :=
  fun a ha => hz a (PoolCertificates.zeroAddresses_bound a ha)

theorem clearV2_of_zero (m : ByteArray) (hz : ∀ a, a < 1056 → m[a]?.getD 0 = 0) : ClearV2 m :=
  fun a ha => hz a (zeroAddressesV2_band a ha).2.1

/-! ### The zeroed-memory reference

The clean reference image assumes `PoolShape.Clear` of its base (bytes 0 and 14..27 zero,
the thirteen pairs' gap bytes zero, ...), which the actual image no longer maintains: with
word 6 raw, table slot 0 carries whatever the raw load drags along.  The reference is
therefore always evaluated over `sanitize m` -- the incoming memory with everything below the
message (byte 1056) cleared -- and the certificates prove its lane terms read no memory. -/

def sanitize (m : ByteArray) : ByteArray :=
  MachineState.writeBytes m (ByteArray.mk (Array.replicate 1056 (0 : UInt8))) 0

theorem sanitize_getD (m : ByteArray) (a : Nat) :
    (sanitize m)[a]?.getD 0 = if a < 1056 then 0 else m[a]?.getD 0 := by
  rw [sanitize, MachineState.writeBytes_getElem?_getD]
  have hs : (ByteArray.mk (Array.replicate 1056 (0 : UInt8))).size = 1056 := rfl
  rw [hs]
  by_cases ha : a < 1056
  · rw [if_pos (by omega), if_pos ha]
    change (Array.replicate 1056 (0 : UInt8))[a - 0]?.getD 0 = 0
    rw [getElem?_pos _ _ (by simpa using ha)]
    simp
  · rw [if_neg (by omega), if_neg ha]

theorem sanitize_zero (m : ByteArray) (a : Nat) (ha : a < 1056) : (sanitize m)[a]?.getD 0 = 0 := by
  rw [sanitize_getD, if_pos ha]

theorem sanitize_clear (m : ByteArray) : Clear (sanitize m) :=
  clear_of_zero _ (sanitize_zero m)

theorem read_sanitize (m : ByteArray) (a : Nat) (ha : 1056 ≤ a) :
    MachineState.readWord (sanitize m) a = MachineState.readWord m a := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact StaggerTableMemory.bytesToNatPadded_congrOffset _ _ _ _ _
    (fun i _ => by rw [sanitize_getD, if_neg (by omega)])

theorem extracted_sanitize (m : ByteArray) (p : Nat) (hp : 1056 ≤ p) :
    PairedScheduleData.extractedWord (sanitize m) p = PairedScheduleData.extractedWord m p := by
  funext i
  unfold PairedScheduleData.extractedWord
  rw [read_sanitize m _ (by omega)]

theorem writeChain_outside (m : ByteArray) (words : Nat → UInt256) (ws : List (Nat × Nat))
    (a : Nat) (ha : ∀ x ∈ ws, x.1+32 ≤ a) :
    (Pair13WriterRaw.writeChain m (ws.map (fun x => (x.1,words x.2))))[a]?.getD 0 = m[a]?.getD 0 := by
  induction ws generalizing m with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, Pair13WriterRaw.writeChain_cons]
    rw [ih _ (fun y hy => ha y (List.mem_cons_of_mem _ hy)), Shared32Scratch.writeWord_getD,
      if_neg (by have := ha x (List.mem_cons_self ..); omega)]

theorem result_outside (clean : Bool) (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    (resultMemory clean m lo hi)[a]?.getD 0 = m[a]?.getD 0 := by
  rw [resultMemory, PoolRawWriter.writerMemory, rawWrites_eq,
    writeChain_outside _ _ _ _ (fun x hx => (PoolCertificates.writes_bound x hx).1.trans ha),
    Shared32Scratch.fan_getD_high _ _ _ _ (by omega)]

theorem read_result_outside (clean : Bool) (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    MachineState.readWord (resultMemory clean m lo hi) a = MachineState.readWord m a := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact StaggerTableMemory.bytesToNatPadded_congrOffset _ _ _ _ _
    (fun i _ => result_outside clean m lo hi (a+i) (by omega))

/-- Above the copied block the actual fan image is the incoming memory verbatim. -/
theorem fanV2_getD_high (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    (fanMemoryV2 m lo hi)[a]?.getD 0 = m[a]?.getD 0 := by
  rw [fanMemoryV2, PoolShapeV2.copiedV2_getD, PoolShapeV2.copiedAddressV2,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    PoolShapeV2.scratchV2_getD, if_neg (by omega), if_neg (by omega)]

theorem resultV2_outside (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    (resultMemoryV2 m lo hi)[a]?.getD 0 = m[a]?.getD 0 := by
  rw [resultMemoryV2, clearTerminal_getD, if_neg (by omega), PoolRawWriter.writerMemory, rawWrites_eq,
    writeChain_outside _ _ _ _ (fun x hx => (PoolCertificates.writes_bound x hx).1.trans ha),
    fanV2_getD_high _ _ _ _ (by omega)]

theorem read_resultV2_outside (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    MachineState.readWord (resultMemoryV2 m lo hi) a = MachineState.readWord m a := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact StaggerTableMemory.bytesToNatPadded_congrOffset _ _ _ _ _
    (fun i _ => resultV2_outside m lo hi (a+i) (by omega))

/-! ### Transporting `Ready` across the four exposed gap bytes

The 45-write writer drops the store at 36, so bytes [50,54) keep whatever the caller left.
Of everything `Ready` reads, exactly one field touches them: `Safe.slack` at round 25, the
only round whose message word (slot 2, address 36) spans the gap.  Both lanes of every slot
and the `scalar` field lie outside it, and `LegacyMessageWord`'s junk `jl * 2 ^ 32 +
jr * 2 ^ 176` cannot represent bits [112,144), so round 25 is forced onto the `Safe`
disjunct rather than choosing it. -/

private theorem lanes_gap (W T : ByteArray) (j : Nat)
    (hb : ∀ i, i < 50 ∨ 54 ≤ i → W[i]?.getD 0 = T[i]?.getD 0) :
    (MachineState.readWord W (18*j)).toNat % 2^32
        = (MachineState.readWord T (18*j)).toNat % 2^32 ∧
      (MachineState.readWord W (18*j)).toNat / 2^144 % 2^32
        = (MachineState.readWord T (18*j)).toNat / 2^144 % 2^32 := by
  constructor
  · rw [PoolFacts.low_value, PoolFacts.low_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    exact hb _ (by omega)
  · rw [PoolFacts.high_value, PoolFacts.high_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    exact hb _ (by omega)

private theorem word_gap (W T : ByteArray) (p : Nat) (hp : p ≤ 1 ∨ 3 ≤ p)
    (hb : ∀ i, i < 50 ∨ 54 ≤ i → W[i]?.getD 0 = T[i]?.getD 0) :
    MachineState.readWord W (18*p) = MachineState.readWord T (18*p) := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro k hk
  exact hb _ (by omega)

theorem ready_of_gap (W T : ByteArray) (words : Nat → UInt32)
    (hb : ∀ i, i < 50 ∨ 54 ≤ i → W[i]?.getD 0 = T[i]?.getD 0)
    (hz : W[54]?.getD 0 = 0)
    (h : StaggerMessage.Ready T words) : StaggerMessage.Ready W words := by
  constructor
  · intro i hi77
    by_cases hp : StaggerTableLayout.pairIndices[i]! ≤ 1 ∨ 3 ≤ StaggerTableLayout.pairIndices[i]!
    · have hm : StaggerCoreModel.message W i = StaggerCoreModel.message T i := by
        have hw := word_gap W T _ hp hb
        simp only [StaggerCoreModel.message, hw]
      rw [hm]
      exact h.paired i hi77
    · have h2 : StaggerTableLayout.pairIndices[i]! = 2 := by omega
      have hne : i ≠ 76 := by
        intro he
        rw [he] at h2
        exact absurd h2 (by decide)
      have hmW : StaggerCoreModel.message W i = MachineState.readWord W (18*2) := by
        simp only [StaggerCoreModel.message, if_neg hne, h2]
      have hmT : StaggerCoreModel.message T i = MachineState.readWord T (18*2) := by
        simp only [StaggerCoreModel.message, if_neg hne, h2]
      have hl := StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)
      rw [hmT] at hl
      apply Or.inr
      refine ⟨Or.inl hne, ?_, ?_, ?_⟩
      · rw [hmW]
        exact (lanes_gap W T 2 hb).1.trans hl.1
      · rw [hmW]
        exact (lanes_gap W T 2 hb).2.trans hl.2
      · rw [hmW]
        refine PoolFacts.zero_byte_slack _ 18 (by decide) (by decide) ?_
        rw [PoolByte.read _ _ _ (by decide)]
        exact hz
  · intro j hj
    apply UInt32.toNat_inj.mp
    have hp := congrArg UInt32.toNat (h.scalar j hj)
    exact (lanes_gap W T j hb).1.trans hp

theorem ready (m r : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (hr : Clear r)
    (words : Nat → UInt32)
    (h : StaggerMessage.Ready (resultMemory true r lo hi) words) :
    StaggerMessage.Ready (resultMemoryV2 m lo hi) words := by
  constructor
  · intro i hi77
    apply Or.inr
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hi76 : i = 76
      · subst i
        apply Or.inr
        have haddr : 18 * StaggerTableLayout.pairIndices[76]! = 594 := by decide
        simp only [StaggerCoreModel.message, ite_self, haddr]
        exact PoolFacts.result_terminal_bound m lo hi hc
      · exact Or.inl hi76
    · have ht := (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
      have hp := (StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)).1
      simp only [StaggerCoreModel.message, ite_self] at hp ⊢
      exact (PoolFacts.result_lanes m r lo hi hc hr _ ht).1.trans hp
    · have ht := (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
      have hp := (StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)).2
      simp only [StaggerCoreModel.message, ite_self] at hp ⊢
      exact (PoolFacts.result_lanes m r lo hi hc hr _ ht).2.trans hp
    · simp only [StaggerCoreModel.message, ite_self]
      exact PoolFacts.result_slack m lo hi hc _ (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
  · intro j hj
    apply UInt32.toNat_inj.mp
    have hp := congrArg UInt32.toNat (h.scalar j hj)
    exact (PoolFacts.result_lanes m r lo hi hc hr j hj).1.trans hp

/-! ### Transporting `Ready` from byte 28

The pad-only block's real table keeps bytes [0,28) of the incoming memory, which the actual
image no longer keeps clean, while the model clears them.  `Ready` reads nothing below byte 28
except through slot 1's slack (bytes 32..49 -- all from 28) and slot 1's upper bits, which only
`LegacyMessageWord` could inspect: slot 1 is forced onto the `Safe` disjunct with byte 32 as
its zero slack byte, and slot 0 is never a round's pair word. -/

theorem ready_of_from28 (W T : ByteArray) (words : Nat → UInt32)
    (hb : ∀ i, 28 ≤ i → W[i]?.getD 0 = T[i]?.getD 0)
    (hz : W[32]?.getD 0 = 0)
    (h : StaggerMessage.Ready T words) : StaggerMessage.Ready W words := by
  have hlow (j : Nat) :
      (MachineState.readWord W (18*j)).toNat % 2^32
        = (MachineState.readWord T (18*j)).toNat % 2^32 := by
    rw [PoolFacts.low_value, PoolFacts.low_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    exact hb _ (by omega)
  have hhigh : (MachineState.readWord W (18*1)).toNat / 2^144 % 2^32
      = (MachineState.readWord T (18*1)).toNat / 2^144 % 2^32 := by
    rw [PoolFacts.high_value, PoolFacts.high_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    exact hb _ (by omega)
  constructor
  · intro i hi77
    have hpos := (StaggerTableLayout.layout_valid ⟨i, hi77⟩).1
    change 1 ≤ StaggerTableLayout.pairIndices[i]! at hpos
    by_cases hp : 2 ≤ StaggerTableLayout.pairIndices[i]!
    · have hw : MachineState.readWord W (18 * StaggerTableLayout.pairIndices[i]!) =
          MachineState.readWord T (18 * StaggerTableLayout.pairIndices[i]!) := by
        apply Word.word_ext
        rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
        apply StaggerTableMemory.bytesToNatPadded_congrOffset
        intro k hk
        exact hb _ (by omega)
      have hm : StaggerCoreModel.message W i = StaggerCoreModel.message T i := by
        simp only [StaggerCoreModel.message, hw]
      rw [hm]
      exact h.paired i hi77
    · have h1 : StaggerTableLayout.pairIndices[i]! = 1 := by omega
      have hne : i ≠ 76 := by
        intro he
        rw [he] at h1
        exact absurd h1 (by decide)
      have hmW : StaggerCoreModel.message W i = MachineState.readWord W (18*1) := by
        simp only [StaggerCoreModel.message, if_neg hne, h1]
      have hmT : StaggerCoreModel.message T i = MachineState.readWord T (18*1) := by
        simp only [StaggerCoreModel.message, if_neg hne, h1]
      have hl := StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)
      rw [hmT] at hl
      apply Or.inr
      refine ⟨Or.inl hne, ?_, ?_, ?_⟩
      · rw [hmW]
        exact (hlow 1).trans hl.1
      · rw [hmW]
        exact hhigh.trans hl.2
      · rw [hmW]
        refine PoolFacts.zero_byte_slack _ 14 (by decide) (by decide) ?_
        rw [PoolByte.read _ _ _ (by decide)]
        exact hz
  · intro j hj
    apply UInt32.toNat_inj.mp
    have hp := congrArg UInt32.toNat (h.scalar j hj)
    exact (hlow j).trans hp

#print axioms ready
#print axioms result_outside
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant

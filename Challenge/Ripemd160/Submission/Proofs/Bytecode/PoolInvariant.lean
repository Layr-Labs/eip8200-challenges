import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolFacts

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PoolShape PoolShapeV2

/-- The copy holes of the C2 staging (60, 61, 614, 615, 648, 649) and the two bytes of the
terminal slot (594, 595) that the raw word 0 carries into the table's hole at 60, 61. -/
def ExtraClear (m : ByteArray) : Prop := ∀ a ∈ [60,61,594,595,614,615,648,649], m[a]?.getD 0 = 0

theorem clear_of_parts (m : ByteArray)
    (hlow : (MachineState.readWord m 0).toNat % 2^144 < 2^32)
    (hgap : PairStoreGap.GapClear m) (hextra : ExtraClear m)
    (hzero0 : m[0]?.getD 0 = 0) : Clear m := by
  intro a ha
  rw [zeroAddresses, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact hzero0
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at ha
  rcases ha with (⟨k,hk,rfl⟩ | ha) | ⟨j,hj,k,hk,rfl⟩
  · have h := PoolFacts.zero_from_window m 14 14 k (StaggerScratch.low_zero m hlow 14 (by decide) (by decide)) hk
    simpa [Nat.add_comm] using h
  · exact hextra a ha
  · simpa only [Nat.add_assoc] using hgap j hj (14+k) (by omega) (by omega)

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

theorem clear_extra (m : ByteArray) (hc : Clear m) : ExtraClear m := by
  intro a ha
  apply hc
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ ha))

theorem clear_zero0 (m : ByteArray) (hc : Clear m) : m[0]?.getD 0 = 0 :=
  hc 0 (List.mem_cons_self ..)

theorem clear_of_zero (m : ByteArray) (hz : ∀ a, a < 1056 → m[a]?.getD 0 = 0) : Clear m :=
  fun a ha => hz a (PoolCertificates.zeroAddresses_bound a ha)

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

/-- Above the copied block the v2m fan image is the incoming memory verbatim. -/
theorem fanV2_getD_high (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    (fanMemoryV2 m lo hi)[a]?.getD 0 = m[a]?.getD 0 := by
  rw [fanMemoryV2, PoolShapeV2.copiedV2_getD, PoolShapeV2.copiedAddressV2,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    PoolShapeV2.scratchV2_getD, if_neg (by omega), if_neg (by omega)]

theorem resultV2_outside (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    (resultMemoryV2 m lo hi)[a]?.getD 0 = m[a]?.getD 0 := by
  rw [resultMemoryV2, PoolRawWriter.writerMemory, rawWrites_eq,
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
    · have hm : StaggerCoreModel.message W i = StaggerCoreModel.message T i :=
        word_gap W T _ hp hb
      rw [hm]
      exact h.paired i hi77
    · have h2 : StaggerTableLayout.pairIndices[i]! = 2 := by omega
      have hne : i ≠ 76 := by
        intro he
        rw [he] at h2
        exact absurd h2 (by decide)
      have hmW : StaggerCoreModel.message W i = MachineState.readWord W (18*2) := by
        show MachineState.readWord W (18 * StaggerTableLayout.pairIndices[i]!) = _
        rw [h2]
      have hmT : StaggerCoreModel.message T i = MachineState.readWord T (18*2) := by
        show MachineState.readWord T (18 * StaggerTableLayout.pairIndices[i]!) = _
        rw [h2]
      have hl := StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)
      rw [hmT] at hl
      apply Or.inr
      refine ⟨hne, ?_, ?_, ?_⟩
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

theorem ready (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (words : Nat → UInt32)
    (h : StaggerMessage.Ready (resultMemory true m lo hi) words) :
    StaggerMessage.Ready (resultMemoryV2 m lo hi) words := by
  constructor
  · intro i hi77
    by_cases hi76 : i = 76
    · subst i
      have ht := PoolFacts.result_terminal m lo hi hc
      have hm : StaggerCoreModel.message (resultMemoryV2 m lo hi) 76 =
          StaggerCoreModel.message (resultMemory true m lo hi) 76 := ht
      rw [hm]
      exact h.paired 76 hi77
    · apply Or.inr
      refine ⟨hi76, ?_, ?_, ?_⟩
      · have ht := (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
        have hp := (StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)).1
        exact (PoolFacts.result_lanes m lo hi hc _ ht).1.trans hp
      · have ht := (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
        have hp := (StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)).2
        exact (PoolFacts.result_lanes m lo hi hc _ ht).2.trans hp
      · exact PoolFacts.result_slack m lo hi hc _ (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
  · intro j hj
    apply UInt32.toNat_inj.mp
    have hp := congrArg UInt32.toNat (h.scalar j hj)
    exact (PoolFacts.result_lanes m lo hi hc j hj).1.trans hp

#print axioms ready
#print axioms result_outside
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant

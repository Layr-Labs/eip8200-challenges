import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolFacts

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PoolShape

def ExtraClear (m : ByteArray) : Prop := ∀ a ∈ [94,95,128,129], m[a]?.getD 0 = 0

theorem clear_of_parts (m : ByteArray)
    (hlow : (MachineState.readWord m 0).toNat % 2^144 < 2^32)
    (hgap : PairStoreGap.GapClear m) (hextra : ExtraClear m) : Clear m := by
  intro a ha
  simp only [zeroAddresses, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at ha
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
  simp only [zeroAddresses, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl ⟨k-14, by omega, by omega⟩)

theorem clear_gap (m : ByteArray) (hc : Clear m) : PairStoreGap.GapClear m := by
  intro j hj k hl hu
  apply hc
  simp only [zeroAddresses, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  exact Or.inr ⟨j,hj,k-14,by omega,by omega⟩

theorem clear_extra (m : ByteArray) (hc : Clear m) : ExtraClear m := by
  intro a ha
  apply hc
  exact List.mem_append_left _ (List.mem_append_right _ ha)

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

theorem ready (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (words : Nat → UInt32)
    (h : StaggerMessage.Ready (resultMemory true m lo hi) words) :
    StaggerMessage.Ready (resultMemory false m lo hi) words := by
  constructor
  · intro i hi77
    by_cases hi76 : i = 76
    · subst i
      have ht := PoolFacts.result_terminal m lo hi hc
      have hm : StaggerCoreModel.message (resultMemory false m lo hi) 76 =
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

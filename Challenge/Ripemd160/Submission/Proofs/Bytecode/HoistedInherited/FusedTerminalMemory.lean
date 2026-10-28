import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PoolInvariant

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open HoistedInherited.PoolShape HoistedInherited.PoolShapeV2 HoistedInherited.FusedTerminalCertificates

/-- The mask applies only to the consuming store at 594, not to other uses of word 11. -/
def storedWord (words : Nat → UInt256) (x : Nat × Nat) : UInt256 :=
  if x.1 = 594 then UInt256.land HoistedInherited.Pair13PoolRaw.poolMask (words x.2) else words x.2

def writerMemory (m : ByteArray) (words : Nat → UInt256) : ByteArray :=
  HoistedInherited.Pair13WriterRaw.writeChain m (writes.map fun x => (x.1, storedWord words x))

def resultMemory (m : ByteArray) (lo hi : UInt256) : ByteArray :=
  writerMemory (fanMemoryV2 m lo hi) (HoistedInherited.Pair13PoolRaw.poolWordV2 (fanMemoryV2 m lo hi))

theorem result_outside (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    (resultMemory m lo hi)[a]?.getD 0 = m[a]?.getD 0 := by
  unfold resultMemory writerMemory
  have he : writes.map (fun x => (x.1, storedWord (HoistedInherited.Pair13PoolRaw.poolWordV2 (fanMemoryV2 m lo hi)) x)) =
      writes.map (fun x => (x.1, if x.1 = 594 then
        UInt256.land HoistedInherited.Pair13PoolRaw.poolMask (HoistedInherited.Pair13PoolRaw.poolWordV2 (fanMemoryV2 m lo hi) x.2)
        else HoistedInherited.Pair13PoolRaw.poolWordV2 (fanMemoryV2 m lo hi) x.2)) := rfl
  rw [he]
  have houtside {mem : ByteArray} {ws : List (Nat × Nat)}
      (f : Nat × Nat → UInt256) (hb : ∀ x ∈ ws, x.1 + 32 ≤ a) :
      (HoistedInherited.Pair13WriterRaw.writeChain mem (ws.map (fun x => (x.1, f x))))[a]?.getD 0 = mem[a]?.getD 0 := by
    induction ws generalizing mem with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, HoistedInherited.Pair13WriterRaw.writeChain_cons]
      rw [ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)), HoistedInherited.Shared32Scratch.writeWord_getD,
        if_neg (by have := hb x (List.mem_cons_self ..); omega)]
  rw [houtside _ (fun x hx => (HoistedInherited.PoolCertificates.writes_bound x hx).1.trans ha)]
  exact HoistedInherited.PoolInvariant.fanV2_getD_high _ _ _ _ ha

theorem read_result_outside (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    MachineState.readWord (resultMemory m lo hi) a = MachineState.readWord m a := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact StaggerTableMemory.bytesToNatPadded_congrOffset _ _ _ _ _
    (fun i _ => result_outside m lo hi (a+i) (by omega))

theorem writeChain_shape (m original : ByteArray) (lo hi : UInt256)
    (f : Nat → Source) (words : Nat → UInt256) (g : Nat → Nat → Source)
    (ws : List (Nat × Nat))
    (hf : ∀ a, m[a]?.getD 0 = (f a).eval original lo hi)
    (hg : ∀ x ∈ ws, ∀ j, j < 32 → PoolByte.byte (words x.2) j = (g x.2 j).eval original lo hi) :
    ∀ a, (HoistedInherited.Pair13WriterRaw.writeChain m (ws.map fun x => (x.1, storedWord words x)))[a]?.getD 0 =
      (fusedStoreSources g f ws a).eval original lo hi := by
  induction ws generalizing m f with
  | nil => exact hf
  | cons x rest ih =>
    rcases x with ⟨address,index⟩
    simp only [List.map_cons, HoistedInherited.Pair13WriterRaw.writeChain_cons, fusedStoreSources]
    apply ih
    · intro a
      rw [HoistedInherited.Shared32Scratch.writeWord_getD]
      unfold fusedStoreSource
      by_cases ha : address ≤ a ∧ a < address+32
      · rw [if_pos ha, if_pos ha, PoolByte.encoded _ _ (by omega)]
        unfold storedWord
        by_cases hx : address = 594
        · rw [if_pos hx, if_pos hx, byte_mask _ _ (by omega),
            hg (address,index) (List.mem_cons_self ..) _ (by omega)]
          unfold maskSource
          split <;> rfl
        · rw [if_neg hx, if_neg hx]
          exact hg (address,index) (List.mem_cons_self ..) _ (by omega)
      · rw [if_neg ha, if_neg ha]
        exact hf a
    · intro x hx j hj
      exact hg x (List.mem_cons_of_mem _ hx) j hj

theorem result_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (a : Nat) :
    (resultMemory m lo hi)[a]?.getD 0 = (HoistedInherited.FusedTerminalCertificates.resultSource a).eval m lo hi := by
  unfold resultMemory writerMemory HoistedInherited.FusedTerminalCertificates.resultSource
  have hindices : ∀ x ∈ writes, x.2 < 16 := by decide
  exact writeChain_shape _ m lo hi _ _ _ writes (fanV2_shape m lo hi hc)
    (fun x hx j hj => poolV2_shape m lo hi hc x.2 j (hindices x hx) hj) a

/-- Bridge the fused image to the already-verified actual image, on the live lanes. -/
theorem result_lanes (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m)
    (j : Nat) (hj : j < 61) :
    (MachineState.readWord (resultMemory m lo hi) (18*j)).toNat % 2^32 =
      (MachineState.readWord (resultMemoryV2 m lo hi) (18*j)).toNat % 2^32 ∧
    (MachineState.readWord (resultMemory m lo hi) (18*j)).toNat / 2^144 % 2^32 =
      (MachineState.readWord (resultMemoryV2 m lo hi) (18*j)).toNat / 2^144 % 2^32 := by
  constructor
  · rw [HoistedInherited.PoolFacts.low_value, HoistedInherited.PoolFacts.low_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    rw [result_shape m lo hi hc, resultV2_shape m lo hi hc,
      (lane_sources ⟨j,hj⟩ ⟨k,hk⟩).2]
  · rw [HoistedInherited.PoolFacts.high_value, HoistedInherited.PoolFacts.high_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    rw [result_shape m lo hi hc, resultV2_shape m lo hi hc,
      (lane_sources ⟨j,hj⟩ ⟨k,hk⟩).1]

theorem result_clear (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) :
    ClearV2 (resultMemory m lo hi) := by
  intro a ha
  rw [result_shape m lo hi hc, clear_sources a ha]
  rfl

theorem result_slack (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (j : Nat) (hj : j < 61) :
    (MachineState.readWord (resultMemory m lo hi) (18*j)).toNat % 2^144 + 2^40 ≤ 2^144 := by
  obtain ⟨hl,hu,-⟩ := HoistedInherited.PoolCertificatesV2.slack_sources ⟨j,hj⟩
  apply HoistedInherited.PoolFacts.zero_byte_slack _ _ hl hu
  rw [PoolByte.read _ _ _ (by omega), result_shape m lo hi hc, slack_sources ⟨j,hj⟩]
  rfl

theorem result_terminal_bound (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) :
    (MachineState.readWord (resultMemory m lo hi) 594).toNat % 2^144 < 2^120 := by
  have h := StaggerTableMemory.readWord_mod_pow (resultMemory m lo hi) 594 18 (by decide)
  change (MachineState.readWord (resultMemory m lo hi) 594).toNat % 2^144 =
    Precompile.bytesToNatPadded (resultMemory m lo hi) 608 18 at h
  rw [h, show (18:Nat)=3+15 from rfl, Bytes.bytesToNatPadded_add,
    HoistedInherited.PoolFacts.window_zero (resultMemory m lo hi) 608 3 (fun k hk => by
      rw [result_shape m lo hi hc, terminal_gap_sources ⟨k, hk⟩]
      rfl)]
  simpa using Bytes.bytesToNatPadded_lt_pow (resultMemory m lo hi) (608+3) 15

theorem ready (m r : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (hr : Clear r)
    (words : Nat → UInt32)
    (h : StaggerMessage.Ready (HoistedInherited.PoolShape.resultMemory true r lo hi) words) :
    StaggerMessage.Ready (resultMemory m lo hi) words := by
  constructor
  · intro i hi77
    apply Or.inr
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hi76 : i = 76
      · subst i
        apply Or.inr
        have haddr : 18 * StaggerTableLayout.pairIndices[76]! = 594 := by decide
        simp only [StaggerCoreModel.message, ite_self, haddr]
        exact result_terminal_bound m lo hi hc
      · exact Or.inl hi76
    · have ht := (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
      have hp := (StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)).1
      simp only [StaggerCoreModel.message, ite_self] at hp ⊢
      exact ((result_lanes m lo hi hc _ ht).1.trans (HoistedInherited.PoolFacts.result_lanes m r lo hi hc hr _ ht).1).trans hp
    · have ht := (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
      have hp := (StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)).2
      simp only [StaggerCoreModel.message, ite_self] at hp ⊢
      exact ((result_lanes m lo hi hc _ ht).2.trans (HoistedInherited.PoolFacts.result_lanes m r lo hi hc hr _ ht).2).trans hp
    · simp only [StaggerCoreModel.message, ite_self]
      exact result_slack m lo hi hc _ (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
  · intro j hj
    apply UInt32.toNat_inj.mp
    have hp := congrArg UInt32.toNat (h.scalar j hj)
    exact ((result_lanes m lo hi hc j hj).1.trans (HoistedInherited.PoolFacts.result_lanes m r lo hi hc hr j hj).1).trans hp


#print axioms ready
#print axioms result_shape
#print axioms result_lanes
#print axioms result_clear
#print axioms result_slack
#print axioms result_terminal_bound
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalMemory

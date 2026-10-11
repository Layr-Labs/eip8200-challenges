import Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotCertificates
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.BackwardSnapshotMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PoolShape PoolShapeV2

/-- Four snapshot stores. The first and third widen backward to avoid live upper lanes. -/
def firstPrefix (m : ByteArray) : ByteArray :=
  MachineState.writeBytes m (MachineState.readPadded m 146 32) 128

def secondPrefix (m : ByteArray) : ByteArray :=
  MachineState.writeBytes (firstPrefix m) (MachineState.readPadded (firstPrefix m) 178 32) 196

def thirdPrefix (m : ByteArray) : ByteArray :=
  MachineState.writeBytes (secondPrefix m) (MachineState.readPadded (secondPrefix m) 236 32) 218

def copiedFour (m : ByteArray) : ByteArray :=
  MachineState.writeBytes (thirdPrefix m) (MachineState.readPadded (thirdPrefix m) 268 32) 286

def copiedAddress (a : Nat) : Nat :=
  if 286 ≤ a ∧ a < 318 then a-18
  else if 218 ≤ a ∧ a < 250 then a+18
  else if 196 ≤ a ∧ a < 228 then a-18
  else if 128 ≤ a ∧ a < 160 then a+18 else a

theorem copiedFour_getD (m : ByteArray) (a : Nat) :
    (copiedFour m)[a]?.getD 0 = m[copiedAddress a]?.getD 0 := by
  simp only [copiedFour, thirdPrefix, secondPrefix, firstPrefix,
    SecondSnapshotCertificates.copy_getD, copiedAddress]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

def fanSource (a : Nat) : Source := scratchSourceV2 (copiedAddress a)
def poolSource (i j : Nat) : Source := fanSource (Pair13PoolRaw.poolAddrV2 i+j)
def resultSource (a : Nat) : Source :=
  FusedTerminalCertificates.fusedStoreSources poolSource fanSource writes a

/-- Garbage bytes need not be equal; all live arithmetic lanes must be. -/
theorem lane_sources : ∀ j : Fin 61, ∀ k : Fin 4,
    resultSource (18*j.val+10+k.val) = FusedTerminalCertificates.resultSource (18*j.val+10+k.val) ∧
    resultSource (18*j.val+28+k.val) = FusedTerminalCertificates.resultSource (18*j.val+28+k.val) := by decide

theorem clear_sources : ∀ a ∈ zeroAddressesV2, resultSource a = .zero := by decide

theorem terminal_gap_sources : ∀ k : Fin 3, resultSource (608+k.val) = .zero := by decide

theorem slack_sources : ∀ j : Fin 61, ∃ k : Fin 13,
    resultSource (18*j.val+14+k.val) = .zero := by decide

def fanMemory (m : ByteArray) (lo hi : UInt256) : ByteArray :=
  copiedFour (Pair13Endian.scratchV2 m lo hi)

def resultMemory (m : ByteArray) (lo hi : UInt256) : ByteArray :=
  FusedTerminalMemory.writerMemory (fanMemory m lo hi) (Pair13PoolRaw.poolWordV2 (fanMemory m lo hi))

theorem result_outside (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    (resultMemory m lo hi)[a]?.getD 0 = m[a]?.getD 0 := by
  unfold resultMemory FusedTerminalMemory.writerMemory
  have he : writes.map (fun x => (x.1, FusedTerminalMemory.storedWord (Pair13PoolRaw.poolWordV2 (fanMemory m lo hi)) x)) =
      writes.map (fun x => (x.1, if x.1 = 594 then
        UInt256.land Pair13PoolRaw.poolMask (Pair13PoolRaw.poolWordV2 (fanMemory m lo hi) x.2)
        else Pair13PoolRaw.poolWordV2 (fanMemory m lo hi) x.2)) := rfl
  rw [he]
  have houtside {mem : ByteArray} {ws : List (Nat × Nat)}
      (f : Nat × Nat → UInt256) (hb : ∀ x ∈ ws, x.1 + 32 ≤ a) :
      (Pair13WriterRaw.writeChain mem (ws.map (fun x => (x.1, f x))))[a]?.getD 0 = mem[a]?.getD 0 := by
    induction ws generalizing mem with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, Pair13WriterRaw.writeChain_cons]
      rw [ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)), Shared32Scratch.writeWord_getD,
        if_neg (by have := hb x (List.mem_cons_self ..); omega)]
  rw [houtside _ (fun x hx => (PoolCertificates.writes_bound x hx).1.trans ha)]
  rw [fanMemory, copiedFour_getD, copiedAddress,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    Pair13Endian.scratchV2, Shared32Scratch.writeWord_getD, if_neg (by omega),
    Shared32Scratch.writeWord_getD, if_neg (by omega)]

theorem read_result_outside (m : ByteArray) (lo hi : UInt256) (a : Nat) (ha : 1112 ≤ a) :
    MachineState.readWord (resultMemory m lo hi) a = MachineState.readWord m a := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact StaggerTableMemory.bytesToNatPadded_congrOffset _ _ _ _ _
    (fun i _ => result_outside m lo hi (a+i) (by omega))


theorem fan_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (a : Nat) :
    (fanMemory m lo hi)[a]?.getD 0 = (fanSource a).eval m lo hi := by
  rw [fanMemory, copiedFour_getD, fanSource]
  exact scratchV2_shape m lo hi hc _

theorem pool_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m)
    (i j : Nat) (hj : j < 32) :
    PoolByte.byte (Pair13PoolRaw.poolWordV2 (fanMemory m lo hi) i) j =
      (poolSource i j).eval m lo hi := by
  rw [Pair13PoolRaw.poolWordV2, Pair13PoolRaw.rawLoadV2, PoolByte.read _ _ _ hj,
    fan_shape m lo hi hc]
  rfl

theorem result_shape (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (a : Nat) :
    (resultMemory m lo hi)[a]?.getD 0 = (resultSource a).eval m lo hi := by
  unfold resultMemory FusedTerminalMemory.writerMemory resultSource
  exact FusedTerminalMemory.writeChain_shape _ m lo hi _ _ _ writes (fan_shape m lo hi hc)
    (fun x _ j hj => pool_shape m lo hi hc x.2 j hj) a

theorem result_lanes (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m)
    (j : Nat) (hj : j < 61) :
    (MachineState.readWord (resultMemory m lo hi) (18*j)).toNat % 2^32 =
      (MachineState.readWord (FusedTerminalMemory.resultMemory m lo hi) (18*j)).toNat % 2^32 ∧
    (MachineState.readWord (resultMemory m lo hi) (18*j)).toNat / 2^144 % 2^32 =
      (MachineState.readWord (FusedTerminalMemory.resultMemory m lo hi) (18*j)).toNat / 2^144 % 2^32 := by
  constructor
  · rw [PoolFacts.low_value, PoolFacts.low_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    rw [result_shape m lo hi hc, FusedTerminalMemory.result_shape m lo hi hc,
      (lane_sources ⟨j,hj⟩ ⟨k,hk⟩).2]
  · rw [PoolFacts.high_value, PoolFacts.high_value]
    apply StaggerTableMemory.bytesToNatPadded_congrOffset
    intro k hk
    rw [result_shape m lo hi hc, FusedTerminalMemory.result_shape m lo hi hc,
      (lane_sources ⟨j,hj⟩ ⟨k,hk⟩).1]

theorem result_clear (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) :
    ClearV2 (resultMemory m lo hi) := by
  intro a ha
  rw [result_shape m lo hi hc, clear_sources a ha]
  rfl

theorem result_slack (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) (j : Nat) (hj : j < 61) :
    (MachineState.readWord (resultMemory m lo hi) (18*j)).toNat % 2^144 + 2^40 ≤ 2^144 := by
  obtain ⟨k,hk⟩ := slack_sources ⟨j,hj⟩
  apply PoolFacts.zero_byte_slack _ (14+k.val) (by omega) (by omega)
  rw [PoolByte.read _ _ _ (by omega), result_shape m lo hi hc]
  rw [show 18*j+(14+k.val) = 18*j+14+k.val by omega, hk]
  rfl

theorem result_terminal_bound (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) :
    (MachineState.readWord (resultMemory m lo hi) 594).toNat % 2^144 < 2^120 := by
  have h := StaggerTableMemory.readWord_mod_pow (resultMemory m lo hi) 594 18 (by decide)
  change (MachineState.readWord (resultMemory m lo hi) 594).toNat % 2^144 =
    Precompile.bytesToNatPadded (resultMemory m lo hi) 608 18 at h
  rw [h, show (18:Nat)=3+15 from rfl, Bytes.bytesToNatPadded_add,
    PoolFacts.window_zero (resultMemory m lo hi) 608 3 (fun k hk => by
      rw [result_shape m lo hi hc, terminal_gap_sources ⟨k, hk⟩]
      rfl)]
  simpa using Bytes.bytesToNatPadded_lt_pow (resultMemory m lo hi) (608+3) 15

theorem ready (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m)
    (words : Nat → UInt32)
    (h : StaggerMessage.Ready (FusedTerminalMemory.resultMemory m lo hi) words) :
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
      exact ((result_lanes m lo hi hc _ ht).1).trans hp
    · have ht := (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
      have hp := (StaggerAlgorithm.message_lanes _ _ _ (h.paired i hi77)).2
      simp only [StaggerCoreModel.message, ite_self] at hp ⊢
      exact ((result_lanes m lo hi hc _ ht).2).trans hp
    · simp only [StaggerCoreModel.message, ite_self]
      exact result_slack m lo hi hc _ (StaggerTableLayout.layout_valid ⟨i,hi77⟩).2.1
  · intro j hj
    apply UInt32.toNat_inj.mp
    have hp := congrArg UInt32.toNat (h.scalar j hj)
    exact ((result_lanes m lo hi hc j hj).1).trans hp

#print axioms ready
#print axioms result_shape
#print axioms copiedFour_getD
#print axioms lane_sources
#print axioms clear_sources
#print axioms terminal_gap_sources
#print axioms slack_sources
end Challenge.Ripemd160.Submission.Proofs.Bytecode.BackwardSnapshotMemory

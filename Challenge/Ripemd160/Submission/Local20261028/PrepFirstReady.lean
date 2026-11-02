import Challenge.Ripemd160.Submission.Local20261028.PrepFirstCertificate
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary75

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.FirstReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RipemdMemoryBridge20261028 RipemdSubmissionTables20261028
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028
open GeneralMessageLayout
open PairedLaneUInt256Bridge Paired144Core

open OrdinaryReads
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028
theorem low_read (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstLayout.initial (FirstLayout.value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (slot : Nat) (hslot : slot < 61) (hne : slot ≠ 51) :
    (CoreModel.load (FirstTable.result5 s x rho).memory (18*slot)).toNat % 2^32 =
      (entryWords s.memory StaggerTableLayout.slots[slot]!).toNat := by
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [low_value, entryWords_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [FirstLayout.actual_bytes s x rho hz hc, FirstLayout.low_sources ⟨slot,hslot⟩ hne ⟨j,hj⟩]
  exact (hz _).symm

theorem high_read (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstLayout.initial (FirstLayout.value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (i : Nat) (hi : i < 77) :
    (CoreModel.load (FirstTable.result5 s x rho).memory
      (18*StaggerTableLayout.pairIndices[i]!)).toNat / 2^144 % 2^32 =
      (entryWords s.memory Crypto.Ripemd160.rP[i+3]!).toNat := by
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [high_value, entryWords_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [FirstLayout.actual_bytes s x rho hz hc, FirstLayout.high_sources ⟨i,hi⟩ ⟨j,hj⟩]
  exact (hz _).symm

theorem raw_slack (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstLayout.initial (FirstLayout.value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (i : Nat) (hi : i < 77) :
    (CoreModel.load (FirstTable.result5 s x rho).memory
      (18*StaggerTableLayout.pairIndices[i]!)).toNat % 2^144 + 2^40 ≤ 2^144 := by
  obtain ⟨hl,hu,hzero⟩ := FirstLayout.barrier_sources ⟨i,hi⟩
  change 14 ≤ barriers[i]! at hl
  change barriers[i]! ≤ 26 at hu
  apply zero_byte_slack _ barriers[i]! hl hu
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [PoolByte.read _ _ _ (by omega), FirstLayout.actual_bytes s x rho hz hc, hzero]
  rfl

theorem read75 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstLayout.initial (FirstLayout.value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    MachineState.readWord (FirstTable.result5 s x rho).memory 918 = UInt256.ofNat 2840853966 := by
  apply Ordinary75.read_eq_of_bytes
  intro j hj
  rw [FirstLayout.actual_bytes s x rho hz hc]
  have h : ∀ j : Fin 32, FirstLayout.value s.memory (FirstLayout.symbols27 (918+j.val)) =
      PoolByte.byte (UInt256.ofNat 2840853966) j.val := by
    intro j; fin_cases j <;> rfl
  exact h ⟨j,hj⟩

theorem ready (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstLayout.initial (FirstLayout.value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    CoreMessage.Ready (FirstTable.result5 s x rho).memory (entryWords s.memory) := by
  constructor
  · intro i hi
    obtain ⟨_,hslot,hleft,_⟩ := StaggerTableLayout.layout_valid ⟨i,hi⟩
    apply Or.inr
    by_cases hb : i=75
    · subst i
      have hm : CoreModel.message (FirstTable.result5 s x rho).memory 75 = UInt256.ofNat 128 := by
        change UInt256.sub (MachineState.readWord (FirstTable.result5 s x rho).memory 918) (UInt256.ofNat 2840853838) = _
        rw [read75 s x rho hz hc]
        rfl
      have hleft8 : entryWords s.memory 8 = 128 := by
        apply UInt32.toNat_inj.mp
        rw [entryWords_toNat]
        change Precompile.bytesToNatPadded s.memory 162 4 = 128
        have hbytes : ∀ j : Fin 4, s.memory[162+j.val]?.getD 0 = (ByteArray.mk #[0,0,0,128])[j.val]?.getD 0 := by
          intro j; rw [hz]; fin_cases j <;> rfl
        have he := StaggerTableMemory.bytesToNatPadded_congrOffset s.memory (ByteArray.mk #[0,0,0,128]) 162 0 4
          (by intro j hj; simpa using hbytes ⟨j,hj⟩)
        exact he.trans (by decide +kernel)
      have hright : entryWords s.memory 9 = 0 := by
        apply UInt32.toNat_inj.mp
        rw [entryWords_toNat]
        change Precompile.bytesToNatPadded s.memory 166 4 = 0
        have hbytes : ∀ j : Fin 4, s.memory[166+j.val]?.getD 0 = (ByteArray.mk #[0,0,0,0])[j.val]?.getD 0 := by
          intro j; rw [hz]; fin_cases j <;> rfl
        have he := StaggerTableMemory.bytesToNatPadded_congrOffset s.memory (ByteArray.mk #[0,0,0,0]) 166 0 4
          (by intro j hj; simpa using hbytes ⟨j,hj⟩)
        exact he.trans (by decide +kernel)
      rw [hm]
      refine ⟨Or.inl (by decide), ?_⟩
      change StaggerLaneSafe.Safe (UInt256.ofNat 128) (entryWords s.memory 8) (entryWords s.memory 9)
      rw [hleft8, hright]
      exact ⟨by decide, by decide, by decide⟩
    · have hne : StaggerTableLayout.pairIndices[i]! ≠ 51 := by
        have hc : ∀ j : Fin 77, StaggerTableLayout.pairIndices[j.val]! = 51 → j.val=75 := by decide +kernel
        intro h; exact hb (hc ⟨i,hi⟩ h)
      have hlo := low_read s x rho hz hc StaggerTableLayout.pairIndices[i]! hslot hne
      rw [hleft] at hlo
      have hhi := high_read s x rho hz hc i hi
      have hs := raw_slack s x rho hz hc i hi
      by_cases ht : i=76
      · subst i
        simp only [CoreModel.message, if_pos rfl, ite_true]
        have hm := RipemdSubmissionTerminalRepair20261028.masked_small
          (CoreModel.load (FirstTable.result5 s x rho).memory (18*StaggerTableLayout.pairIndices[76]!))
        refine ⟨Or.inr hm, ⟨?_,?_,?_⟩⟩
        · rw [mask_low]; exact hlo
        · rw [mask_high]; exact hhi
        · omega
      · simp only [CoreModel.message, if_neg ht, if_neg hb]
        exact ⟨Or.inl ht, ⟨hlo,hhi,hs⟩⟩
  · intro j hj hne
    apply UInt32.toNat_inj.mp
    exact low_read s x rho hz hc j hj hne
#print axioms read75
#print axioms ready
end RipemdSubmission20261101.FirstReady

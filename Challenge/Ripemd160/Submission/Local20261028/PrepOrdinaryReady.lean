import Challenge.Ripemd160.Submission.Local20261028.PrepReferenceReads
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.OrdinaryReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028
open GeneralMessageLayout

theorem sub_add_self (a b : UInt256) : UInt256.sub (UInt256.add a b) a = b := by
  unfold UInt256.add UInt256.sub
  congr 1
  exact add_sub_cancel_left a.val b.val

theorem message75 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0) :
    CoreModel.message (OrdinaryTable.result7 s x rho).memory 75 =
      MachineState.readWord (Ordinary75.reference s.memory) 918 := by
  change UInt256.sub (MachineState.readWord (OrdinaryTable.result7 s x rho).memory 918)
    (UInt256.ofNat BiasedBytes.key) = _
  rw [Ordinary75.read_add s x rho hz, sub_add_self]

theorem ready (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0) :
    CoreMessage.Ready (OrdinaryTable.result7 s x rho).memory (OrdinaryReads.entryWords s.memory) := by
  constructor
  · intro i hi
    obtain ⟨_,hslot,hleft,_⟩ := StaggerTableLayout.layout_valid ⟨i,hi⟩
    apply Or.inr
    by_cases hb : i=75
    · subst i
      have hlo := ReferenceReads.low_read s.memory hz StaggerTableLayout.pairIndices[75]! hslot
      rw [hleft] at hlo
      have hhi := ReferenceReads.high_read s.memory hz 75 (by decide)
      have hs := ReferenceReads.raw_slack s.memory hz 75 (by decide)
      rw [message75 s x rho hz]
      exact ⟨Or.inl (by decide), ⟨hlo,hhi,hs⟩⟩
    · have hne : StaggerTableLayout.pairIndices[i]! ≠ 51 := by
        have hc : ∀ j : Fin 77, StaggerTableLayout.pairIndices[j.val]! = 51 → j.val=75 := by decide +kernel
        intro h
        exact hb (hc ⟨i,hi⟩ h)
      have hlo := OrdinaryReads.low_read s x rho hz StaggerTableLayout.pairIndices[i]! hslot hne
      rw [hleft] at hlo
      have hhi := OrdinaryReads.high_read s x rho hz i hi
      have hs := OrdinaryReads.raw_slack s x rho hz i hi
      by_cases ht : i=76
      · subst i
        simp only [CoreModel.message, if_pos rfl, ite_true]
        have hm := RipemdSubmissionTerminalRepair20261028.masked_small
          (CoreModel.load (OrdinaryTable.result7 s x rho).memory (18*StaggerTableLayout.pairIndices[76]!))
        refine ⟨Or.inr hm, ⟨?_,?_,?_⟩⟩
        · rw [OrdinaryReads.mask_low]; exact hlo
        · rw [OrdinaryReads.mask_high]; exact hhi
        · omega
      · simp only [CoreModel.message, if_neg ht, if_neg hb, ite_false]
        exact ⟨Or.inl ht, ⟨hlo,hhi,hs⟩⟩
  · intro j hj hne
    apply UInt32.toNat_inj.mp
    exact OrdinaryReads.low_read s x rho hz j hj hne
#print axioms message75
#print axioms ready
end RipemdSubmission20261101.OrdinaryReady

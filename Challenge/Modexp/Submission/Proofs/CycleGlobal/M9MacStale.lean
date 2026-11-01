import Challenge.Modexp.Submission.Proofs.CycleGlobal.M9MacChain
import Challenge.Modexp.Submission.Proofs.Fast.Exp

noncomputable section
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

/-!
# M9: the MAC section entered with a stale `t` top limb

The shift-reduce loop heads no longer clear the `t` top limb (`2112 + 32 (n - 1)`, i.e. 2336 for
eight limbs and 2208 for four) after the `MCOPY`.  The section's first block
(`rideTopProgramNP`, block 0 / the four-limb `zero4` block) never reads that word: it overwrites it
with the zero-top product.  So entering the section on `um0` (top limb stale) reaches exactly the
state the existing section lemma reaches on `um = storeWord um0 top 0`.
-/

namespace CycleSubmission.Global.Fast.M9Mac
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open Challenge.Modexp.Submission.Proofs.Fast.M9Mac
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

theorem writeBytes_overwrite_stale (mem a b : ByteArray) (start : Nat) (hsz : a.size = b.size) :
    MachineState.writeBytes (MachineState.writeBytes mem a start) b start =
      MachineState.writeBytes mem b start := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size, hsz]
    split_ifs <;> omega
  · intro i h1 h2
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h1,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h2,
      MachineState.writeBytes_getElem?_getD, MachineState.writeBytes_getElem?_getD,
      MachineState.writeBytes_getElem?_getD, hsz]
    split <;> rfl

/-- The first MAC step on a cleared top limb, written over the stale memory. -/
theorem l1StepOn_stale (um0 : ByteArray) (bi : UInt256) (n j : Nat) :
    SquareModel.l1StepOn
        ⟨Exp.storeWord um0 (2112 + 32 * (n - 1 - j)) (UInt256.ofNat 0), UInt256.ofNat 0⟩
        bi 1280 n j =
      { memory := MachineState.writeBytes um0
          (Data.Bytes.natToBytesPadded
            (macSum (MachineState.readWord um0 (1280 + 32 * (n - 1 - j))) bi
              (UInt256.ofNat 0) (UInt256.ofNat 0)).toNat 32) (2112 + 32 * (n - 1 - j))
        carry := macCarry (MachineState.readWord um0 (1280 + 32 * (n - 1 - j))) bi
          (UInt256.ofNat 0) (UInt256.ofNat 0) } := by
  have hx : MachineState.readWord
      (Exp.storeWord um0 (2112 + 32 * (n - 1 - j)) (UInt256.ofNat 0)) (1280 + 32 * (n - 1 - j)) =
      MachineState.readWord um0 (1280 + 32 * (n - 1 - j)) :=
    Exp.storeWord_readWord_disjoint um0 _ _ _ (Or.inl (by omega))
  have ht : MachineState.readWord
      (Exp.storeWord um0 (2112 + 32 * (n - 1 - j)) (UInt256.ofNat 0)) (2112 + 32 * (n - 1 - j)) =
      UInt256.ofNat 0 := by
    unfold Exp.storeWord
    exact Challenge.EvmProof.Memory.readWord_writeWord um0 _ _
  unfold SquareModel.l1StepOn
  simp only [hx, ht]
  unfold Exp.storeWord
  rw [writeBytes_overwrite_stale]
  simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

/-- Block 0 on the stale top limb (eight limbs, pc 2787 to 2805). -/
def gasSteps_block0_stale (s : State) (um0 : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord (Exp.storeWord um0 2336 (UInt256.ofNat 0)) (1280 + 32 * (7 - i))))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat 2787) um0 q (maxWord :: rest))
      (chainState s (UInt256.ofNat 2805)
        (SquareModel.l1StepOn ⟨Exp.storeWord um0 2336 (UInt256.ofNat 0), UInt256.ofNat 0⟩ q 1280 8 0)
        q rest) := by
  have hs := hslot 0 (by omega)
  have hxu : MachineState.readWord (Exp.storeWord um0 2336 (UInt256.ofNat 0)) (1280 + 32 * (7 - 0)) =
      MachineState.readWord um0 (1280 + 32 * (8 - 1 - 0)) :=
    Exp.storeWord_readWord_disjoint um0 _ _ _ (Or.inl (by omega))
  rw [hxu] at hs
  have hx : rest[(10 : Fin 16).val - 2]? =
      some (MachineState.readWord (⟨um0, UInt256.ofNat 0⟩ : MacState).memory (1280 + 32 * (8 - 1 - 0))) := hs
  have h := run_ride_top_np_stale s (UInt256.ofNat 2787) ⟨um0, UInt256.ofNat 0⟩ q 8 0 2336 10
      (by decide) (MachineState.readWord um0 (1280 + 32 * (8 - 1 - 0))) rfl
      rest hrest (by decide) (by omega) hx (by decide) hact (by decide) (by decide)
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
  have he := l1StepOn_stale um0 q 8 0
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at he
  rw [he]
  exact block0.steps (environment (setupState s (UInt256.ofNat 2787) um0 q (maxWord :: rest))
    hcode hfork hrun hnp) rfl h

/-- The four-limb head's first product on the stale top limb (pc 10827 to 10845). -/
def gasSteps_zero4_stale (s : State) (um0 : ByteArray) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord (Exp.storeWord um0 2208 (UInt256.ofNat 0)) (1280 + 32 * (7 - i))))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat 10827) um0 q (maxWord :: rest))
      (chainState s (UInt256.ofNat 10845)
        (SquareModel.l1StepOn ⟨Exp.storeWord um0 2208 (UInt256.ofNat 0), UInt256.ofNat 0⟩ q 1280 4 0)
        q rest) := by
  have hs := hslot 4 (by omega)
  have hxu : MachineState.readWord (Exp.storeWord um0 2208 (UInt256.ofNat 0)) (1280 + 32 * (7 - 4)) =
      MachineState.readWord um0 (1280 + 32 * (4 - 1 - 0)) :=
    Exp.storeWord_readWord_disjoint um0 _ _ _ (Or.inl (by omega))
  rw [hxu] at hs
  have hx : rest[(6 : Fin 16).val - 2]? =
      some (MachineState.readWord (⟨um0, UInt256.ofNat 0⟩ : MacState).memory (1280 + 32 * (4 - 1 - 0))) := hs
  have h := run_ride_top_np_stale s (UInt256.ofNat 10827) ⟨um0, UInt256.ofNat 0⟩ q 4 0 2208 6
      (by decide) (MachineState.readWord um0 (1280 + 32 * (4 - 1 - 0))) rfl
      rest hrest (by decide) (by omega) hx (by decide) hact (by decide) (by decide)
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.reduceAdd] at h
  have he := l1StepOn_stale um0 q 4 0
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at he
  rw [he]
  exact zero4Block.steps (environment (setupState s (UInt256.ofNat 10827) um0 q (maxWord :: rest))
    hcode hfork hrun hnp) rfl h

/-- **The section on a stale top limb.**  Same conclusion as `gasSteps_macChain` on
`um = storeWord um0 (2080 + 32 n) 0`, started from memory `um0`. -/
def gasSteps_macChain_stale (n : Nat) (hn : n = 4 ∨ n = 8) (s : State) (um0 um : ByteArray)
    (hum : um = Exp.storeWord um0 (2080 + 32 * n) (UInt256.ofNat 0)) (q : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1014) (hlong : 9 ≤ rest.length)
    (hslot : ∀ i : Nat, i < 7 → rest[8 - i]? =
      some (MachineState.readWord um (1280 + 32 * (7 - i))))
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (setupState s (UInt256.ofNat (sectionPC n)) um0 q (maxWord :: rest))
      (chainState s (UInt256.ofNat (sectionEndPC n)) (l1Step um q 1280 n n) q rest) :=
  if h4 : n = 4 then by
    subst h4
    have hum' : um = Exp.storeWord um0 2208 (UInt256.ofNat 0) := hum
    subst hum'
    have hz := gasSteps_zero4_stale s um0 q rest hrest hlong hslot hrun hcode hfork hnp hact
    have hread : ∀ i : Nat, i < 7 →
        MachineState.readWord (SquareModel.l1StepOn
          ⟨Exp.storeWord um0 2208 (UInt256.ofNat 0), UInt256.ofNat 0⟩ q 1280 4 0).memory
          (1280 + 32 * (7 - i)) =
        MachineState.readWord (Exp.storeWord um0 2208 (UInt256.ofNat 0)) (1280 + 32 * (7 - i)) := by
      intro i hi
      rw [l1StepOn_readWord_below ⟨Exp.storeWord um0 2208 (UInt256.ofNat 0), UInt256.ofNat 0⟩
        q 1280 4 0 (1280 + 32 * (7 - i)) (by omega)]
    have hr := gasSteps_runC 3 5 rfl s (SquareModel.l1StepOn
        ⟨Exp.storeWord um0 2208 (UInt256.ofNat 0), UInt256.ofNat 0⟩ q 1280 4 0) q 4 (0 + 1)
      rest (Exp.storeWord um0 2208 (UInt256.ofNat 0)) hrest hlong hslot hread hrun hcode hfork hnp hact
      (by decide) rfl
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by decide) (by decide)
    rw [← l1Run_succ_left] at hr
    have hE : sectionEndPC 4 = 10945 := rfl
    rw [hE]
    exact (hz.trans hr).cast rfl (by rw [SquareModel.l1Step_eq_l1Run])
  else by
    have h8 : n = 8 := by omega
    subst h8
    have hum' : um = Exp.storeWord um0 2336 (UInt256.ofNat 0) := hum
    subst hum'
    have hb0 := gasSteps_block0_stale s um0 q rest hrest hlong hslot hrun hcode hfork hnp hact
    have hread : ∀ i : Nat, i < 7 →
        MachineState.readWord (SquareModel.l1StepOn
          ⟨Exp.storeWord um0 2336 (UInt256.ofNat 0), UInt256.ofNat 0⟩ q 1280 8 0).memory
          (1280 + 32 * (7 - i)) =
        MachineState.readWord (Exp.storeWord um0 2336 (UInt256.ofNat 0)) (1280 + 32 * (7 - i)) := by
      intro i hi
      rw [l1StepOn_readWord_below ⟨Exp.storeWord um0 2336 (UInt256.ofNat 0), UInt256.ofNat 0⟩
        q 1280 8 0 (1280 + 32 * (7 - i)) (by omega)]
    have hr := gasSteps_run 7 1 rfl s (SquareModel.l1StepOn
        ⟨Exp.storeWord um0 2336 (UInt256.ofNat 0), UInt256.ofNat 0⟩ q 1280 8 0) q 8 (0 + 1)
      rest (Exp.storeWord um0 2336 (UInt256.ofNat 0)) hrest hlong hslot hread hrun hcode hfork hnp hact
      (by decide) rfl
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by decide)
    rw [← l1Run_succ_left] at hr
    have hE : sectionEndPC 8 = 3034 := rfl
    rw [hE]
    exact ((hb0.trans hr).trans (gasSteps_exit s _ q rest hrest hrun hcode hfork hnp)).cast rfl
      (by rw [SquareModel.l1Step_eq_l1Run])

end CycleSubmission.Global.Fast.M9Mac

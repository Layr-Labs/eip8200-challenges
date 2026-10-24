import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
import Challenge.Modexp.Submission.Proofs.Fast.StagedProduct
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact
import Challenge.Modexp.Submission.Proofs.Fast.LazyCsubTrace
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

/-!
# Eight-limb square rounds without the carry flush

n8g/st8 keep the square's carry word on the stack: the `tn = 0` exit copies `t → a` inline and the
carry continuation stores the row head word (4293) at `0x820` before the subtraction. The round
memory therefore differs from `SquareLoopMem.sqRound` (built on `lift`) only in the word at
`0x820`. `Same A B` says two memories agree outside that word; every later consumer reads its
input through `mpZeroed`, which rewrites `[2048, 2112 + 32 n)`, so `Same` memories give the same
rounds, the same product and the same loop result.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRoundC
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro TnCacheMemory

def Same (A B : ByteArray) : Prop := lift A (UInt256.ofNat 0) = lift B (UInt256.ofNat 0)

theorem Same.refl (A : ByteArray) : Same A A := rfl

theorem Same.symm {A B : ByteArray} (h : Same A B) : Same B A := Eq.symm h

theorem Same.trans {A B C : ByteArray} (h1 : Same A B) (h2 : Same B C) : Same A C := Eq.trans h1 h2

theorem same_lift (A : ByteArray) (v : UInt256) : Same (lift A v) A := by
  unfold Same
  rw [lift_overwrite]

theorem Same.readWord {A B : ByteArray} (h : Same A B) (p : Nat) (hp : p + 32 ≤ 2080 ∨ 2112 ≤ p) :
    MachineState.readWord A p = MachineState.readWord B p := by
  rw [← read_lift_outside A (UInt256.ofNat 0) p hp, ← read_lift_outside B (UInt256.ofNat 0) p hp, h]

theorem writeBytes_lift_absorb (A P : ByteArray) (v : UInt256) (hP : 64 ≤ P.size) :
    MachineState.writeBytes (lift A v) P 2048 = MachineState.writeBytes A P 2048 := by
  apply ByteArray.ext_getElem
  · simp only [lift, MachineState.writeBytes_size, wordBytes_size]
    split_ifs <;> omega
  · intro i h1 h2
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h1,
        ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h2]
    simp only [lift, MachineState.writeBytes_getElem?_getD, wordBytes_size]
    by_cases hi : 2048 ≤ i ∧ i < 2048 + P.size
    · simp only [hi, and_self, if_true]
    · have hj : ¬ (2080 ≤ i ∧ i < 2080 + 32) := by omega
      simp only [hi, hj, if_false]

theorem mpZeroed_lift (s : State) (A : ByteArray) (v : UInt256) (n : Nat) :
    mpZeroed s (lift A v) n = mpZeroed s A n := by
  unfold mpZeroed
  exact writeBytes_lift_absorb A _ v (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)

theorem Same.mpZeroed {A B : ByteArray} (h : Same A B) (s : State) (n : Nat) :
    Monpro.mpZeroed s A n = Monpro.mpZeroed s B n := by
  rw [← mpZeroed_lift s A (UInt256.ofNat 0) n, ← mpZeroed_lift s B (UInt256.ofNat 0) n]
  exact congrArg (fun X => Monpro.mpZeroed s X n) h

theorem Same.sqRound {A B : ByteArray} (h : Same A B) (s : State) (n c : Nat) :
    SquareLoopMem.sqRound s n c A = SquareLoopMem.sqRound s n c B := by
  unfold SquareLoopMem.sqRound
  rw [h.mpZeroed s n]

theorem Same.sqRunMem {A B : ByteArray} (h : Same A B) (s : State) (n k : Nat) (hk : 1 ≤ k) :
    SquareLoopMem.sqRunMem s n k A = SquareLoopMem.sqRunMem s n k B := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [SquareLoopMem.sqRunMem_succ, SquareLoopMem.sqRunMem_succ, h.sqRound s n j]

theorem Same.stagedProduct {A B : ByteArray} (h : Same A B) (s : State) (n : Nat) :
    StagedProduct.memory s A n = StagedProduct.memory s B n := by
  unfold StagedProduct.memory
  rw [h.mpZeroed s n]

theorem Same.scratchZero {A B : ByteArray} (h : Same A B) (hB : R8RowZeroExact.ScratchZero B) :
    R8RowZeroExact.ScratchZero A := by
  intro i hlo hhi
  have hl : (lift A (UInt256.ofNat 0))[i]?.getD 0 = (lift B (UInt256.ofNat 0))[i]?.getD 0 := by
    rw [h]
  simp only [lift, MachineState.writeBytes_getElem?_getD, wordBytes_size,
    show ¬ (2080 ≤ i ∧ i < 2080 + 32) from by omega, if_false] at hl
  rw [hl]
  exact hB i hlo hhi

theorem csStep_lift (M : ByteArray) (v : UInt256) (n : Nat) (hn : n ≤ 8) :
    ∀ j, j ≤ n → Csub.csStep (lift M v) n j =
      ⟨lift (Csub.csStep M n j).memory v, (Csub.csStep M n j).flag⟩
  | 0, _ => rfl
  | j + 1, hj => by
      have ih := csStep_lift M v n hn j (by omega)
      simp only [Csub.csStep, ih]
      rw [read_lift_outside _ _ _ (Or.inr (by omega)), read_lift_outside _ _ _ (Or.inl (by omega))]
      congr 1
      exact (lift_put _ v _ _ (Or.inl (by omega))).symm


theorem lift_writeBytes (A P : ByteArray) (v : UInt256) (a : Nat) (hP : P.size ≠ 0)
    (hd : a + P.size ≤ 2080 ∨ 2112 ≤ a) :
    lift (MachineState.writeBytes A P a) v = MachineState.writeBytes (lift A v) P a := by
  have hw : (Data.Bytes.natToBytesPadded v.toNat 32).size = 32 := wordBytes_size v
  have hsize : (lift (MachineState.writeBytes A P a) v).size =
      (MachineState.writeBytes (lift A v) P a).size := by
    simp only [lift, MachineState.writeBytes_size, hw, if_neg hP]
    split_ifs <;> omega
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  simp only [lift, MachineState.writeBytes_getElem?_getD, hw]
  split_ifs <;> first | rfl | omega

theorem readPadded_lift (A : ByteArray) (v : UInt256) (a k : Nat) (hd : a + k ≤ 2080 ∨ 2112 ≤ a) :
    MachineState.readPadded (lift A v) a k = MachineState.readPadded A a k :=
  Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint _ _ _ _ _
    (by rw [wordBytes_size]; omega)

def copy8 (A : ByteArray) : ByteArray :=
  MachineState.writeBytes A (MachineState.readPadded A 2112 256) 2368

theorem copy8_lift (A : ByteArray) (v : UInt256) : copy8 (lift A v) = lift (copy8 A) v := by
  unfold copy8
  rw [readPadded_lift A v 2112 256 (Or.inr le_rfl),
    lift_writeBytes _ _ v 2368 (by rw [Challenge.EvmProof.Memory.readPadded_size]; decide)
      (Or.inr (by decide))]

def sub8 (A : ByteArray) : ByteArray :=
  MachineState.writeBytes (Csub.csStep A 8 8).memory
    (MachineState.readPadded (Csub.csStep A 8 8).memory 1792 (32 * 8)) 2368

theorem sub8_lift (A : ByteArray) (v : UInt256) : sub8 (lift A v) = lift (sub8 A) v := by
  unfold sub8
  rw [csStep_lift A v 8 (by decide) 8 le_rfl]
  dsimp only
  rw [readPadded_lift _ v 1792 (32 * 8) (Or.inl (by decide)),
    lift_writeBytes _ _ v 2368 (by rw [Challenge.EvmProof.Memory.readPadded_size]; decide)
      (Or.inr (by decide))]


theorem copy8_readWord (A : ByteArray) (addr : Nat) (hd : addr + 32 ≤ 2368 ∨ 2624 ≤ addr) :
    MachineState.readWord (copy8 A) addr = MachineState.readWord A addr :=
  Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)

theorem sub8_readWord (A : ByteArray) (addr : Nat) (hd : addr + 32 ≤ 1792 ∨ 2624 ≤ addr) :
    MachineState.readWord (sub8 A) addr = MachineState.readWord A addr := by
  unfold sub8
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)]
  exact Csub.csStep_readWord_disjoint A 8 addr (by decide) (by omega) 8 le_rfl

theorem same_copy (F : ByteArray) :
    Same (copy8 F) (LazyCsub.resultMemory (lift F (UInt256.ofNat 0)) 8 2368) := by
  have h0 : (MachineState.readWord (lift F (UInt256.ofNat 0)) 2080).toNat = 0 := by
    rw [read_lift]; decide
  unfold LazyCsub.resultMemory
  rw [if_pos h0, show 32 * 8 = 256 from rfl]
  change Same (copy8 F) (copy8 (lift F (UInt256.ofNat 0)))
  rw [copy8_lift]
  exact (same_lift _ _).symm

theorem same_sub (F : ByteArray) (w : UInt256) :
    Same (sub8 (lift F w)) (LazyCsub.resultMemory (lift F (UInt256.ofNat 1)) 8 2368) := by
  have h1 : (MachineState.readWord (lift F (UInt256.ofNat 1)) 2080).toNat = 1 := by
    rw [read_lift]; decide
  have htn : (MachineState.readWord (Csub.csStep (lift F (UInt256.ofNat 1)) 8 8).memory 2080).toNat ≤ 1 := by
    rw [Csub.csStep_readWord_disjoint _ 8 2080 (by decide) (Or.inr (by decide)) 8 le_rfl, h1]
  have huse : (Csub.csUse (lift F (UInt256.ofNat 1)) 8 8).toNat ≠ 0 := by
    rw [Csub.csUse_toNat _ 8 8 htn, Csub.csStep_readWord_disjoint _ 8 2080 (by decide)
      (Or.inr (by decide)) 8 le_rfl, h1]
    omega
  unfold LazyCsub.resultMemory Csub.subResultMemory
  rw [if_neg (by rw [h1]; decide), Csub.csSrc_toNat _ 8 8 (Csub.csUse_le_one _ 8 8 htn), if_neg huse]
  change Same (sub8 (lift F w)) (sub8 (lift F (UInt256.ofNat 1)))
  rw [sub8_lift, sub8_lift]
  exact (same_lift _ _).trans (same_lift _ _).symm

def gasSteps_lazyFlag8 (s : State) (X : ByteArray) (ret : UInt256) (tail : List UInt256)
    (hcap : tail.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs : MachineState.readWord X 2688 = UInt256.ofNat (32 * 8))
    (hflag : (MachineState.readWord X 2080).toNat ≠ 0) :
    Challenge.EvmProof.GasSteps (LazyGate.atState s X 4214 (UInt256.ofNat 2368) ret tail)
      { s with pc := ret, stack := tail, memory := sub8 X } := by
  have env := SquareRow.environment s hcode hfork hrun hnp
  have hc := LazyCsub.gateBlock.steps
    (env.transfer (t := LazyGate.atState s X 4214 (UInt256.ofNat 2368) ret tail) rfl rfl) rfl
    (LazyGate.run_gate s X (UInt256.ofNat 2368) ret tail hcap hact
      (by simpa only [hcode] using jumpDestSub))
  rw [if_neg hflag] at hc
  have hE := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Challenge.Modexp.Submission.Proofs.Bytecode.Artifact.submissionArtifact .Osaka Challenge.Modexp.Submission.Proofs.Fast.csFixedEntry8
    (by simpa [Csub.subEntryState,
      Challenge.Modexp.Submission.Proofs.Bytecode.Artifact.submissionArtifact] using hcode)
    (by simpa [Csub.subEntryState, State.fork] using hfork)
    (Csub.run_csFixedEntry8 s X (UInt256.ofNat 2368) ret tail hcap hrun hcode hact hs)
    (by simpa [Csub.subEntryState] using hrun)
    (by simpa [Csub.subEntryState, State.fork] using hnp)
  have hs32 : MachineState.readWord (Csub.csStep X 8 8).memory 2688 = UInt256.ofNat (32 * 8) := by
    rw [Csub.csStep_readWord_disjoint X 8 2688 (by decide) (Or.inr (by decide)) 8 le_rfl]; exact hs
  have hflag' : (MachineState.readWord (Csub.csStep X 8 8).memory 2080).toNat ≠ 0 := by
    rw [Csub.csStep_readWord_disjoint X 8 2080 (by decide) (Or.inr (by decide)) 8 le_rfl]; exact hflag
  have hF := Csub.gasSteps_csFixedFrom8Flag s X (UInt256.ofNat 2368) ret tail hcap hrun hcode hact
    hfork hnp hjump hs32 (by decide) hflag'
  exact ((hc.cast rfl rfl).trans (hE.cast rfl rfl)).trans hF

end Challenge.Modexp.Submission.Proofs.Fast.SquareRoundC

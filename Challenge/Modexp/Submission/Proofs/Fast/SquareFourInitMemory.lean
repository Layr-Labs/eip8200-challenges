import Challenge.Modexp.Submission.Proofs.Fast.SquareFourInitCore
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourInit
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open SquareWords Monpro
open _root_.Challenge.Modexp.Submission.Proofs.Fast.SquareInit (storeWord)

def digitAddr (j : Nat) : Nat := 2400+32*(3-j)

theorem read_storeWord_outside (mem : ByteArray) (dst addr : Nat) (x : UInt256)
    (hd : addr+32 ≤ dst ∨ dst+32 ≤ addr) :
    MachineState.readWord (storeWord mem dst x) addr = MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hd

@[simp] theorem read_storeWord (mem : ByteArray) (dst : Nat) (x : UInt256) :
    MachineState.readWord (storeWord mem dst x) dst = x :=
  Challenge.EvmProof.Memory.readWord_writeWord mem dst x

theorem read_doubleWords_keep (mem : ByteArray) (k : Nat) (hk : k < 4) :
    ∀ j, j ≤ k →
      MachineState.readWord (doubleWords mem j).memory (digitAddr k) =
        MachineState.readWord mem (digitAddr k) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    simp only [doubleWords]
    rw [read_storeWord_outside]
    · exact ih (by omega)
    · left; simp only [digitAddr]; omega

def doubleDigit (mem : ByteArray) (j : Nat) : UInt256 :=
  doubled (MachineState.readWord mem (digitAddr j)) (doubleWords mem j).carry

theorem doubleWords_succ (mem : ByteArray) (j : Nat) (hj : j < 4) :
    doubleWords mem (j+1) =
      ⟨storeWord (doubleWords mem j).memory (digitAddr j) (doubleDigit mem j),
       highBit (MachineState.readWord mem (digitAddr j))⟩ := by
  have hread := read_doubleWords_keep mem j hj j le_rfl
  simp only [digitAddr] at hread
  simp only [doubleWords]
  rw [hread]
  rfl

theorem read_doubleWords_val (mem : ByteArray) (k : Nat) (hk : k < 4) :
    ∀ j, k < j → j ≤ 4 →
      MachineState.readWord (doubleWords mem j).memory (digitAddr k) = doubleDigit mem k := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hkj hj
    rw [doubleWords_succ mem j (by omega)]
    dsimp only
    by_cases he : k = j
    · subst k; exact read_storeWord _ _ _
    · rw [read_storeWord_outside]
      · exact ih (by omega) (by omega)
      · right; simp only [digitAddr]; omega

theorem read_doubleWords_outside (mem : ByteArray) (addr : Nat)
    (hd : addr+32 ≤ 2400 ∨ 2528 ≤ addr) :
    ∀ j, j ≤ 4 →
      MachineState.readWord (doubleWords mem j).memory addr = MachineState.readWord mem addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [doubleWords_succ mem j (by omega)]
    dsimp only
    rw [read_storeWord_outside]
    · exact ih (by omega)
    · simp only [digitAddr]; omega

theorem carry_bound (mem : ByteArray) (j : Nat) : (doubleWords mem j).carry.toNat < 2 := by
  cases j with
  | zero => simp [doubleWords]
  | succ j => exact highBit_lt_two _

theorem doubleWords_invariant (mem : ByteArray) :
    ∀ j, j ≤ 4 →
      limbSum (fun k => (doubleDigit mem k).toNat) j +
        (doubleWords mem j).carry.toNat * Limbs.radix^j =
      2*limbSum (fun k => (MachineState.readWord mem (digitAddr k)).toNat) j := by
  intro j
  induction j with
  | zero => intro _; simp [limbSum, doubleWords]
  | succ j ih =>
    intro hj
    have prev := ih (by omega)
    have cur := doubled_spec (MachineState.readWord mem (digitAddr j))
      (doubleWords mem j).carry (carry_bound mem j)
    change (highBit (MachineState.readWord mem (digitAddr j))).toNat * Limbs.radix +
      (doubleDigit mem j).toNat =
      2*(MachineState.readWord mem (digitAddr j)).toNat + (doubleWords mem j).carry.toNat at cur
    rw [limbSum_succ, limbSum_succ, doubleWords_succ mem j (by omega), pow_succ]
    dsimp only
    calc
      _ = limbSum (fun k => (doubleDigit mem k).toNat) j +
          ((highBit (MachineState.readWord mem (digitAddr j))).toNat * Limbs.radix +
            (doubleDigit mem j).toNat)*Limbs.radix^j := by ring
      _ = limbSum (fun k => (doubleDigit mem k).toNat) j +
          (2*(MachineState.readWord mem (digitAddr j)).toNat +
            (doubleWords mem j).carry.toNat)*Limbs.radix^j := by rw [cur]
      _ = (limbSum (fun k => (doubleDigit mem k).toNat) j +
          (doubleWords mem j).carry.toNat*Limbs.radix^j) +
            2*(MachineState.readWord mem (digitAddr j)).toNat*Limbs.radix^j := by ring
      _ = _ := by rw [prev]; ring

theorem read_init_low (mem : ByteArray) (j : Nat) (hj : j < 4) :
    MachineState.readWord (initMemory mem) (digitAddr j) = doubleDigit mem j := by
  rw [initMemory, read_storeWord_outside, read_storeWord_outside]
  · exact read_doubleWords_val mem j hj 4 hj le_rfl
  · simp only [digitAddr]; right; omega
  · simp only [digitAddr]; left; omega

theorem read_init_high (mem : ByteArray) :
    MachineState.readWord (initMemory mem) 2368 = (doubleWords mem 4).carry := by
  rw [initMemory, read_storeWord_outside _ _ _ _ (Or.inl (by decide)), read_storeWord]

theorem read_init_route (mem : ByteArray) :
    MachineState.readWord (initMemory mem) 2720 = UInt256.ofNat 5191 := by
  exact read_storeWord _ _ _

theorem read_init_outside (mem : ByteArray) (addr : Nat)
    (hd : addr+32 ≤ 2368 ∨ 2752 ≤ addr) :
    MachineState.readWord (initMemory mem) addr = MachineState.readWord mem addr := by
  rw [initMemory, read_storeWord_outside _ _ _ _ (by omega),
    read_storeWord_outside _ _ _ _ (by omega)]
  exact read_doubleWords_outside mem addr (by omega) 4 le_rfl

attribute [local irreducible] doubleWords initMemory

/-- The concrete in-place doubling pass prepares a five-limb value equal to `2*a`. -/
theorem init_represents (mem : ByteArray) (a : Nat)
    (ha : Model.FastRepresents mem 2400 4 a) :
    Model.FastRepresents (initMemory mem) 2368 5 (2*a) := by
  have hv := doubleWords_invariant mem 4 le_rfl
  have hsrc : limbSum (fun k => (MachineState.readWord mem (digitAddr k)).toNat) 4 = a :=
    limbSum_fastRepresents (mem := mem) (ptr := 2400) (count := 4) (value := a) ha
  rw [hsrc] at hv
  have hval : Csub.lowValue (initMemory mem) 2368 5 5 = 2*a := by
    rw [← limbSum_eq_lowValue, limbSum_succ]
    have hlo : limbSum (fun k =>
          (MachineState.readWord (initMemory mem) (2368+32*(5-1-k))).toNat) 4 =
        limbSum (fun k => (doubleDigit mem k).toNat) 4 := by
      apply limbSum_congr
      intro k hk
      have hp : 2368+32*(5-1-k) = digitAddr k := by simp only [digitAddr]; omega
      rw [hp, read_init_low mem k hk]
    rw [hlo]
    norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
    rw [read_init_high]
    exact hv
  rw [← hval]
  exact Csub.fastRepresents_lowValue _ _ _

end Challenge.Modexp.Submission.Proofs.Fast.SquareFourInit

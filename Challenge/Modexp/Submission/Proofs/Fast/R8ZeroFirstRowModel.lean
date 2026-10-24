import Challenge.Modexp.Submission.Proofs.Fast.R4Math
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroCore

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel CarryScratchAgreement

/-- Equality outside the still-uninitialized portion of T. -/
def EqFrom (cut : Nat) (a b : ByteArray) : Prop :=
  ∀ i, i < 2048 ∨ cut ≤ i → a[i]?.getD 0 = b[i]?.getD 0

theorem eqFrom_read {cut : Nat} {a b : ByteArray} (h : EqFrom cut a b)
    (addr : Nat) (hout : addr + 32 ≤ 2048 ∨ cut ≤ addr) :
    MachineState.readWord a addr = MachineState.readWord b addr := by
  have hp : MachineState.readPadded a addr 32 = MachineState.readPadded b addr 32 := by
    apply Challenge.EvmProof.Memory.readPadded_congr
    intro i hi
    exact h (addr + i) (by omega)
  unfold MachineState.readWord
  rw [hp]

theorem eqFrom_store {cut : Nat} {a b : ByteArray} (h : EqFrom (cut + 32) a b)
    (hcut : 2048 ≤ cut) (w : UInt256) :
    EqFrom cut
      (MachineState.writeBytes a (Data.Bytes.natToBytesPadded w.toNat 32) cut)
      (MachineState.writeBytes b (Data.Bytes.natToBytesPadded w.toNat 32) cut) := by
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD, MachineState.writeBytes_getElem?_getD]
  split
  · rfl
  · apply h i
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] at *
    omega

theorem eqFrom_zeroed (s : State) (mem : ByteArray) :
    EqFrom 2368 mem (mpZeroed s mem 8) := by
  intro i hi
  simp only [mpZeroed, MachineState.writeBytes_getElem?_getD,
    Challenge.EvmProof.Memory.readPadded_size]
  rw [if_neg (by omega)]

def diagonal (mem : ByteArray) : MacState :=
  let x := MachineState.readWord mem 2592
  { memory := MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (x*x).toNat 32) 2336
    carry := mulHi x x }

def zeroStep (q : MacState) (bi : UInt256) (j : Nat) : MacState :=
  let x := MachineState.readWord q.memory (aAddr 8 j)
  { memory := MachineState.writeBytes q.memory
      (Data.Bytes.natToBytesPadded (R4Math.zSum x bi q.carry).toNat 32) (tAddr 8 j)
    carry := R4Math.zCarry x bi q.carry maxWord }

def zeroRun (q : MacState) (bi : UInt256) : Nat → MacState
  | 0 => q
  | k+1 => zeroStep (zeroRun q bi k) bi (k+1)

def firstProduct (mem : ByteArray) : MacState :=
  zeroRun (diagonal mem) (MachineState.readWord mem 2592 + MachineState.readWord mem 2592) 7

def firstMemory (mem : ByteArray) : ByteArray :=
  MachineState.writeBytes (firstProduct mem).memory
    (Data.Bytes.natToBytesPadded (firstProduct mem).carry.toNat 32) 2080

theorem zeroStep_bridge (qa qb : MacState) (bi : UInt256) (j : Nat)
    (hj : j < 8)
    (heq : EqFrom (tAddr 8 j + 32) qa.memory qb.memory)
    (hc : qa.carry = qb.carry)
    (hz : MachineState.readWord qb.memory (tAddr 8 j) = UInt256.ofNat 0) :
    EqFrom (tAddr 8 j) (zeroStep qa bi j).memory (l1StepOn qb bi 2368 8 j).memory ∧
      (zeroStep qa bi j).carry = (l1StepOn qb bi 2368 8 j).carry := by
  have hx := eqFrom_read heq (aAddr 8 j) (Or.inr (by unfold aAddr tAddr; omega))
  simp only [zeroStep, l1StepOn, aAddr, tAddr] at hx hz ⊢
  rw [hx, hc, hz, R4Math.zSum_eq, R4Math.zCarry_eq]
  exact ⟨eqFrom_store heq (by unfold tAddr; omega) _, rfl⟩

theorem readWord_l1Run_below (q : MacState) (bi : UInt256) (addr k : Nat)
    (hk : k ≤ 7) (ha : addr + 32 ≤ tAddr 8 k) :
    MachineState.readWord (l1Run q bi 2368 8 1 k).memory addr =
      MachineState.readWord q.memory addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [l1Run_succ, readWord_l1StepOn_disj _ _ _ _ _ _ (Or.inl (by
        simpa [tAddr, Nat.add_comm] using ha))]
      apply ih (by omega)
      unfold tAddr at *
      omega

theorem add_zero_word (a : UInt256) : a + UInt256.ofNat 0 = a := by
  rw [Challenge.EvmProof.Word.word_add_comm]
  exact R4Math.zero_add_w a

theorem zero_add_word (a : UInt256) : UInt256.ofNat 0 + a = a :=
  R4Math.zero_add_w a

theorem lt_self_word (a : UInt256) : UInt256.lt a a = UInt256.ofNat 0 := by
  simp [UInt256.lt]

theorem diagHi_self (a : UInt256) : SquareDiag.diagHi a a = mulHi a a := by
  have h := SquareDiag.diag_spec a (UInt256.ofNat 0) (by decide)
  rw [add_zero_word] at h
  have hn : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [hn, Nat.add_zero] at h
  exact (R4Math.pair_unique (h.trans (mulHi_spec a a).symm)).1

theorem diagonal_eq_sqPro (mem : ByteArray)
    (hz : MachineState.readWord mem 2336 = UInt256.ofNat 0) :
    diagonal mem = sqPro mem 8 0 (UInt256.ofNat 0) := by
  simp only [diagonal, sqPro, sqSum, sqCarry, sqLo, sqHi, sqX, aAddr, tAddr,
    Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, hz, add_zero_word,
    lt_self_word, diagHi_self, zero_add_word]

theorem diagonal_bridge (s : State) (mem : ByteArray) :
    EqFrom 2336 (diagonal mem).memory (sqPro (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory ∧
      (diagonal mem).carry = (sqPro (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry := by
  have hz := readWord_mpZeroed_zero s mem 8 2336 (by decide) (by decide)
  rw [← diagonal_eq_sqPro _ hz]
  have heq := eqFrom_zeroed s mem
  have hx := eqFrom_read heq 2592 (Or.inr (by decide))
  simp only [diagonal, hx]
  exact ⟨eqFrom_store heq (by decide) _, trivial⟩

theorem old_next_zero (s : State) (mem : ByteArray) (bi : UInt256) (k : Nat)
    (hk : k < 7) :
    MachineState.readWord
      (l1Run (sqPro (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)) bi 2368 8 1 k).memory
      (tAddr 8 (k+1)) = UInt256.ofNat 0 := by
  rw [readWord_l1Run_below _ _ _ k (by omega) (by unfold tAddr; omega)]
  rw [readWord_sqPro_disj _ _ _ _ _ (Or.inl (by unfold tAddr; omega))]
  exact readWord_mpZeroed_zero s mem 8 _ (by unfold tAddr; omega) (by unfold tAddr; omega)

theorem zeroRun_bridge (s : State) (mem : ByteArray) (bi : UInt256) :
    ∀ k, k ≤ 7 →
      EqFrom (tAddr 8 k)
        (zeroRun (diagonal mem) bi k).memory
        (l1Run (sqPro (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)) bi 2368 8 1 k).memory ∧
      (zeroRun (diagonal mem) bi k).carry =
        (l1Run (sqPro (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)) bi 2368 8 1 k).carry := by
  intro k
  induction k with
  | zero => intro _; exact diagonal_bridge s mem
  | succ k ih =>
      intro hk
      have prev := ih (by omega)
      have hcut : tAddr 8 (k+1) + 32 = tAddr 8 k := by unfold tAddr; omega
      have h := zeroStep_bridge _ _ bi (k+1) (by omega)
        (by rw [hcut]; exact prev.1) prev.2 (old_next_zero s mem bi k (by omega))
      simpa only [zeroRun, l1Run_succ, Nat.add_comm 1 k] using h

theorem firstProduct_bridge (s : State) (mem : ByteArray) :
    EqFrom 2112 (firstProduct mem).memory (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory ∧
      (firstProduct mem).carry = (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry := by
  have hx := eqFrom_read (eqFrom_zeroed s mem) 2592 (Or.inr (by decide))
  have h := zeroRun_bridge s mem
    (MachineState.readWord mem 2592 + MachineState.readWord mem 2592) 7 (by decide)
  simpa only [firstProduct, sqL1, sqB2, sqX, aAddr, tAddr,
    Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, add_zero_word, ← hx] using h

/-- The exact bridge needed before the existing L2 code. The sole permitted
memory discrepancy is the old return/overflow scratch word2048..2079. -/
theorem firstMemory_bridge (s : State) (mem : ByteArray) :
    Agree (firstMemory mem)
      (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
        (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry) := by
  have h := firstProduct_bridge s mem
  have hz : MachineState.readWord (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 2080 =
      UInt256.ofNat 0 := by
    rw [readWord_sqL1 _ 8 0 2080 _ (by decide) (Or.inl (by decide))]
    exact readWord_mpZeroed_tn s mem 8
  unfold firstMemory midMem1
  rw [hz, zero_add_word, h.2]
  exact eqFrom_store h.1 (by decide) _

#print axioms firstMemory_bridge

end Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow

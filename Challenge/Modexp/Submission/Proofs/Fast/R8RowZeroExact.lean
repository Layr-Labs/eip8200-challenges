import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult
import Challenge.Modexp.Submission.Proofs.Fast.StagedMonpro
import Challenge.Modexp.Submission.Proofs.Fast.CsubCore

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# The first row of a square: exact memory bridge

`R8ZeroFirstRow.firstMemory_bridge` relates the machine memory after the eight-limb
first-row program to the machine-carry row model `midMem1 (sqL1 (mpZeroed s mem 8) 8 0 0)`
up to the scratch word `[2048, 2080)`.  In the square loop that scratch word is zero at
every row-0 entry (the exponentiation entry zero-fills it, and nothing in a round writes
it), so the two memories are *equal*.  This module proves that equality and the
invariance of the zero scratch word under every memory operation of a round.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult CarryRowModel CarryScratchAgreement

/-- The scratch word `[2048, 2080)` (the pure model's `t[n+1]` slot) is all zero. -/
def ScratchZero (mem : ByteArray) : Prop :=
  ∀ i, 2048 ≤ i → i < 2080 → mem[i]?.getD 0 = 0

theorem ScratchZero.write {mem : ByteArray} (h : ScratchZero mem) (bytes : ByteArray)
    (start : Nat) (hout : start + bytes.size ≤ 2048 ∨ 2080 ≤ start) :
    ScratchZero (MachineState.writeBytes mem bytes start) := by
  intro i hlo hhi
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega)]
  exact h i hlo hhi

theorem ScratchZero.store {mem : ByteArray} (h : ScratchZero mem) (w start : Nat)
    (hout : start + 32 ≤ 2048 ∨ 2080 ≤ start) :
    ScratchZero (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) start) :=
  h.write _ start (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; exact hout)

theorem scratchZero_mpZeroed (s : State) (mem : ByteArray) (n : Nat) (hn : 1 ≤ n) :
    ScratchZero (mpZeroed s mem n) := by
  intro i hlo hhi
  simp only [mpZeroed, MachineState.writeBytes_getElem?_getD,
    Challenge.EvmProof.Memory.readPadded_size]
  rw [if_pos (by omega), Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega)]
  exact Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by omega)

/-! ## The machine-carry row model never writes the scratch word -/

theorem ScratchZero.sqPro {mem : ByteArray} (h : ScratchZero mem) (n i : Nat) (tb : UInt256) :
    ScratchZero (sqPro mem n i tb).memory :=
  h.store _ _ (Or.inr (by unfold tAddr; omega))

theorem ScratchZero.l1StepOn {q : MacState} (h : ScratchZero q.memory) (bi : UInt256)
    (pa n j : Nat) : ScratchZero (l1StepOn q bi pa n j).memory :=
  h.store _ _ (Or.inr (by omega))

theorem ScratchZero.l1Run {q : MacState} (h : ScratchZero q.memory) (bi : UInt256)
    (pa n j0 : Nat) : ∀ k, ScratchZero (l1Run q bi pa n j0 k).memory
  | 0 => h
  | k + 1 => (ScratchZero.l1Run h bi pa n j0 k).l1StepOn bi pa n (j0 + k)

theorem ScratchZero.sqL1 {mem : ByteArray} (h : ScratchZero mem) (n i : Nat) (tb : UInt256) :
    ScratchZero (sqL1 mem n i tb).memory :=
  (h.sqPro n i tb).l1Run _ 2368 n (i + 1) (n - 1 - i)

theorem ScratchZero.midMem1 {mem : ByteArray} (h : ScratchZero mem) (c : UInt256) :
    ScratchZero (midMem1 mem c) :=
  h.store _ 2080 (Or.inr (by decide))

theorem ScratchZero.l2Step {mem : ByteArray} (h : ScratchZero mem) (mu c0 : UInt256) (n : Nat) :
    ∀ k, ScratchZero (l2Step mem mu c0 n k).memory
  | 0 => h
  | k + 1 => (ScratchZero.l2Step h mu c0 n k).store _ _ (Or.inr (by omega))

theorem ScratchZero.tailMem1 {mem : ByteArray} (h : ScratchZero mem) (c : UInt256) :
    ScratchZero (tailMem1 mem c) :=
  h.store _ 2112 (Or.inr (by decide))

theorem ScratchZero.tailCarry {mem : ByteArray} (h : ScratchZero mem) (c f : UInt256) :
    ScratchZero (tailCarry mem c f) :=
  (h.tailMem1 c).store _ 2080 (Or.inr (by decide))

theorem ScratchZero.rowFromCarry {q : MacState} (h : ScratchZero q.memory) (n : Nat) :
    ScratchZero (rowFromCarry q n) :=
  ((h.midMem1 q.carry).l2Step (rowMu q.memory n) (rowC0 q.memory n) n (n - 1)).tailCarry _ _

theorem ScratchZero.sqRowCarry {mem : ByteArray} (h : ScratchZero mem) (n i : Nat)
    (tb : UInt256) : ScratchZero (sqRowCarry mem n i tb) :=
  (h.sqL1 n i tb).rowFromCarry n

theorem ScratchZero.sqRowsCarry {mem : ByteArray} (h : ScratchZero mem) (n : Nat) :
    ∀ i, ScratchZero (sqRowsCarry mem n i)
  | 0 => h
  | i + 1 => (ScratchZero.sqRowsCarry h n i).sqRowCarry n i _

/-- The CSUB limb loop writes its differences at `1792 + 32 * (n - 1 - j)`, below 2048. -/
theorem ScratchZero.csStep {mem : ByteArray} (h : ScratchZero mem) (n : Nat) (hn : n ≤ 8) :
    ∀ j, ScratchZero (Csub.csStep mem n j).memory
  | 0 => h
  | j + 1 => (ScratchZero.csStep h n hn j).store _ _ (Or.inl (by omega))

/-! ## The first-row program never writes the scratch word -/

theorem ScratchZero.diagonal {mem : ByteArray} (h : ScratchZero mem) :
    ScratchZero (R8ZeroFirstRow.diagonal mem).memory :=
  h.store _ 2336 (Or.inr (by decide))

theorem ScratchZero.zeroStep {q : MacState} (h : ScratchZero q.memory) (bi : UInt256) (j : Nat) :
    ScratchZero (R8ZeroFirstRow.zeroStep q bi j).memory :=
  h.store _ _ (Or.inr (by unfold tAddr; omega))

theorem ScratchZero.zeroRun {q : MacState} (h : ScratchZero q.memory) (bi : UInt256) :
    ∀ k, ScratchZero (R8ZeroFirstRow.zeroRun q bi k).memory
  | 0 => h
  | k + 1 => (ScratchZero.zeroRun h bi k).zeroStep bi (k + 1)

theorem ScratchZero.firstMemory {mem : ByteArray} (h : ScratchZero mem) :
    ScratchZero (R8ZeroFirstRow.firstMemory mem) :=
  (h.diagonal.zeroRun _ 7).store _ 2080 (Or.inr (by decide))


/-! ## Sizes: every write of the row lands inside `[2080, 2368)` once the array is that long -/

theorem size_store_of_le (bs : ByteArray) (w start : Nat) (h : start + 32 ≤ bs.size) :
    (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded w 32) start).size = bs.size := by
  rw [MachineState.writeBytes_size, YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    if_neg (by decide)]
  exact Nat.max_eq_left h

theorem size_mpZeroed8 (s : State) (mem : ByteArray) :
    (mpZeroed s mem 8).size = max mem.size 2368 := by
  simp only [mpZeroed]
  rw [MachineState.writeBytes_size, Challenge.EvmProof.Memory.readPadded_size, if_neg (by decide)]

theorem size_sqPro (mem : ByteArray) (n i : Nat) (tb : UInt256) (h : tAddr n i + 32 ≤ mem.size) :
    (sqPro mem n i tb).memory.size = mem.size :=
  size_store_of_le _ _ _ h

theorem size_l1Run (q : MacState) (bi : UInt256) (pa n j0 : Nat) (hn : n ≤ 8)
    (hq : 2368 ≤ q.memory.size) :
    ∀ k, (l1Run q bi pa n j0 k).memory.size = q.memory.size
  | 0 => rfl
  | k + 1 => by
    show (MachineState.writeBytes (l1Run q bi pa n j0 k).memory _
      (2112 + 32 * (n - 1 - (j0 + k)))).size = q.memory.size
    rw [size_store_of_le _ _ _ (by rw [size_l1Run q bi pa n j0 hn hq k]; omega),
      size_l1Run q bi pa n j0 hn hq k]

theorem size_midMem1 (mem : ByteArray) (c : UInt256) (h : 2112 ≤ mem.size) :
    (midMem1 mem c).size = mem.size :=
  size_store_of_le _ _ _ h

theorem size_model (s : State) (mem : ByteArray) :
    (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
      (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry).size = max mem.size 2368 := by
  have hz : 2368 ≤ (mpZeroed s mem 8).size := by
    rw [size_mpZeroed8]; exact Nat.le_max_right _ _
  have hp : (sqPro (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory.size =
      (mpZeroed s mem 8).size :=
    size_sqPro _ 8 0 _ (by unfold tAddr; omega)
  have hl : (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory.size =
      (mpZeroed s mem 8).size := by
    unfold sqL1
    rw [size_l1Run _ _ 2368 8 (0 + 1) (by decide) (by rw [hp]; exact hz) (8 - 1 - 0), hp]
  rw [size_midMem1 _ _ (by rw [hl]; omega), hl, size_mpZeroed8]

theorem size_diagonal (mem : ByteArray) :
    (R8ZeroFirstRow.diagonal mem).memory.size = max mem.size 2368 := by
  show (MachineState.writeBytes mem _ 2336).size = _
  rw [MachineState.writeBytes_size, YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    if_neg (by decide)]

theorem size_zeroRun (q : MacState) (bi : UInt256) (hq : 2368 ≤ q.memory.size) :
    ∀ k, (R8ZeroFirstRow.zeroRun q bi k).memory.size = q.memory.size
  | 0 => rfl
  | k + 1 => by
    show (MachineState.writeBytes (R8ZeroFirstRow.zeroRun q bi k).memory _
      (tAddr 8 (k + 1))).size = q.memory.size
    rw [size_store_of_le _ _ _ (by rw [size_zeroRun q bi hq k]; unfold tAddr; omega),
      size_zeroRun q bi hq k]

theorem size_firstMemory (mem : ByteArray) :
    (R8ZeroFirstRow.firstMemory mem).size = max mem.size 2368 := by
  have hd : 2368 ≤ (R8ZeroFirstRow.diagonal mem).memory.size := by
    rw [size_diagonal]; exact Nat.le_max_right _ _
  unfold R8ZeroFirstRow.firstMemory R8ZeroFirstRow.firstProduct
  rw [size_store_of_le _ _ _ (by rw [size_zeroRun _ _ hd 7]; omega), size_zeroRun _ _ hd 7,
    size_diagonal]

/-! ## The exact bridge -/

/-- With a zero scratch word, the machine memory after the first-row program **is** the
machine-carry row model of the zeroed memory. -/
theorem firstMemory_eq (s : State) (mem : ByteArray) (hscr : ScratchZero mem) :
    R8ZeroFirstRow.firstMemory mem =
      midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
        (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry := by
  have hA := R8ZeroFirstRow.firstMemory_bridge s mem
  have hL : ScratchZero (R8ZeroFirstRow.firstMemory mem) := hscr.firstMemory
  have hR : ScratchZero (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
      (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry) :=
    ((scratchZero_mpZeroed s mem 8 (by decide)).sqL1 8 0 _).midMem1 _
  have hsize : (R8ZeroFirstRow.firstMemory mem).size =
      (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
        (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry).size := by
    rw [size_firstMemory, size_model]
  apply ByteArray.ext_getElem hsize
  intro i hi hi'
  rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi,
    ← Challenge.EvmProof.Memory.getD0_eq_getElem _ i hi']
  by_cases hout : i < 2048 ∨ 2080 ≤ i
  · exact hA i hout
  · rw [hL i (by omega) (by omega), hR i (by omega) (by omega)]

/-! ## The slot-channel bridge of the first row -/

theorem readPadded_zeroStep_low (q : MacState) (bi : UInt256) (j : Nat) (start count : Nat)
    (h : start + count ≤ 2112) :
    MachineState.readPadded (R8ZeroFirstRow.zeroStep q bi j).memory start count =
      MachineState.readPadded q.memory start count := by
  show MachineState.readPadded (MachineState.writeBytes q.memory _ (tAddr 8 j)) start count = _
  apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
  left; unfold tAddr; omega

theorem readPadded_zeroRun_low (q : MacState) (bi : UInt256) (start count : Nat)
    (h : start + count ≤ 2112) :
    ∀ k, MachineState.readPadded (R8ZeroFirstRow.zeroRun q bi k).memory start count =
      MachineState.readPadded q.memory start count
  | 0 => rfl
  | k + 1 => by
    show MachineState.readPadded (R8ZeroFirstRow.zeroStep (R8ZeroFirstRow.zeroRun q bi k) bi (k+1)).memory
      start count = _
    rw [readPadded_zeroStep_low _ _ _ _ _ h, readPadded_zeroRun_low q bi start count h k]

/-- The real memory after the reassembled first row (no scratch-word store) is the
machine-carry model with the entry scratch word of the real memory re-installed, and the
cell holds the model's scratch word. -/
theorem firstProduct_unflush (s : State) (mem : ByteArray) (hscr : ScratchZero mem) :
    (R8ZeroFirstRow.firstProduct mem).memory =
        unflush mem (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry) ∧
      (R8ZeroFirstRow.firstProduct mem).carry =
        MachineState.readWord (midMem1 (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory
          (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).carry) 2080 := by
  have hz : MachineState.readWord (sqL1 (mpZeroed s mem 8) 8 0 (UInt256.ofNat 0)).memory 2080 =
      UInt256.ofNat 0 := by
    rw [readWord_sqL1 _ 8 0 2080 _ (by decide) (Or.inl (by decide))]
    exact readWord_mpZeroed_tn s mem 8
  have hd : 2368 ≤ (R8ZeroFirstRow.diagonal mem).memory.size := by
    rw [size_diagonal]; exact Nat.le_max_right _ _
  constructor
  · rw [← firstMemory_eq s mem hscr]
    unfold R8ZeroFirstRow.firstMemory
    rw [unflush_writeWord _ _ _ (YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _)]
    unfold unflush
    have hsame : MachineState.readPadded mem 2080 32 =
        MachineState.readPadded (R8ZeroFirstRow.firstProduct mem).memory 2080 32 := by
      unfold R8ZeroFirstRow.firstProduct
      rw [readPadded_zeroRun_low _ _ 2080 32 (by decide) 7]
      show _ = MachineState.readPadded (MachineState.writeBytes mem _ 2336) 2080 32
      rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint _ _ 2080 32 2336
        (Or.inl (by decide))]
    rw [hsame]
    symm
    apply writeBytes_readPadded_self
    unfold R8ZeroFirstRow.firstProduct
    rw [size_zeroRun _ _ hd 7]
    omega
  · unfold midMem1
    rw [Challenge.EvmProof.Memory.readWord_writeWord, hz, R8ZeroFirstRow.zero_add_word]
    exact (R8ZeroFirstRow.firstProduct_bridge s mem).2

end Challenge.Modexp.Submission.Proofs.Fast.R8RowZeroExact

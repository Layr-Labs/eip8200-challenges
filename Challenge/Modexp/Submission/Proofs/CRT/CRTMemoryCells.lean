import Challenge.Modexp.Submission.Proofs.Fast.Model
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace HistoricalSearch.CRTMemoryCells
open EvmSemantics
open Challenge.EvmProof.Memory

def writeCell (mem : ByteArray) (cell : Nat × UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded cell.2.toNat 32) cell.1

def storeCells (mem : ByteArray) : List (Nat × UInt256) → ByteArray
  | [] => mem
  | cell :: cells => storeCells (writeCell mem cell) cells

/-- Sequential stores preserve every disjoint read window, irrespective of
store order or the original memory's physical length. -/
theorem readPadded_storeCells (mem : ByteArray) (cells : List (Nat × UInt256))
    (start count : Nat)
    (h : ∀ c ∈ cells, start+count ≤ c.1 ∨ c.1+32 ≤ start) :
    MachineState.readPadded (storeCells mem cells) start count =
      MachineState.readPadded mem start count := by
  induction cells generalizing mem with
  | nil => rfl
  | cons c cs ih =>
    rw [storeCells, ih _ (fun d hd => h d (List.mem_cons_of_mem c hd))]
    unfold writeCell
    apply readPadded_writeBytes_disjoint
    simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h c (by simp)

theorem readWord_storeCells (mem : ByteArray) (cells : List (Nat × UInt256))
    (start : Nat)
    (h : ∀ c ∈ cells, start+32 ≤ c.1 ∨ c.1+32 ≤ start) :
    MachineState.readWord (storeCells mem cells) start = MachineState.readWord mem start := by
  unfold MachineState.readWord
  rw [readPadded_storeCells mem cells start 32 h]

/-- A write is harmless to an established cell if it writes the same value at
the same address or is disjoint. This avoids requiring a global store order. -/
theorem writeCell_preserves (mem : ByteArray) (c : Nat × UInt256) (addr : Nat) (value : UInt256)
    (hmem : MachineState.readWord mem addr = value)
    (hc : (c.1 = addr ∧ c.2 = value) ∨ addr+32 ≤ c.1 ∨ c.1+32 ≤ addr) :
    MachineState.readWord (writeCell mem c) addr = value := by
  rcases hc with ⟨ha, hv⟩ | hd
  · unfold writeCell
    rw [ha, hv, readWord_writeWord]
  · unfold writeCell
    rw [readWord_writeBytes_disjoint]
    · exact hmem
    · simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hd

theorem storeCells_preserves (mem : ByteArray) (cells : List (Nat × UInt256))
    (addr : Nat) (value : UInt256)
    (hmem : MachineState.readWord mem addr = value)
    (h : ∀ c ∈ cells, (c.1 = addr ∧ c.2 = value) ∨ addr+32 ≤ c.1 ∨ c.1+32 ≤ addr) :
    MachineState.readWord (storeCells mem cells) addr = value := by
  induction cells generalizing mem with
  | nil => exact hmem
  | cons c cs ih =>
    exact ih (writeCell mem c) (writeCell_preserves mem c addr value hmem (h c (by simp)))
      (fun d hd => h d (List.mem_cons_of_mem c hd))

/-- A cell appearing in the store list has its assigned value afterwards,
provided all other stores preserve it. -/
theorem storeCells_hit (mem : ByteArray) (cells : List (Nat × UInt256))
    (addr : Nat) (value : UInt256) (hit : (addr,value) ∈ cells)
    (h : ∀ c ∈ cells, (c.1 = addr ∧ c.2 = value) ∨ addr+32 ≤ c.1 ∨ c.1+32 ≤ addr) :
    MachineState.readWord (storeCells mem cells) addr = value := by
  induction cells generalizing mem with
  | nil => simp at hit
  | cons c cs ih =>
    rcases List.mem_cons.mp hit with he | ht
    · subst c
      rw [storeCells]
      apply storeCells_preserves
      · exact readWord_writeWord mem addr value
      · exact fun d hd => h d (List.mem_cons_of_mem (addr,value) hd)
    · exact ih (writeCell mem c) ht (fun d hd => h d (List.mem_cons_of_mem c hd))

/-- All new operand/cancellation/column/counter scratch stores are below1792.
Both original operand blocks and every configuration word remain available. -/
theorem scratch_preserves_live (mem : ByteArray) (cells : List (Nat × UInt256))
    (h : ∀ c ∈ cells, 768 ≤ c.1 ∧ c.1+32 ≤ 1792)
    (start count : Nat) (hrange : start+count ≤ 768 ∨ 1792 ≤ start) :
    MachineState.readPadded (storeCells mem cells) start count =
      MachineState.readPadded mem start count := by
  apply readPadded_storeCells
  intro c hc
  have hb := h c hc
  omega

end HistoricalSearch.CRTMemoryCells

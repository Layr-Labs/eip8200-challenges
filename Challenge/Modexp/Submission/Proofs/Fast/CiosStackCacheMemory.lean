import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

/-!
Three accumulator words live on the EVM stack during CIOS execution. The
logical memory is obtained by flushing them in exactly the exit-block order.
The projection lemmas below allow the existing memory-based MONPRO recurrence
to remain the arithmetic specification.
-/
namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Memory
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

@[simp] theorem storeWord_size (mem : ByteArray) (a : Nat) (x : UInt256) :
    (storeWord mem a x).size = max mem.size (a+32) := by
  simp [storeWord, MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

theorem storeWord_overwrite (mem : ByteArray) (a : Nat) (x y : UInt256) :
    storeWord (storeWord mem a x) a y = storeWord mem a y := by
  apply ByteArray.ext_getElem
  · simp only [storeWord_size]; omega
  · intro i hleft hright
    rw [← getD0_eq_getElem _ _ hleft, ← getD0_eq_getElem _ _ hright]
    simp only [storeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split <;> rfl

theorem storeWord_comm (mem : ByteArray) (a b : Nat) (x y : UInt256)
    (hsep : a+32 ≤ b ∨ b+32 ≤ a) :
    storeWord (storeWord mem a x) b y = storeWord (storeWord mem b y) a x := by
  apply ByteArray.ext_getElem
  · simp only [storeWord_size]; omega
  · intro i hleft hright
    rw [← getD0_eq_getElem _ _ hleft, ← getD0_eq_getElem _ _ hright]
    simp only [storeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases ha : a ≤ i ∧ i < a+32
    · have hb : ¬ (b ≤ i ∧ i < b+32) := by omega
      simp only [ha, hb, if_false]
    · by_cases hb : b ≤ i ∧ i < b+32
      · simp only [ha, hb, if_false]
      · simp only [ha, hb, if_false]

theorem readWord_storeWord_disjoint (mem : ByteArray) (a b : Nat) (x : UInt256)
    (hsep : a+32 ≤ b ∨ b+32 ≤ a) :
    MachineState.readWord (storeWord mem a x) b = MachineState.readWord mem b := by
  apply readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hsep.symm

structure CachedMemory where
  memory : ByteArray
  t0 : UInt256
  t1 : UInt256
  t2 : UInt256

def CachedMemory.virtual (c : CachedMemory) : ByteArray :=
  storeWord (storeWord (storeWord c.memory 8256 c.t0) 8288 c.t1) 8320 c.t2

@[simp] theorem virtual_t0 (c : CachedMemory) :
    MachineState.readWord c.virtual 8256 = c.t0 := by
  rw [CachedMemory.virtual, readWord_storeWord_disjoint _ 8320 8256 _ (by omega),
    readWord_storeWord_disjoint _ 8288 8256 _ (by omega), readWord_storeWord]

@[simp] theorem virtual_t1 (c : CachedMemory) :
    MachineState.readWord c.virtual 8288 = c.t1 := by
  rw [CachedMemory.virtual, readWord_storeWord_disjoint _ 8320 8288 _ (by omega),
    readWord_storeWord]

@[simp] theorem virtual_t2 (c : CachedMemory) :
    MachineState.readWord c.virtual 8320 = c.t2 := by
  exact readWord_storeWord _ _ _

theorem virtual_read_disjoint (c : CachedMemory) (a : Nat)
    (hsep : a+32 ≤ 8256 ∨ 8352 ≤ a) :
    MachineState.readWord c.virtual a = MachineState.readWord c.memory a := by
  rw [CachedMemory.virtual, readWord_storeWord_disjoint _ 8320 a _ (by omega),
    readWord_storeWord_disjoint _ 8288 a _ (by omega),
    readWord_storeWord_disjoint _ 8256 a _ (by omega)]

def CachedMemory.write (c : CachedMemory) (a : Nat) (x : UInt256) : CachedMemory :=
  if a = 8256 then { c with t0 := x }
  else if a = 8288 then { c with t1 := x }
  else if a = 8320 then { c with t2 := x }
  else { c with memory := storeWord c.memory a x }

theorem virtual_write_t0 (c : CachedMemory) (x : UInt256) :
    storeWord c.virtual 8256 x = ({ c with t0 := x } : CachedMemory).virtual := by
  unfold CachedMemory.virtual
  rw [storeWord_comm _ 8320 8256 _ _ (by omega),
    storeWord_comm _ 8288 8256 _ _ (by omega), storeWord_overwrite]

theorem virtual_write_t1 (c : CachedMemory) (x : UInt256) :
    storeWord c.virtual 8288 x = ({ c with t1 := x } : CachedMemory).virtual := by
  unfold CachedMemory.virtual
  rw [storeWord_comm _ 8320 8288 _ _ (by omega), storeWord_overwrite]

theorem virtual_write_t2 (c : CachedMemory) (x : UInt256) :
    storeWord c.virtual 8320 x = ({ c with t2 := x } : CachedMemory).virtual := by
  exact storeWord_overwrite _ _ _ _

theorem virtual_write_disjoint (c : CachedMemory) (a : Nat) (x : UInt256)
    (hsep : a+32 ≤ 8256 ∨ 8352 ≤ a) :
    storeWord c.virtual a x =
      ({ c with memory := storeWord c.memory a x } : CachedMemory).virtual := by
  unfold CachedMemory.virtual
  rw [storeWord_comm _ 8320 a _ _ (by omega),
    storeWord_comm _ 8288 a _ _ (by omega), storeWord_comm _ 8256 a _ _ (by omega)]

/-- Every aligned accumulator write either updates a cached word or commutes
with all three cache locations. No assumption on the word values is needed. -/
theorem virtual_write (c : CachedMemory) (a : Nat) (x : UInt256)
    (ha : a = 8256 ∨ a = 8288 ∨ a = 8320 ∨ a+32 ≤ 8256 ∨ 8352 ≤ a) :
    (c.write a x).virtual = storeWord c.virtual a x := by
  unfold CachedMemory.write
  split_ifs with h0 h1 h2
  · subst a; exact (virtual_write_t0 c x).symm
  · subst a; exact (virtual_write_t1 c x).symm
  · subst a; exact (virtual_write_t2 c x).symm
  · exact (virtual_write_disjoint c a x (by omega)).symm

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory.virtual_write

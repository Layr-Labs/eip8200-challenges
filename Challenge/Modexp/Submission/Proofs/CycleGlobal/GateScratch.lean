import Challenge.Modexp.Submission.Proofs.CycleGlobal.SlimFrames
import Challenge.EvmProof.Memory
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.GateScratch
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

def value (esize : Nat) : UInt256 := UInt256.eq (UInt256.ofNat 3) (UInt256.ofNat esize)
def memory (mem : ByteArray) (esize : Nat) : ByteArray :=
 MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (value esize).toNat 32) 512

theorem readWord (mem : ByteArray) (esize addr : Nat)
 (hd : addr+32≤512 ∨ 544≤addr) :
 MachineState.readWord (memory mem esize) addr = MachineState.readWord mem addr := by
 apply Memory.readWord_writeBytes_disjoint
 simpa [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hd

theorem readValue (mem : ByteArray) (esize : Nat) :
 MachineState.readWord (memory mem esize) 512 = value esize :=
 Memory.readWord_writeWord mem 512 (value esize)

theorem represents (mem : ByteArray) (esize ptr n X : Nat)
 (hd : ptr+32*n≤512 ∨ 544≤ptr) (hrep : Model.FastRepresents mem ptr n X) :
 Model.FastRepresents (memory mem esize) ptr n X := by
 refine (Model.fastRepresents_congr (a := mem) ?_ X).1 hrep
 intro j hj
 rw [readWord _ _ _ (by omega)]

theorem frame (mem : ByteArray) (esize n bsize mi : Nat) (hf : Exp.Frame mem n bsize mi) :
 Exp.Frame (memory mem esize) n bsize mi := by
 constructor
 · rw [readWord _ _ _ (Or.inr (by decide))]; exact hf.s32
 · rw [readWord _ _ _ (Or.inr (by decide))]; exact hf.minvW
 · rw [readWord _ _ _ (Or.inr (by decide))]; exact hf.ml
 · rw [readWord _ _ _ (Or.inr (by decide))]; exact hf.tl
 · rw [readWord _ _ _ (Or.inr (by decide))]; exact hf.eoff

theorem outer (mem : ByteArray) (n bsize esize msize : Nat) :
 SlimFrames.outer (memory mem esize) n bsize esize msize =
 SlimFrames.outer mem n bsize esize msize := by
 simp only [SlimFrames.outer,CycleSubmission.Global.Fast.Shift.entrySlots,
  CycleSubmission.Global.Fast.Shift.aprevSlot,CycleSubmission.Global.Fast.Shift.hdSlot,
  CycleSubmission.Global.Fast.Shift.headWord,CycleSubmission.Global.Fast.Shift.loopPC]
 simp only [readWord _ _ _ (Or.inr (by decide : 544≤1312)),
  readWord _ _ _ (Or.inr (by decide : 544≤1344)),readWord _ _ _ (Or.inr (by decide : 544≤1376)),
  readWord _ _ _ (Or.inr (by decide : 544≤1408)),readWord _ _ _ (Or.inr (by decide : 544≤1440)),
  readWord _ _ _ (Or.inr (by decide : 544≤1472)),readWord _ _ _ (Or.inr (by decide : 544≤1504)),
  readWord _ _ _ (Or.inr (by decide : 544≤1536)),readWord _ _ _ (Or.inr (by decide : 544≤1568)),
  readWord _ _ _ (Or.inr (by decide : 544≤1632)),readWord _ _ _ (Or.inr (by decide : 544≤1664)),
  readWord _ _ _ (Or.inl (by decide : 32+32≤512))]
#print axioms readWord
#print axioms represents
#print axioms frame
#print axioms outer
end CycleSubmission.Global.GateScratch

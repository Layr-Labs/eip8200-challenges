import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
namespace CycleSubmission.LimbMemory
open EvmSemantics
open Challenge.EvmProof.Memory CycleSubmission.Prepared.Arithmetic
def mask : UInt256 := UInt256.ofNat (2^240-1)
def store (mem : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
 MachineState.writeBytes mem (Data.Bytes.natToBytesPadded value.toNat 32) address
/-- The fifth and seventh accumulator limbs are carried until the loop exits. -/
structure Holds (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : Prop where
 at768 : MachineState.readWord mem 768 = a 0
 at1344 : MachineState.readWord mem 1344 = n 0
 at1376 : MachineState.readWord mem 1376 = n 1
 at2720 : MachineState.readWord mem 2720 = inv
 at1568 : MachineState.readWord mem 1568 = n 7
 at1600 : MachineState.readWord mem 1600 = n 8
 at32 : MachineState.readWord mem 32 = a 3
 at64 : MachineState.readWord mem 64 = a 4
 at128 : MachineState.readWord mem 128 = a 6
/-- The old mask is stored once, before the repeated kernel begins. -/
theorem install (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
 (h : SquareMeaning.Memory0 mem inv a b n) : Holds mem inv a b n := by
 exact ⟨h.at768,h.at1344,h.at1376,h.at2720,h.at1568,h.at1600,h.at32,h.at64,h.at128⟩
/-- The final carried limb reestablishes the original complete memory contract. -/
theorem flush (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
 (h : Holds mem inv a b n) :
 SquareMeaning.Memory0 (store (store mem 96 (a 5)) 160 (a 7)) inv a b n := by
 constructor <;>
  simp (disch := decide) only [store,readWord_writeWord,read_disjoint,
   h.at768,h.at1344,h.at1376,h.at2720,h.at1568,h.at1600,
   h.at32,h.at64,h.at128]
/-- Both private cache stores are disjoint from the retained base operand. -/
theorem store_keeps_base (mem : ByteArray) (address : Nat) (value : UInt256)
 (start count : Nat) (hlo : 256 ≤ start) (hhi : start+count ≤ 768)
 (hdisj : address+32 ≤ 256 ∨ 768 ≤ address) :
 MachineState.readPadded (store mem address value) start count =
 MachineState.readPadded mem start count := by
 unfold store
 apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
 simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
 omega
#print axioms install
#print axioms flush
end CycleSubmission.LimbMemory

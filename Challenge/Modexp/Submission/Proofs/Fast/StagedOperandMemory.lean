import Challenge.Modexp.Submission.Proofs.Fast.Csub

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

/-- The eight-limb kernel leaves this portion of its scratch block unused. -/
def stage (mem : ByteArray) (pa n : Nat) : ByteArray :=
  MachineState.writeBytes mem (MachineState.readPadded mem pa (32*n)) 4864

def inputMemory (mem : ByteArray) (pa n : Nat) : ByteArray :=
  if n = 4 ∨ n = 8 then stage mem pa n else mem

def Snapshot (mem : ByteArray) (pa n : Nat) : Prop :=
  ∀ j, j < n → MachineState.readWord mem (4864 + 32*j) =
    MachineState.readWord mem (pa + 32*j)

theorem read_stage_outside (mem : ByteArray) (pa n addr : Nat)
    (hd : addr + 32 ≤ 4864 ∨ 4864 + 32*n ≤ addr) :
    MachineState.readWord (stage mem pa n) addr = MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa using hd

theorem read_stage_member (mem : ByteArray) (pa n j : Nat) (hj : j < n) :
    MachineState.readWord (stage mem pa n) (4864 + 32*j) =
      MachineState.readWord mem (pa + 32*j) := by
  exact Csub.readWord_mcopy mem pa 4864 (32*n) j (by omega)

theorem snapshot_stage (mem : ByteArray) (pa n : Nat) (hpa : pa + 32*n ≤ 4096) :
    Snapshot (stage mem pa n) pa n := by
  intro j hj
  rw [read_stage_member mem pa n j hj, read_stage_outside mem pa n _ (Or.inl (by omega))]

theorem read_inputMemory_outside (mem : ByteArray) (pa n addr : Nat)
    (hd : addr + 32 ≤ 4096 ∨ 5184 ≤ addr) :
    MachineState.readWord (inputMemory mem pa n) addr = MachineState.readWord mem addr := by
  unfold inputMemory
  split
  · rename_i hn
    exact read_stage_outside mem pa n addr (by rcases hn with rfl | rfl <;> omega)
  · rfl

theorem fastRepresents_inputMemory (mem : ByteArray) (pa n ptr count value : Nat)
    (hptr : ptr + 32*count ≤ 4096) :
    Model.FastRepresents (inputMemory mem pa n) ptr count value ↔
      Model.FastRepresents mem ptr count value := by
  apply Model.fastRepresents_congr
  intro j hj
  exact read_inputMemory_outside mem pa n (ptr+32*j) (Or.inl (by omega))

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

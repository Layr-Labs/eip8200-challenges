import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

def stage (mem : ByteArray) (pa n : Nat) : ByteArray :=
  MachineState.writeBytes mem (MachineState.readPadded mem pa (32*n)) 2368

def stageW (mem : ByteArray) (pa n : Nat) : ByteArray :=
  MachineState.writeBytes mem (MachineState.readPadded mem pa (32*n)) (1856 + 64*n)

theorem stageW_eight (mem : ByteArray) (pa : Nat) : stageW mem pa 8 = stage mem pa 8 := rfl

theorem read_stageW_outside (mem : ByteArray) (pa n addr : Nat)
    (hd : addr + 32 ≤ 1856 + 64*n ∨ 1856 + 64*n + 32*n ≤ addr) :
    MachineState.readWord (stageW mem pa n) addr = MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa using hd

theorem read_stageW_four_outside (mem : ByteArray) (addr : Nat)
    (hd : addr + 32 ≤ 2112 ∨ 2240 ≤ addr) :
    MachineState.readWord (stageW mem 2112 4) addr = MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa using hd

theorem read_stageW_four_member (mem : ByteArray) (j : Nat) (hj : j < 4) :
    MachineState.readWord (stageW mem 2112 4) (2112 + 32*j) =
      MachineState.readWord mem (2112 + 32*j) :=
  Csub.readWord_mcopy mem 2112 2112 (32*4) j (by omega)

theorem read_stageW_four (mem : ByteArray) (addr : Nat)
    (hd : addr + 32 ≤ 2112 ∨ 2240 ≤ addr ∨ ∃ j, j < 4 ∧ addr = 2112 + 32*j) :
    MachineState.readWord (stageW mem 2112 4) addr = MachineState.readWord mem addr := by
  rcases hd with h | h | ⟨j, hj, rfl⟩
  · exact read_stageW_four_outside mem addr (Or.inl h)
  · exact read_stageW_four_outside mem addr (Or.inr h)
  · exact read_stageW_four_member mem j hj

theorem represents_stageW_four (mem : ByteArray) (ptr cnt v : Nat)
    (hd : ptr + 32*cnt ≤ 2112 ∨ 2240 ≤ ptr ∨ (ptr = 2112 ∧ cnt ≤ 4))
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (stageW mem 2112 4) ptr cnt v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 hrep
  intro j hj
  rcases hd with h | h | ⟨rfl, hc⟩
  · rw [read_stageW_four_outside mem _ (Or.inl (by omega))]
  · rw [read_stageW_four_outside mem _ (Or.inr (by omega))]
  · rw [read_stageW_four_member mem j (by omega)]

def eligible (mem : ByteArray) (n : Nat) : Prop :=
  (n = 4 ∨ n = 8) ∧ MachineState.readWord mem 2720 ≠ UInt256.ofNat 1

instance (mem : ByteArray) (n : Nat) : Decidable (eligible mem n) := by
  unfold eligible
  infer_instance

def inputMemory (mem : ByteArray) (pa n : Nat) : ByteArray :=
  if eligible mem n then stage mem pa n else mem

def Snapshot (mem : ByteArray) (pa n : Nat) : Prop :=
  ∀ j, j < n → MachineState.readWord mem (2368 + 32*j) =
    MachineState.readWord mem (pa + 32*j)

theorem read_stage_outside (mem : ByteArray) (pa n addr : Nat)
    (hd : addr + 32 ≤ 2368 ∨ 2368 + 32*n ≤ addr) :
    MachineState.readWord (stage mem pa n) addr = MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa using hd

theorem read_stage_member (mem : ByteArray) (pa n j : Nat) (hj : j < n) :
    MachineState.readWord (stage mem pa n) (2368 + 32*j) =
      MachineState.readWord mem (pa + 32*j) := by
  exact Csub.readWord_mcopy mem pa 2368 (32*n) j (by omega)

theorem snapshot_stage (mem : ByteArray) (pa n : Nat) (hpa : pa + 32*n ≤ 2048) :
    Snapshot (stage mem pa n) pa n := by
  intro j hj
  rw [read_stage_member mem pa n j hj, read_stage_outside mem pa n _ (Or.inl (by omega))]

theorem read_inputMemory_outside (mem : ByteArray) (pa n addr : Nat)
    (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
    MachineState.readWord (inputMemory mem pa n) addr = MachineState.readWord mem addr := by
  unfold inputMemory
  split
  · rename_i hn
    exact read_stage_outside mem pa n addr (by rcases hn.1 with rfl | rfl <;> omega)
  · rfl

theorem eligible_preserved (a b : ByteArray) (n : Nat)
    (h : MachineState.readWord a 2720 = MachineState.readWord b 2720) :
    eligible a n ↔ eligible b n := by simp only [eligible, h]

theorem eligible_zeroed (s : State) (mem : ByteArray) (n : Nat) (hn : n ≤ 8) :
    eligible (Monpro.mpZeroed s mem n) n ↔ eligible mem n :=
  eligible_preserved _ _ n (Monpro.readWord_mpZeroed s mem n 2720 hn (Or.inr (by decide)))

theorem eligible_inputMemory (mem : ByteArray) (pa n : Nat) :
    eligible (inputMemory mem pa n) n ↔ eligible mem n :=
  eligible_preserved _ _ n (read_inputMemory_outside mem pa n 2720 (Or.inr (by decide)))

theorem fastRepresents_inputMemory (mem : ByteArray) (pa n ptr count value : Nat)
    (hptr : ptr + 32*count ≤ 2048) :
    Model.FastRepresents (inputMemory mem pa n) ptr count value ↔
      Model.FastRepresents mem ptr count value := by
  apply Model.fastRepresents_congr
  intro j hj
  exact read_inputMemory_outside mem pa n (ptr+32*j) (Or.inl (by omega))

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

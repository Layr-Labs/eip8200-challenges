import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro

theorem read_l1_high (mem : ByteArray) (bi : UInt256) (pa n addr j : Nat)
    (hn : n ≤ 8) (ha : 8960 ≤ addr) :
    MachineState.readWord (l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [l1Step]
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
    · exact ih
    · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      omega

theorem read_l2_high (mem : ByteArray) (mu c0 : UInt256) (n addr j : Nat)
    (hn : n ≤ 8) (ha : 8960 ≤ addr) :
    MachineState.readWord (l2Step mem mu c0 n j).memory addr =
      MachineState.readWord mem addr := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [l2Step]
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
    · exact ih
    · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      omega

theorem Snapshot.l1 {mem : ByteArray} {pa n : Nat} (h : Snapshot mem pa n)
    (bi : UInt256) (j : Nat) (hn : n ≤ 8) (hpa : pa+32*n ≤ 8192) :
    Snapshot (l1Step mem bi pa n j).memory pa n := by
  intro k hk
  rw [read_l1_high _ _ _ _ _ _ hn (by omega),
    readWord_l1Step _ _ _ _ _ _ (by omega) (Or.inl (by omega))]
  exact h k hk

theorem read_zeroed_high (s : State) (mem : ByteArray) (n addr : Nat)
    (hn : n ≤ 8) (ha : 8960 ≤ addr) :
    MachineState.readWord (mpZeroed s mem n) addr = MachineState.readWord mem addr := by
  unfold mpZeroed
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

theorem Snapshot.zeroed {mem : ByteArray} {pa n : Nat} (h : Snapshot mem pa n)
    (s : State) (hn : n ≤ 8) (hpa : pa+32*n ≤ 8192) :
    Snapshot (mpZeroed s mem n) pa n := by
  intro k hk
  rw [read_zeroed_high _ _ _ _ hn (by omega),
    readWord_mpZeroed _ _ _ _ (by omega) (Or.inl (by omega))]
  exact h k hk

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem read_two_stores (mem : ByteArray) (v w r : Nat)
    (hr : r+32 ≤ 2048 ∨ 2112 ≤ r) :
    MachineState.readWord
      (MachineState.writeBytes
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 2080)
        (Data.Bytes.natToBytesPadded w 32) 2048) r =
      MachineState.readWord mem r := by
  have h1 : MachineState.readWord
      (MachineState.writeBytes
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 2080)
        (Data.Bytes.natToBytesPadded w 32) 2048) r =
      MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 2080) r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h2 : MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 2080) r =
      MachineState.readWord mem r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  rw [h1, h2]

theorem read_mid (mem : ByteArray) (c : UInt256) (r : Nat)
    (hr : r+32 ≤ 2048 ∨ 2112 ≤ r) :
    MachineState.readWord (midMem mem c) r = MachineState.readWord mem r :=
  read_two_stores mem _ _ r hr

theorem rowMu_mid (mem : ByteArray) (c : UInt256) (n : Nat) (hn : 2 ≤ n) :
    rowMu (midMem mem c) n = rowMu mem n := by
  unfold rowMu
  rw [read_mid mem c 2816 (Or.inr (by decide)),
    read_mid mem c (2080+32*n) (Or.inr (by omega))]

theorem rowC0_mid (mem : ByteArray) (c : UInt256) (n : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) :
    rowC0 (midMem mem c) n = rowC0 mem n := by
  unfold rowC0
  rw [rowMu_mid mem c n hn, read_mid mem c (32*n-32) (Or.inl (by omega))]

/-- The row-head inverse relation belongs to the logical memory state. -/
def inverseInvariant (mem : ByteArray) (n : Nat) : Prop :=
  ((MachineState.readWord mem (32*n-32)).toNat *
    (MachineState.readWord mem 2816).toNat + 1) % 2 ^ 256 = 0

opaque inverse_mpZeroed (s : State) (mem : ByteArray) (n : Nat)
    (hn : n ≤ 8) (hminv : inverseInvariant mem n) :
    inverseInvariant (mpZeroed s mem n) n := by
  unfold inverseInvariant at *
  rw [readWord_mpZeroed s mem n (32*n-32) hn (Or.inl (by omega)),
    readWord_mpZeroed s mem n 2816 hn (Or.inr (by decide))]
  exact hminv

opaque inverse_rowsMem (mem : ByteArray) (pa pb n i : Nat)
    (hn : n ≤ 8) (hminv : inverseInvariant mem n) :
    inverseInvariant (rowsMem mem pa pb n i) n := by
  unfold inverseInvariant at *
  rw [readWord_rowsMem mem pa pb n (32*n-32) hn (Or.inl (by omega)) i,
    readWord_rowsMem mem pa pb n 2816 hn (Or.inr (by decide)) i]
  exact hminv

opaque inverse_l1Step (mem : ByteArray) (bi : UInt256) (pa n j : Nat)
    (hn : n ≤ 8) (hminv : inverseInvariant mem n) :
    inverseInvariant (l1Step mem bi pa n j).memory n := by
  unfold inverseInvariant at *
  rw [readWord_l1Step mem bi pa n (32*n-32) j hn (Or.inl (by omega)),
    readWord_l1Step mem bi pa n 2816 j hn (Or.inr (by decide))]
  exact hminv

opaque inverse_midMem (mem : ByteArray) (c : UInt256) (n : Nat)
    (hn : n ≤ 8) (hminv : inverseInvariant mem n) :
    inverseInvariant (midMem mem c) n := by
  unfold inverseInvariant at *
  rw [read_mid mem c (32*n-32) (Or.inl (by omega)),
    read_mid mem c 2816 (Or.inr (by decide))]
  exact hminv

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

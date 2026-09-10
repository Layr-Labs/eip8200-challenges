import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem read_two_stores (mem : ByteArray) (v w r : Nat)
    (hr : r+32 ≤ 8192 ∨ 8256 ≤ r) :
    MachineState.readWord
      (MachineState.writeBytes
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224)
        (Data.Bytes.natToBytesPadded w 32) 8192) r =
      MachineState.readWord mem r := by
  have h1 : MachineState.readWord
      (MachineState.writeBytes
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224)
        (Data.Bytes.natToBytesPadded w 32) 8192) r =
      MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224) r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  have h2 : MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) 8224) r =
      MachineState.readWord mem r := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    omega
  rw [h1, h2]

theorem read_mid (mem : ByteArray) (c : UInt256) (r : Nat)
    (hr : r+32 ≤ 8192 ∨ 8256 ≤ r) :
    MachineState.readWord (midMem mem c) r = MachineState.readWord mem r :=
  read_two_stores mem _ _ r hr

theorem rowMu_mid (mem : ByteArray) (c : UInt256) (n : Nat) (hn : 2 ≤ n) :
    rowMu (midMem mem c) n = rowMu mem n := by
  unfold rowMu
  rw [read_mid mem c 9376 (Or.inr (by decide)),
    read_mid mem c (8224+32*n) (Or.inr (by omega))]

theorem rowC0_mid (mem : ByteArray) (c : UInt256) (n : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) :
    rowC0 (midMem mem c) n = rowC0 mem n := by
  unfold rowC0
  rw [rowMu_mid mem c n hn, read_mid mem c (32*n-32) (Or.inl (by omega))]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

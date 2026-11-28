import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace RipemdSubmission20261101
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode RipemdSubmissionTables20261028
open StackRoundTrace
private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a+b) := by
  apply Word.word_ext
  change (a % 2^256 + b % 2^256) % 2^256 = (a+b) % 2^256
  exact (Nat.add_mod a b (2^256)).symm
private theorem hadd_literals (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a+b) := add_literals a b
namespace Ordinary2
def template : List Instr := [
.op (.Dup ⟨1, by decide⟩),
.op .PC,
.op .MSTORE,
.op (.Dup ⟨4, by decide⟩),
.push ⟨2, by decide⟩ (UInt256.ofNat 90),
.op .MSTORE,
.op (.Dup ⟨3, by decide⟩),
.push ⟨1, by decide⟩ (UInt256.ofNat 72),
.op .MSTORE,
.push ⟨1, by decide⟩ (UInt256.ofNat 236),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 142),
.op .MLOAD,
.push ⟨2, by decide⟩ (UInt256.ofNat 266),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 232),
.op .MLOAD,
.op (.Dup ⟨1, by decide⟩),
.push ⟨2, by decide⟩ (UInt256.ofNat 472),
.op .MSTORE]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [(MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 614)) (Data.Bytes.natToBytesPadded (x 4).toNat 32) 90)) (Data.Bytes.natToBytesPadded (x 3).toNat 32) 72)) 232), (MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 614)) (Data.Bytes.natToBytesPadded (x 4).toNat 32) 90)) (Data.Bytes.natToBytesPadded (x 3).toNat 32) 72)) 266), (MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 614)) (Data.Bytes.natToBytesPadded (x 4).toNat 32) 90)) (Data.Bytes.natToBytesPadded (x 3).toNat 32) 72)) 142), (MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 614)) (Data.Bytes.natToBytesPadded (x 4).toNat 32) 90)) (Data.Bytes.natToBytesPadded (x 3).toNat 32) 72)) 236), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 614)) (Data.Bytes.natToBytesPadded (x 4).toNat 32) 90)) (Data.Bytes.natToBytesPadded (x 3).toNat 32) 72)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 614)) (Data.Bytes.natToBytesPadded (x 4).toNat 32) 90)) (Data.Bytes.natToBytesPadded (x 3).toNat 32) 72)) 266)).toNat 32) 472)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 613).take 30 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (576+37)).take 30 = _
  rw [← List.drop_drop, CandidateBytes.drop9]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 613), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 643), stack := outputs x rho s, memory := memory x s} := by
  have hcap (n : Nat) (hn : n ≤ 100) : rho.length + n < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hactiveAt (address size : Nat) (ha : address+size ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address size) = s.activeWords := by
    have heq : MachineState.activeWordsAfter s.activeWords.toNat address size = s.activeWords.toNat := by
      unfold MachineState.activeWordsAfter
      split_ifs
      · rfl
      · apply Nat.max_eq_left
        omega
    rw [heq]
    exact (Word.word_eq_ofNat_toNat _).symm
  simp (discharger := omega) [template, inputs, outputs, memory,
    runInstrSeq, DataStepper.runInstr, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap, hzero,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat,
    Word.literal_eq_ofNat, add_literals, hadd_literals]
  all_goals rfl
#print axioms exact_bytes
#print axioms run
end Ordinary2
end RipemdSubmission20261101

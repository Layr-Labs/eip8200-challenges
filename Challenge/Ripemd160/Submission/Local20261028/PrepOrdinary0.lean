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
namespace Ordinary0
def template : List Instr := [
.push ⟨1, by decide⟩ (UInt256.ofNat 146),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 128),
.op .MSTORE,
.push ⟨1, by decide⟩ (UInt256.ofNat 178),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 196),
.op .MSTORE,
.push ⟨1, by decide⟩ (UInt256.ofNat 236),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 218),
.op .MSTORE,
.push ⟨2, by decide⟩ (UInt256.ofNat 268),
.op .MLOAD,
.push ⟨2, by decide⟩ (UInt256.ofNat 286),
.op .MSTORE]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) 178)).toNat 32) 196)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) 178)).toNat 32) 196)) 236)).toNat 32) 218)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) 178)).toNat 32) 196)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) (Data.Bytes.natToBytesPadded ((MachineState.readWord ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 128)) 178)).toNat 32) 196)) 236)).toNat 32) 218)) 268)).toNat 32) 286)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 530).take 26 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (512+18)).take 26 = _
  rw [← List.drop_drop, CandidateBytes.drop8]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 530), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 556), stack := outputs x rho s, memory := memory x s} := by
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
end Ordinary0
end RipemdSubmission20261101

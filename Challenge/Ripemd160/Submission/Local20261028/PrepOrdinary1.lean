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
namespace Ordinary1
def template : List Instr := [
.push ⟨1, by decide⟩ (UInt256.ofNat 138),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 168),
.op .MLOAD,
.push ⟨2, by decide⟩ (UInt256.ofNat 262),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 236),
.op .MLOAD,
.push ⟨2, by decide⟩ (UInt256.ofNat 266),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 228),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 224),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 134),
.op .MLOAD,
.push ⟨22, by decide⟩ (UInt256.ofNat 63353157587505792712163362468939828208675924746436608),
.op .ADD,
.push ⟨2, by decide⟩ (UInt256.ofNat 258),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 180),
.op .MLOAD,
.push ⟨1, by decide⟩ (UInt256.ofNat 146),
.op .MLOAD,
.op (.Dup ⟨0, by decide⟩),
.push ⟨2, by decide⟩ (UInt256.ofNat 594),
.op .MSTORE]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [(MachineState.readWord (s.memory) 146), (MachineState.readWord (s.memory) 180), (MachineState.readWord (s.memory) 258), (UInt256.add ((UInt256.ofNat 63353157587505792712163362468939828208675924746436608)) ((MachineState.readWord (s.memory) 134))), (MachineState.readWord (s.memory) 224), (MachineState.readWord (s.memory) 228), (MachineState.readWord (s.memory) 266), (MachineState.readWord (s.memory) 236), (MachineState.readWord (s.memory) 262), (MachineState.readWord (s.memory) 168), (MachineState.readWord (s.memory) 138), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((MachineState.readWord (s.memory) 146)).toNat 32) 594)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 556).take 65 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (512+44)).take 65 = _
  rw [← List.drop_drop, CandidateBytes.drop8]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 556), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 621), stack := outputs x rho s, memory := memory x s} := by
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
end Ordinary1
end RipemdSubmission20261101

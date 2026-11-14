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
namespace Ordinary5
def template : List Instr := [
.op (.Dup ⟨7, by decide⟩),
.push ⟨3, by decide⟩ (UInt256.ofNat 828),
.op .MSTORE,
.op (.Dup ⟨2, by decide⟩),
.push ⟨3, by decide⟩ (UInt256.ofNat 612),
.op .MSTORE,
.op (.Dup ⟨8, by decide⟩),
.op .PC,
.op .MSTORE,
.op (.Dup ⟨0, by decide⟩),
.push ⟨2, by decide⟩ (UInt256.ofNat 558),
.op .MSTORE,
.push ⟨2, by decide⟩ (UInt256.ofNat 936),
.op .MSTORE,
.push ⟨2, by decide⟩ (UInt256.ofNat 846),
.op .MSTORE]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (x 7).toNat 32) 828)) (Data.Bytes.natToBytesPadded (x 2).toNat 32) 612)) (Data.Bytes.natToBytesPadded (x 8).toNat 32) 720)) (Data.Bytes.natToBytesPadded (x 0).toNat 32) 558)) (Data.Bytes.natToBytesPadded (x 0).toNat 32) 936)) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 846)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 707).take 28 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (704+3)).take 28 = _
  rw [← List.drop_drop, CandidateBytes.drop11]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 707), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 735), stack := outputs x rho s, memory := memory x s} := by
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
end Ordinary5
end RipemdSubmission20261101

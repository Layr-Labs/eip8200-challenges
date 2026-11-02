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
namespace First4
def template : List Instr := [
.push ⟨1, by decide⟩ (UInt256.ofNat 122),
.push ⟨2, by decide⟩ (UInt256.ofNat 10426),
.push ⟨2, by decide⟩ (UInt256.ofNat 576),
.op .CODECOPY,
.op (.Dup ⟨0, by decide⟩),
.push ⟨2, by decide⟩ (UInt256.ofNat 738),
.op .MSTORE,
.push ⟨2, by decide⟩ (UInt256.ofNat 720),
.op .MSTORE,
.op (.Dup ⟨0, by decide⟩),
.push ⟨14, by decide⟩ (UInt256.ofNat 5192296858534827628530496329220095),
.op .NOT,
.op .AND,
.push ⟨2, by decide⟩ (UInt256.ofNat 828),
.op .MSTORE,
.op (.Dup ⟨0, by decide⟩),
.push ⟨2, by decide⟩ (UInt256.ofNat 972),
.op .MSTORE]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := (MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes ((MachineState.writeBytes (s.memory) (MachineState.readPadded s.executionEnv.code 10426 122) 576)) (Data.Bytes.natToBytesPadded (x 0).toNat 32) 738)) (Data.Bytes.natToBytesPadded (x 0).toNat 32) 720)) (Data.Bytes.natToBytesPadded ((UInt256.land ((UInt256.lnot ((UInt256.ofNat 5192296858534827628530496329220095)))) (x 1))).toNat 32) 828)) (Data.Bytes.natToBytesPadded (x 1).toNat 32) 972)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10136).take 45 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10112+24)).take 45 = _
  rw [← List.drop_drop, CandidateBytes.drop158]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10136), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 10181), stack := outputs x rho s, memory := memory x s} := by
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
end First4
end RipemdSubmission20261101

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
namespace PrefixBefore
def template : List Instr := [
.op (.Dup ⟨8, by decide⟩),
.op (.Dup ⟨1, by decide⟩),
.op .MUL,
.push ⟨1, by decide⟩ (UInt256.ofNat 23),
.op .SHR,
.op (.Dup ⟨8, by decide⟩),
.op (.Dup ⟨8, by decide⟩),
.op (.Dup ⟨13, by decide⟩),
.push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
.op .ADD,
.push ⟨1, by decide⟩ (UInt256.ofNat 94),
.op .MLOAD,
.op .ADD,
.op (.Dup ⟨13, by decide⟩),
.op (.Dup ⟨13, by decide⟩),
.op (.Dup ⟨13, by decide⟩),
.op .NOT,
.op .OR,
.op .XOR,
.op .ADD,
.op (.Dup ⟨5, by decide⟩),
.op .AND,
.op (.Dup ⟨4, by decide⟩),
.op .MUL,
.push ⟨1, by decide⟩ (UInt256.ofNat 25),
.op .SHR,
.op .ADD,
.op (.Dup ⟨4, by decide⟩),
.op .AND,
.op (.Dup ⟨4, by decide⟩),
.op (.Dup ⟨4, by decide⟩),
.op (.Dup ⟨6, by decide⟩),
.op (.Dup ⟨15, by decide⟩),
.op (.Dup ⟨6, by decide⟩),
.op .NOT,
.op .OR,
.op (.Dup ⟨4, by decide⟩),
.op .XOR,
.push ⟨2, by decide⟩ (UInt256.ofNat 608),
.op .MLOAD,
.op (.Dup ⟨14, by decide⟩),
.op .ADD,
.op .ADD,
.push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
.op .ADD,
.op .AND,
.op .MUL,
.push ⟨1, by decide⟩ (UInt256.ofNat 24),
.op .SHR,
.op (.Dup ⟨3, by decide⟩),
.op .ADD,
.op .AND,
.push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
.op (.Dup ⟨14, by decide⟩),
.op (.Dup ⟨6, by decide⟩),
.op .MUL,
.push ⟨1, by decide⟩ (UInt256.ofNat 23),
.op .SHR,
.op (.Swap ⟨3, by decide⟩),
.op (.Dup ⟨3, by decide⟩),
.op (.Dup ⟨5, by decide⟩),
.op .NOT,
.op .OR,
.op (.Dup ⟨3, by decide⟩),
.op .XOR,
.op .ADD,
.push ⟨2, by decide⟩ (UInt256.ofNat 728),
.op .MLOAD,
.op .ADD,
.op .ADD,
.op (.Dup ⟨6, by decide⟩),
.op .AND,
.op (.Dup ⟨5, by decide⟩),
.op .MUL,
.push ⟨1, by decide⟩ (UInt256.ofNat 24),
.op .SHR,
.op (.Dup ⟨4, by decide⟩),
.op .ADD,
.op (.Dup ⟨6, by decide⟩),
.op .AND,
.push ⟨1, by decide⟩ (UInt256.ofNat 144),
.op .SHL,
.op (.Dup ⟨14, by decide⟩),
.op .OR,
.op (.Swap ⟨0, by decide⟩),
.push ⟨1, by decide⟩ (UInt256.ofNat 144),
.op .SHL,
.op (.Dup ⟨13, by decide⟩),
.op .OR,
.op (.Swap ⟨3, by decide⟩),
.push ⟨1, by decide⟩ (UInt256.ofNat 144),
.op .SHL,
.op (.Dup ⟨15, by decide⟩),
.op .OR,
.op (.Swap ⟨1, by decide⟩),
.op (.Dup ⟨5, by decide⟩),
.op .MUL,
.push ⟨1, by decide⟩ (UInt256.ofNat 23),
.op .SHR,
.push ⟨1, by decide⟩ (UInt256.ofNat 144),
.op .SHL,
.op (.Dup ⟨12, by decide⟩),
.op .OR,
.op (.Swap ⟨2, by decide⟩),
.push ⟨1, by decide⟩ (UInt256.ofNat 144),
.op .SHL,
.op (.Dup ⟨11, by decide⟩),
.op .OR]
def inputs (x : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def outputs (x : Nat → UInt256) (rho : List UInt256) (s : State) : List UInt256 :=
  [(UInt256.lor (x 6) ((UInt256.shiftLeft ((UInt256.shiftRight ((UInt256.mul (x 0) (x 9))) ((UInt256.ofNat 23)))) ((UInt256.ofNat 144))))), (UInt256.lor (x 9) ((UInt256.shiftLeft ((UInt256.land (x 1) ((UInt256.add ((UInt256.shiftRight ((UInt256.mul (x 0) (x 8))) ((UInt256.ofNat 23)))) ((UInt256.shiftRight ((UInt256.mul (x 0) ((UInt256.land (x 1) ((UInt256.add ((UInt256.add ((MachineState.readWord (s.memory) 728)) ((UInt256.add ((UInt256.xor ((UInt256.land ((UInt256.add (x 7) ((UInt256.shiftRight ((UInt256.mul ((UInt256.land ((UInt256.add ((UInt256.ofNat 1352829926)) ((UInt256.add ((UInt256.add (x 6) ((MachineState.readWord (s.memory) 608)))) ((UInt256.xor ((UInt256.land (x 1) ((UInt256.add ((UInt256.shiftRight ((UInt256.mul (x 0) ((UInt256.land (x 1) ((UInt256.add ((UInt256.xor ((UInt256.lor ((UInt256.lnot (x 7))) (x 8))) (x 9))) ((UInt256.add ((MachineState.readWord (s.memory) 94)) ((UInt256.add ((UInt256.ofNat 1352829926)) (x 10))))))))))) ((UInt256.ofNat 25)))) (x 6))))) ((UInt256.lor ((UInt256.lnot ((UInt256.shiftRight ((UInt256.mul (x 0) (x 8))) ((UInt256.ofNat 23)))))) (x 9))))))))) (x 1))) (x 0))) ((UInt256.ofNat 24)))))) (x 1))) ((UInt256.lor ((UInt256.lnot ((UInt256.shiftRight ((UInt256.mul (x 0) (x 9))) ((UInt256.ofNat 23)))))) ((UInt256.land (x 1) ((UInt256.add ((UInt256.shiftRight ((UInt256.mul (x 0) ((UInt256.land (x 1) ((UInt256.add ((UInt256.xor ((UInt256.lor ((UInt256.lnot (x 7))) (x 8))) (x 9))) ((UInt256.add ((MachineState.readWord (s.memory) 94)) ((UInt256.add ((UInt256.ofNat 1352829926)) (x 10))))))))))) ((UInt256.ofNat 25)))) (x 6))))))))) (x 7))))) ((UInt256.ofNat 1352829926)))))))) ((UInt256.ofNat 24)))))))) ((UInt256.ofNat 144))))), (UInt256.lor (x 10) ((UInt256.shiftLeft ((UInt256.shiftRight ((UInt256.mul (x 0) (x 8))) ((UInt256.ofNat 23)))) ((UInt256.ofNat 144))))), (UInt256.lor (x 7) ((UInt256.shiftLeft ((UInt256.shiftRight ((UInt256.mul (x 0) ((UInt256.land (x 1) ((UInt256.add ((UInt256.shiftRight ((UInt256.mul (x 0) ((UInt256.land (x 1) ((UInt256.add ((UInt256.xor ((UInt256.lor ((UInt256.lnot (x 7))) (x 8))) (x 9))) ((UInt256.add ((MachineState.readWord (s.memory) 94)) ((UInt256.add ((UInt256.ofNat 1352829926)) (x 10))))))))))) ((UInt256.ofNat 25)))) (x 6))))))) ((UInt256.ofNat 23)))) ((UInt256.ofNat 144))))), (UInt256.lor (x 8) ((UInt256.shiftLeft ((UInt256.land ((UInt256.add (x 7) ((UInt256.shiftRight ((UInt256.mul ((UInt256.land ((UInt256.add ((UInt256.ofNat 1352829926)) ((UInt256.add ((UInt256.add (x 6) ((MachineState.readWord (s.memory) 608)))) ((UInt256.xor ((UInt256.land (x 1) ((UInt256.add ((UInt256.shiftRight ((UInt256.mul (x 0) ((UInt256.land (x 1) ((UInt256.add ((UInt256.xor ((UInt256.lor ((UInt256.lnot (x 7))) (x 8))) (x 9))) ((UInt256.add ((MachineState.readWord (s.memory) 94)) ((UInt256.add ((UInt256.ofNat 1352829926)) (x 10))))))))))) ((UInt256.ofNat 25)))) (x 6))))) ((UInt256.lor ((UInt256.lnot ((UInt256.shiftRight ((UInt256.mul (x 0) (x 8))) ((UInt256.ofNat 23)))))) (x 9))))))))) (x 1))) (x 0))) ((UInt256.ofNat 24)))))) (x 1))) ((UInt256.ofNat 144))))), x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] ++ rho
def memory (x : Nat → UInt256) (s : State) : ByteArray := s.memory
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 794).take 136 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (768+26)).take 136 = _
  rw [← List.drop_drop, CandidateBytes.drop12]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 794), stack := inputs x rho} =
      some {s with pc := (UInt256.ofNat 930), stack := outputs x rho s, memory := memory x s} := by
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
  all_goals repeat first | apply And.intro | rfl
#print axioms exact_bytes
#print axioms run
end PrefixBefore
end RipemdSubmission20261101

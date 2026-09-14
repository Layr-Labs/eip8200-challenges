import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Funding
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace

def highKey : UInt256 := UInt256.ofNat 30169115476673038213297653277143730720156734734729216
def sparseKey : UInt256 := UInt256.ofNat (128 * (2^144+1))
def highTemplate : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 1352829926),
   .push ⟨1, by decide⟩ (UInt256.ofNat 144), .op .SHL]
def sparseTemplate : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 128), .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 144), .op .SHL, .op .OR]

theorem high_value : UInt256.shiftLeft (UInt256.ofNat 1352829926) (UInt256.ofNat 144) = highKey := by decide
theorem sparse_value : UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 128) (UInt256.ofNat 144)) (UInt256.ofNat 128) = sparseKey := by decide

theorem run_high (s : State) (pc : UInt256) (rest : List UInt256)
    (hrun : s.halt = .Running) (hstack : rest.length ≤ 1000) :
    runInstrSeq highTemplate {s with pc := pc, stack := rest} =
      some {s with pc := pcAfter pc highTemplate, stack := highKey :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 23) : rest.length + n < 1024 := by omega
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  simp (discharger := omega) [highTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, hrun, hcap, h0, h1, h2, h3, Word.word_toNat_ofNat, high_value]
  rfl

theorem run_sparse (s : State) (pc : UInt256) (rest : List UInt256)
    (hrun : s.halt = .Running) (hstack : rest.length ≤ 1000) :
    runInstrSeq sparseTemplate {s with pc := pc, stack := rest} =
      some {s with pc := pcAfter pc sparseTemplate, stack := sparseKey :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 23) : rest.length + n < 1024 := by omega
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  simp (discharger := omega) [sparseTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, hrun, hcap, h0, h1, h2, h3, Word.word_toNat_ofNat, sparse_value,
    List.getElem?_cons_zero, List.exchange]
  rfl

#print axioms high_value
#print axioms sparse_value
#print axioms run_high
#print axioms run_sparse
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Funding

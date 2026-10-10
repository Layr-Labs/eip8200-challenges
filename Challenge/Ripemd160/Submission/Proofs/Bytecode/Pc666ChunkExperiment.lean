import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolRawWriter
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/- A local execution lemma only; this experimental template is not connected
   to the submitted artifact or its universal correctness endpoint. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pc666ChunkExperiment
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory PoolRawWriter
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b
def template : List Instr :=
  [ .op (.Dup ⟨13, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 684),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 936),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 108),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 792),
    .op .MSTORE,
    .op (.Dup ⟨15, by decide⟩),
    .op .PC,
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 540),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 756),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE ]

def writes (words : Nat → UInt256) : List (Nat × UInt256) :=
  [(684, words 6), (936, words 8), (108, words 5), (792, words 1),
   (666, words 14), (540, words 1), (756, words 9), (522, words 0)]
def memory (m : ByteArray) (words : Nat → UInt256) : ByteArray :=
  Pair13WriterRaw.writeChain m (writes words)
theorem run_experimental_chunk1 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) (hpc : pc = UInt256.ofNat 646) :
    runInstrSeq template {s with pc := pc, stack := stack1 words rho} =
      some {s with
        pc := pcAfter pc template
        stack := outputStack1 words rho
        memory := memory s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords address hactive haddress
  have hactivePC : MachineState.activeWordsAfter s.activeWords.toNat 666 32 % UInt256.size =
      s.activeWords.toNat := congrArg UInt256.toNat (hactiveAt 666 (by decide))
  have hactive540 : MachineState.activeWordsAfter s.activeWords.toNat 540 32 % UInt256.size =
      s.activeWords.toNat := congrArg UInt256.toNat (hactiveAt 540 (by decide))
  have hactive756 : MachineState.activeWordsAfter s.activeWords.toNat 756 32 % UInt256.size =
      s.activeWords.toNat := congrArg UInt256.toNat (hactiveAt 756 (by decide))
  norm_num [UInt256.size] at hactivePC hactive540 hactive756
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [hpc, add_literals, template, stack1, outputStack1, memory, writes, Pair13WriterRaw.writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals try simp (config := { maxSteps := 600000 }) (discharger := omega)
    [add_literals, Word.word_toNat_ofNat, hactivePC, hactiveAt]
  all_goals try (rw [hactivePC])
  all_goals try (rw [hactive540, hactive756]; exact hactiveAt 522 (by decide))
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_experimental_chunk1
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pc666ChunkExperiment

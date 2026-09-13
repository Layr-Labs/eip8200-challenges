import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80MaskConsume
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80MaskConsume
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Table80Setup
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache PairedScheduleMemory
open PairTableMemory PairTableActive PairTableLayout

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

theorem run_stores (s : State) (pc returnPC : UInt256) (rest : List UInt256) (words : Nat → UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq storesTemplate {s with pc := pc, stack := poolStack words ++ (returnPC :: rest)} =
      some {s with pc := pcAfter pc storesTemplate, stack := Table80Raw.cache ++ (returnPC :: rest), memory := resultMemory s.memory words} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    word_active_preserved _ _ hactive ha
  simp (discharger := omega) [storesTemplate, poolStack, resultMemory, storeDescending,
    tableWords, slots, writeWord, Table80Raw.cache, maskWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    PairedHelperBooleanTrace.push0_toNat,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [add_eq_hAdd]
#print axioms run_stores
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80MaskConsume

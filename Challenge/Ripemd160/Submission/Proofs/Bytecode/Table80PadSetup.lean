import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory
open PairTableActive PairTableSparse PairTableLayout

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

theorem run_pad (s : State) (pc returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256) :
    runInstrSeq padTemplate {s with pc := pc, stack := returnPC :: rest} =
      some {s with pc := pcAfter pc padTemplate, stack := Table80Raw.cache ++ (returnPC :: rest), memory := PairTablePad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    word_active_preserved _ _ hactive ha
  have hcopyActive := zero_active_preserved s.activeWords hactive
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  simp (discharger := omega) [padTemplate, PairTablePad.resultMemory,
    storeSelected, PairTablePad.keepPad, tableWords, slots, zeroMemory,
    PadOnlySchedule.padWords, PadOnlySchedule.lowDiet_eq_lowLength,
    PadOnlySchedule.lowLength, PadOnlySchedule.highLength,
    writeWord, Table80Raw.cache,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    PairedHelperBooleanTrace.push0_toNat,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, hcopyActive, hsize,
    PairTablePad.readPadded_end, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [add_eq_hAdd]
#print axioms run_pad
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup

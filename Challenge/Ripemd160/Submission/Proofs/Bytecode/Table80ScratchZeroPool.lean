import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ScratchZero
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ScratchZero
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Table80Setup
open StackRoundTrace DenseScheduleTemplate PairedMask32Cache
open PairTableScratch PairTableActive

theorem run_pool (s : State) (pc returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq poolTemplate {s with pc := pc, stack := maskWord :: returnPC :: rest} =
      some {s with pc := pcAfter pc poolTemplate, stack := poolStack (poolWord s.memory) ++ (returnPC :: rest)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    word_active_preserved _ _ hactive ha
  simp (discharger := omega) [poolTemplate, poolStack, poolWord, Word.mask32, maskWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    Word.land_comm, PairedHelperBooleanTrace.push0_toNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_pool
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ScratchZero

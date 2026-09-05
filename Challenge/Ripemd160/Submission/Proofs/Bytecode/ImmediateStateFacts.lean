import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionFunctionalTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateModelMatch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundActiveWords
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateStateFacts

open EvmSemantics EvmSemantics.EVM
open CompressionTrace CompressionRightTrace RoundActiveWords
open private leftSelector_lt rightSelector_lt leftStates_tableByte
  rightStates_tableByte from
  Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionFunctionalTrace

private theorem afterConstantLoad_activeWords (s : State) (base i : Nat)
    (hi : i < 80) (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 4 * 32 + 32 ≤ 67 * 32) :
    (afterConstantLoad s base i).activeWords = s.activeWords :=
  congrArg (fun (t : State) => t.activeWords)
    (ImmediateModelMatch.afterConstantLoad_eq s base i hi hactive hbase)

private theorem tableAtReturned_activeWords (s : State) (base i : Nat)
    (hi : i < 80) (hlo : 31 ≤ base) (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 96 + 32 ≤ 67 * 32) (returnDest : UInt256)
    (rest : List UInt256) :
    (TableTrace.tableAtReturned s (UInt256.ofNat base) (UInt256.ofNat i)
      returnDest rest).activeWords = s.activeWords := by
  have h := congrArg (fun (t : State) => t.activeWords)
    (ImmediateNeutralLoads.tableAtReturned_neutral s base i hi hlo
      (by omega) hactive returnDest rest)
  exact h

private theorem leftRoundState_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (leftRoundState s messageOffset returnDest rest i).activeWords =
      s.activeWords := by
  let q₀ := afterConstantLoad s 1568 i
  have h₀ : q₀.activeWords = s.activeWords :=
    afterConstantLoad_activeWords s 1568 i hi hactive (by omega)
  let q₁ := leftFirstReturned s messageOffset returnDest rest i
  have h₁ : q₁.activeWords = s.activeWords := by
    unfold q₁ leftFirstReturned
    exact (tableAtReturned_activeWords q₀ 1376 i hi (by omega)
      (by rw [h₀]; exact hactive) (by omega) _ _).trans h₀
  let q₂ := leftSecondReturned s messageOffset returnDest rest i
  have h₂ : q₂.activeWords = s.activeWords := by
    unfold q₂ leftSecondReturned
    exact (tableAtReturned_activeWords q₁ 1184 i hi (by omega)
      (by rw [h₁]; exact hactive) (by omega) _ _).trans h₁
  have hword :
      (TableTrace.tableValue q₁ (UInt256.ofNat 1184)
        (UInt256.ofNat i)).toNat < 16 := by
    rw [TableTrace.tableValue_tableByte q₁ 1184 i (by omega) (by omega) hi]
    change (InitializationCorrect.tableByte s.memory 1184 i).toNat < 16
    rw [htables.1 i hi, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (leftSelector_lt i hi) (by norm_num))]
    exact leftSelector_lt i hi
  unfold leftRoundState
  exact (roundReturned_activeWords q₂ 192 (by omega) (roundIndex i)
    (TableTrace.tableValue q₁ (UInt256.ofNat 1184) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1376) (UInt256.ofNat i))
    (constantAt s 1568 i) (UInt256.ofNat 714) hword _
    (by rw [h₂]; exact hactive)).trans h₂

theorem leftStates_tables_preserved (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (n : Nat)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    InitializationCorrect.TablesCorrect
      (leftStates s messageOffset returnDest rest n).memory := by
  rcases htables with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1184 i
      (by omega)]
    exact hr i hi
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1280 i
      (by omega)]
    exact hrP i hi
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1376 i
      (by omega)]
    exact hs i hi
  · intro i hi
    rw [leftStates_tableByte s messageOffset returnDest rest n 1472 i
      (by omega)]
    exact hsP i hi

theorem leftStates_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) (n : Nat) (hn : n ≤ 80) :
    (leftStates s messageOffset returnDest rest n).activeWords =
      s.activeWords := by
  have hloop : ∀ n, n ≤ 80 →
      (leftStates s messageOffset returnDest rest n).activeWords =
        s.activeWords := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [leftStates_succ]
        exact (leftRoundState_activeWords
          (leftStates s messageOffset returnDest rest n)
          messageOffset returnDest rest n (by omega)
          (leftStates_tables_preserved s messageOffset returnDest rest n htables)
          (by rw [ih (by omega)]; exact hactive)).trans (ih (by omega))
  exact hloop n hn

private theorem rightRoundState_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (i : Nat) (hi : i < 80)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) :
    (rightRoundState s messageOffset returnDest rest i).activeWords =
      s.activeWords := by
  let q₀ := afterConstantLoad s 1728 i
  have h₀ : q₀.activeWords = s.activeWords :=
    afterConstantLoad_activeWords s 1728 i hi hactive (by omega)
  let q₁ := rightFirstReturned s messageOffset returnDest rest i
  have h₁ : q₁.activeWords = s.activeWords := by
    unfold q₁ rightFirstReturned
    exact (tableAtReturned_activeWords q₀ 1472 i hi (by omega)
      (by rw [h₀]; exact hactive) (by omega) _ _).trans h₀
  let q₂ := rightSecondReturned s messageOffset returnDest rest i
  have h₂ : q₂.activeWords = s.activeWords := by
    unfold q₂ rightSecondReturned
    exact (tableAtReturned_activeWords q₁ 1280 i hi (by omega)
      (by rw [h₁]; exact hactive) (by omega) _ _).trans h₁
  have hword :
      (TableTrace.tableValue q₁ (UInt256.ofNat 1280)
        (UInt256.ofNat i)).toNat < 16 := by
    rw [TableTrace.tableValue_tableByte q₁ 1280 i (by omega) (by omega) hi]
    change (InitializationCorrect.tableByte s.memory 1280 i).toNat < 16
    rw [htables.2.1 i hi, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans (rightSelector_lt i hi) (by norm_num))]
    exact rightSelector_lt i hi
  unfold rightRoundState
  exact (roundReturned_activeWords q₂ 352 (by omega) (rightRoundIndex i)
    (TableTrace.tableValue q₁ (UInt256.ofNat 1280) (UInt256.ofNat i))
    (TableTrace.tableValue s (UInt256.ofNat 1472) (UInt256.ofNat i))
    (constantAt s 1728 i) (UInt256.ofNat 792) hword _
    (by rw [h₂]; exact hactive)).trans h₂

theorem rightStates_tables_preserved (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) (n : Nat)
    (htables : InitializationCorrect.TablesCorrect s.memory) :
    InitializationCorrect.TablesCorrect
      (rightStates s messageOffset returnDest rest n).memory := by
  rcases htables with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1184 i
      (by omega)]
    exact hr i hi
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1280 i
      (by omega)]
    exact hrP i hi
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1376 i
      (by omega)]
    exact hs i hi
  · intro i hi
    rw [rightStates_tableByte s messageOffset returnDest rest n 1472 i
      (by omega)]
    exact hsP i hi

theorem rightStates_activeWords (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256)
    (htables : InitializationCorrect.TablesCorrect s.memory)
    (hactive : 67 ≤ s.activeWords.toNat) (n : Nat) (hn : n ≤ 80) :
    (rightStates s messageOffset returnDest rest n).activeWords =
      s.activeWords := by
  have hloop : ∀ n, n ≤ 80 →
      (rightStates s messageOffset returnDest rest n).activeWords =
        s.activeWords := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [rightStates_succ]
        exact (rightRoundState_activeWords
          (rightStates s messageOffset returnDest rest n)
          messageOffset returnDest rest n (by omega)
          (rightStates_tables_preserved s messageOffset returnDest rest n htables)
          (by rw [ih (by omega)]; exact hactive)).trans (ih (by omega))
  exact hloop n hn

theorem leftStates_slotWord (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (n base i : Nat) (hbase : 352 ≤ base) :
    InitializationCorrect.slotWord
        (leftStates s messageOffset returnDest rest n).memory base i =
      InitializationCorrect.slotWord s.memory base i := by
  unfold InitializationCorrect.slotWord
  change wordAt (leftStates s messageOffset returnDest rest n) (base + 32 * i) = _
  exact CompressionFunctionalTrace.leftStates_word_outside
    s messageOffset returnDest rest n (base + 32 * i) (Or.inr (by omega))

theorem rightStates_slotWord (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (n base i : Nat) (hbase : 512 ≤ base) :
    InitializationCorrect.slotWord
        (rightStates s messageOffset returnDest rest n).memory base i =
      InitializationCorrect.slotWord s.memory base i := by
  unfold InitializationCorrect.slotWord
  change wordAt (rightStates s messageOffset returnDest rest n) (base + 32 * i) = _
  exact CompressionFunctionalTrace.rightStates_word_outside
    s messageOffset returnDest rest n (base + 32 * i) (Or.inr (by omega))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateStateFacts

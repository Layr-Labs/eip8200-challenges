import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionRightTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateNeutralLoads

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateModelMatch

open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace CompressionRightTrace ImmediateNeutralLoads

theorem afterConstantLoad_eq (s : State) (base i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hbase : base + 4 * 32 + 32 ≤ 67 * 32) :
    afterConstantLoad s base i = s := by
  have ha : s.activeWordsAfterUInt256 (base + roundIndex i * 32) 32 =
      s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    unfold roundIndex
    have hdiv : i / 16 ≤ 4 := by omega
    omega
  simp only [afterConstantLoad, ha]

theorem leftFirstReturned_eq (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat) :
    leftFirstReturned s messageOffset returnDest rest i =
      {s with
        pc := UInt256.ofNat 693
        stack := TableTrace.tableValue s 1376 (UInt256.ofNat i) ::
          ([constantAt s 1568 i, UInt256.ofNat 714, UInt256.ofNat (roundIndex i),
            UInt256.ofNat i, messageOffset, returnDest] ++ rest)} := by
  unfold leftFirstReturned
  rw [afterConstantLoad_eq s 1568 i hi hactive (by omega)]
  exact tableAtReturned_neutral s 1376 i hi (by omega) (by omega) hactive _ _

theorem leftSecondReturned_eq (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat) :
    leftSecondReturned s messageOffset returnDest rest i =
      {s with
        pc := UInt256.ofNat 706
        stack := TableTrace.tableValue s 1184 (UInt256.ofNat i) ::
          ([TableTrace.tableValue s 1376 (UInt256.ofNat i), constantAt s 1568 i,
            UInt256.ofNat 714, UInt256.ofNat (roundIndex i), UInt256.ofNat i,
            messageOffset, returnDest] ++ rest)} := by
  have hfirst := leftFirstReturned_eq s messageOffset returnDest rest i hi hactive
  have ha : 67 ≤ (leftFirstReturned s messageOffset returnDest rest i).activeWords.toNat := by
    rw [hfirst]
    exact hactive
  unfold leftSecondReturned
  rw [tableAtReturned_neutral _ 1184 i hi (by omega) (by omega) ha, hfirst]
  rfl

theorem leftRoundState_immediate (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat) (nextPC : UInt256)
    (nextStack : List UInt256) :
    {leftRoundState s messageOffset returnDest rest i
      with pc := nextPC, stack := nextStack} =
      RoundTrace.roundReturned s 192 (roundIndex i)
        (TableTrace.tableValue s 1184 (UInt256.ofNat i))
        (TableTrace.tableValue s 1376 (UInt256.ofNat i))
        (constantAt s 1568 i) nextPC nextStack := by
  unfold leftRoundState
  rw [leftSecondReturned_eq s messageOffset returnDest rest i hi hactive]
  simp only
  rw [roundReturned_reframe (oldReturn := nextPC) (oldRest := nextStack)]
  rfl

theorem rightFirstReturned_eq (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat) :
    rightFirstReturned s messageOffset returnDest rest i =
      {s with
        pc := UInt256.ofNat 767
        stack := TableTrace.tableValue s 1472 (UInt256.ofNat i) ::
          ([constantAt s 1728 i, UInt256.ofNat 792, UInt256.ofNat (roundIndex i),
            UInt256.ofNat i, messageOffset, returnDest] ++ rest)} := by
  unfold rightFirstReturned
  rw [afterConstantLoad_eq s 1728 i hi hactive (by omega)]
  exact tableAtReturned_neutral s 1472 i hi (by omega) (by omega) hactive _ _

theorem rightSecondReturned_eq (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat) :
    rightSecondReturned s messageOffset returnDest rest i =
      {s with
        pc := UInt256.ofNat 780
        stack := TableTrace.tableValue s 1280 (UInt256.ofNat i) ::
          ([TableTrace.tableValue s 1472 (UInt256.ofNat i), constantAt s 1728 i,
            UInt256.ofNat 792, UInt256.ofNat (roundIndex i), UInt256.ofNat i,
            messageOffset, returnDest] ++ rest)} := by
  have hfirst := rightFirstReturned_eq s messageOffset returnDest rest i hi hactive
  have ha : 67 ≤ (rightFirstReturned s messageOffset returnDest rest i).activeWords.toNat := by
    rw [hfirst]
    exact hactive
  unfold rightSecondReturned
  rw [tableAtReturned_neutral _ 1280 i hi (by omega) (by omega) ha, hfirst]
  rfl

theorem rightRoundState_immediate (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat) (nextPC : UInt256)
    (nextStack : List UInt256) :
    {rightRoundState s messageOffset returnDest rest i
      with pc := nextPC, stack := nextStack} =
      RoundTrace.roundReturned s 352 (rightRoundIndex i)
        (TableTrace.tableValue s 1280 (UInt256.ofNat i))
        (TableTrace.tableValue s 1472 (UInt256.ofNat i))
        (constantAt s 1728 i) nextPC nextStack := by
  unfold rightRoundState
  rw [rightSecondReturned_eq s messageOffset returnDest rest i hi hactive]
  simp only
  rw [roundReturned_reframe (oldReturn := nextPC) (oldRest := nextStack)]
  rfl

theorem leftRoundState_pinned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x620 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[j]!))
    (nextPC : UInt256) (nextStack : List UInt256) :
    {leftRoundState s messageOffset returnDest rest i
      with pc := nextPC, stack := nextStack} =
      RoundTrace.roundReturned s 192 (i / 16)
        (UInt256.ofNat (Crypto.Ripemd160.r[i]!))
        (UInt256.ofNat (Crypto.Ripemd160.s[i]!))
        (Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[i / 16]!))
        nextPC nextStack := by
  have hk : constantAt s 1568 i =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.K[i / 16]!) := by
    simpa only [constantAt, roundIndex, InitializationCorrect.slotWord,
      Nat.mul_comm] using constants (i / 16) (by omega)
  rw [leftRoundState_immediate s messageOffset returnDest rest i hi hactive]
  have hr : TableTrace.tableValue s 1184 (UInt256.ofNat i) =
      InitializationCorrect.tableByte s.memory 1184 i :=
    TableTrace.tableValue_tableByte s 1184 i (by omega) (by omega) hi
  have hs : TableTrace.tableValue s 1376 (UInt256.ofNat i) =
      InitializationCorrect.tableByte s.memory 1376 i :=
    TableTrace.tableValue_tableByte s 1376 i (by omega) (by omega) hi
  rw [hr, hs,
    tables.1 i hi, tables.2.2.1 i hi, hk]
  rfl

theorem rightRoundState_pinned (s : State) (messageOffset returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 80)
    (hactive : 67 ≤ s.activeWords.toNat)
    (tables : InitializationCorrect.TablesCorrect s.memory)
    (constants : ∀ j, j < 5 → InitializationCorrect.slotWord s.memory 0x6c0 j =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))
    (nextPC : UInt256) (nextStack : List UInt256) :
    {rightRoundState s messageOffset returnDest rest i
      with pc := nextPC, stack := nextStack} =
      RoundTrace.roundReturned s 352 (4 - i / 16)
        (UInt256.ofNat (Crypto.Ripemd160.rP[i]!))
        (UInt256.ofNat (Crypto.Ripemd160.sP[i]!))
        (Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[i / 16]!))
        nextPC nextStack := by
  have hk : constantAt s 1728 i =
      Challenge.EvmProof.Word.ofUInt32 (Crypto.Ripemd160.KP[i / 16]!) := by
    simpa only [constantAt, roundIndex, InitializationCorrect.slotWord,
      Nat.mul_comm] using constants (i / 16) (by omega)
  rw [rightRoundState_immediate s messageOffset returnDest rest i hi hactive]
  have hr : TableTrace.tableValue s 1280 (UInt256.ofNat i) =
      InitializationCorrect.tableByte s.memory 1280 i :=
    TableTrace.tableValue_tableByte s 1280 i (by omega) (by omega) hi
  have hs : TableTrace.tableValue s 1472 (UInt256.ofNat i) =
      InitializationCorrect.tableByte s.memory 1472 i :=
    TableTrace.tableValue_tableByte s 1472 i (by omega) (by omega) hi
  rw [hr, hs,
    tables.2.1 i hi, tables.2.2.2 i hi, hk]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateModelMatch

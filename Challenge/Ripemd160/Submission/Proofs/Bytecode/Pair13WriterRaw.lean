import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreMerge
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory
open Pair13PoolRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl

def writeChain (memory : ByteArray) (writes : List (Nat × UInt256)) : ByteArray :=
  writes.foldl (fun acc item => writeWord acc item.1 item.2) memory

theorem writeChain_cons (memory : ByteArray) (x : Nat × UInt256) (l : List (Nat × UInt256)) :
    writeChain memory (x :: l) = writeChain (writeWord memory x.1 x.2) l := rfl

/-- The value the pool leaves on the stack for source `i`.  Only the five words the JD8
artifact still masks -- 4, 5, 6, 7, 8, 9 and 11 -- arrive as the `2 ^ 144 + 1` broadcast of a clean
32-bit field; the other nine arrive as the raw thirty-two byte load, junk included. -/
def dualW (words : Nat → UInt256) (i : Nat) : UInt256 :=
  if i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 11 then
    UInt256.mul coefficient (words i) else words i

theorem coefficient_toNat : coefficient.toNat = 2 ^ 144 + 1 := by
  rw [coefficient, Word.word_toNat_ofNat]
  norm_num

theorem dual_toNat (w : UInt256) (hw : w.toNat < 2 ^ 32) :
    (UInt256.mul coefficient w).toNat = w.toNat * (2 ^ 144 + 1) := by
  rw [PairStoreMerge.mul_toNat, coefficient_toNat, Nat.mul_comm]
  exact Nat.mod_eq_of_lt ((PairStoreMerge.pack_nat_bound _ hw).trans (by norm_num))

theorem mask_dual (words : Nat → UInt256) (i : Nat)
    (hi : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 11)
    (hw : (words i).toNat < 2 ^ 32) :
    UInt256.land (UInt256.ofNat 4294967295) (dualW words i) = words i := by
  rw [dualW, if_pos hi]
  apply Word.word_ext
  rw [Word.word_toNat_land, Word.word_toNat_ofNat, dual_toNat _ hw,
    Nat.mod_eq_of_lt (by norm_num : 4294967295 < 2 ^ 256), Nat.and_comm,
    show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h : (words i).toNat * (2 ^ 144 + 1)
      = (words i).toNat + (words i).toNat * 2 ^ 112 * 2 ^ 32 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.mul_assoc]
    norm_num
  rw [h, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]

theorem writeWord_comm (memory : ByteArray) (a b : Nat) (v u : UInt256)
    (h : a + 32 ≤ b ∨ b + 32 ≤ a) :
    writeWord (writeWord memory a v) b u = writeWord (writeWord memory b u) a v := by
  apply ByteArray.ext_getElem
  · simp only [writeWord_size]; omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hb : b ≤ i ∧ i < b + 32
    · rw [if_pos hb, if_pos hb, if_neg (by omega)]
    · rw [if_neg hb, if_neg hb]

/-- Overwriting the eighteen bytes below a slot erases the dual lane the broadcast
adds, so the packed and the plain word are interchangeable there. -/
theorem absorb (memory : ByteArray) (a b : Nat) (hab : b + 18 = a) (w u : UInt256)
    (hw : w.toNat < 2 ^ 32) :
    writeWord (writeWord memory a (UInt256.mul coefficient w)) b u =
      writeWord (writeWord memory a w) b u := by
  apply ByteArray.ext_getElem
  · simp only [writeWord_size]
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hb : b ≤ i ∧ i < b + 32
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      by_cases ha : a ≤ i ∧ i < a + 32
      · rw [if_pos ha, if_pos ha,
          YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega),
          YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega),
          dual_toNat w hw,
          PairStoreMerge.byte_pack_nat w.toNat (i - a) hw (by omega), if_neg (by omega)]
      · rw [if_neg ha, if_neg ha]

/-! ### Reordering the interleaved stores

Only table-adjacent slots (eighteen bytes apart) overlap, and the emitted order already
writes every such pair high-first, so the interleaving is a linear extension of the
descending order and an insertion sort reaches it through disjoint swaps only. -/

def ins (x : Nat × UInt256) : List (Nat × UInt256) → List (Nat × UInt256)
  | [] => [x]
  | y :: ys => if y.1 < x.1 then x :: y :: ys else y :: ins x ys

def isort : List (Nat × UInt256) → List (Nat × UInt256)
  | [] => []
  | x :: xs => ins x (isort xs)

/-- The same insertion sort on the addresses alone.  The order check has to live here rather
than on the pair list: with the stored words left abstract the pair-level proposition is not
closed, so `decide` refuses it, while on a literal `List Nat` the kernel settles it directly. -/
def insN (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if b < a then a :: b :: bs else b :: insN a bs

def insOKN (a : Nat) : List Nat → Bool
  | [] => true
  | b :: bs =>
      if b < a then true else ((decide (a + 32 ≤ b) || decide (b + 32 ≤ a)) && insOKN a bs)

def isortN : List Nat → List Nat
  | [] => []
  | a :: as => insN a (isortN as)

def isortOKN : List Nat → Bool
  | [] => true
  | a :: as => insOKN a (isortN as) && isortOKN as

theorem keys_ins (x : Nat × UInt256) (l : List (Nat × UInt256)) :
    (ins x l).map Prod.fst = insN x.1 (l.map Prod.fst) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y.1 < x.1
    · simp only [ins, insN, List.map_cons, if_pos h]
    · simp only [ins, insN, List.map_cons, if_neg h, ih]

theorem keys_isort (l : List (Nat × UInt256)) :
    (isort l).map Prod.fst = isortN (l.map Prod.fst) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [isort, isortN, List.map_cons, keys_ins, ih]

theorem chain_ins (memory : ByteArray) (x : Nat × UInt256) (l : List (Nat × UInt256))
    (h : insOKN x.1 (l.map Prod.fst) = true) :
    writeChain memory (x :: l) = writeChain memory (ins x l) := by
  induction l generalizing memory with
  | nil => rfl
  | cons y ys ih =>
    by_cases hlt : y.1 < x.1
    · simp only [ins, if_pos hlt]
    · simp only [List.map_cons, insOKN, if_neg hlt, Bool.and_eq_true] at h
      have hd : x.1 + 32 ≤ y.1 ∨ y.1 + 32 ≤ x.1 := by
        have h1 := h.1
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        exact h1
      have hins : ins x (y :: ys) = y :: ins x ys := by simp only [ins, if_neg hlt]
      calc writeChain memory (x :: y :: ys)
          = writeChain (writeWord (writeWord memory x.1 x.2) y.1 y.2) ys := rfl
        _ = writeChain (writeWord (writeWord memory y.1 y.2) x.1 x.2) ys := by
              rw [writeWord_comm memory x.1 y.1 x.2 y.2 hd]
        _ = writeChain (writeWord memory y.1 y.2) (x :: ys) := rfl
        _ = writeChain (writeWord memory y.1 y.2) (ins x ys) := ih _ h.2
        _ = writeChain memory (y :: ins x ys) := rfl
        _ = writeChain memory (ins x (y :: ys)) := by rw [hins]

theorem chain_isort (memory : ByteArray) (l : List (Nat × UInt256))
    (h : isortOKN (l.map Prod.fst) = true) :
    writeChain memory l = writeChain memory (isort l) := by
  induction l generalizing memory with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, isortOKN, Bool.and_eq_true] at h
    have h1 : insOKN x.1 ((isort xs).map Prod.fst) = true := by rw [keys_isort]; exact h.1
    rw [writeChain_cons, ih _ h.2, ← writeChain_cons, chain_ins memory x (isort xs) h1]
    rfl

def template0 : List Instr :=
  [ .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 126),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 900),
    .op .MSTORE,
    .op (.Dup ⟨11, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 216),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 882),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 846),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 828),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 558),
    .op .MSTORE ]

def stack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 9,
    dualW words 0,
    dualW words 3,
    dualW words 8,
    dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def outputStack0 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 9,
    dualW words 0,
    dualW words 3,
    dualW words 8,
    dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def writes0 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (126, dualW words 11),
    (900, dualW words 9),
    (216, dualW words 10),
    (882, dualW words 3),
    (864, dualW words 11),
    (846, dualW words 3),
    (828, dualW words 9),
    (558, dualW words 8) ]
def memory0 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes0 words)

theorem run_chunk0 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template0 {s with pc := pc, stack := stack0 words rho} =
      some {s with
        pc := pcAfter pc template0
        stack := outputStack0 words rho
        memory := memory0 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template0, stack0, outputStack0, memory0, writes0, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk0

def template1 : List Instr :=
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
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 774),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 540),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 756),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE ]

def stack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 9,
    dualW words 0,
    dualW words 3,
    dualW words 8,
    dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def outputStack1 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 0,
    dualW words 3,
    dualW words 8,
    dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def writes1 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (684, dualW words 6),
    (936, dualW words 8),
    (108, dualW words 5),
    (792, dualW words 1),
    (774, dualW words 1),
    (540, dualW words 1),
    (756, dualW words 9),
    (522, dualW words 0) ]
def memory1 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes1 words)

theorem run_chunk1 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template1 {s with pc := pc, stack := stack1 words rho} =
      some {s with
        pc := pcAfter pc template1
        stack := outputStack1 words rho
        memory := memory1 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template1, stack1, outputStack1, memory1, writes1, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk1

def template2 : List Instr :=
  [ .op (.Dup ⟨13, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 90),
    .op .MSTORE,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 72),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 36),
    .op .MSTORE,
    .op (.Dup ⟨13, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 504),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1080),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1062),
    .op .MSTORE ]

def stack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 0,
    dualW words 3,
    dualW words 8,
    dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def outputStack2 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 3,
    dualW words 8,
    dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def writes2 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (90, dualW words 12),
    (72, dualW words 4),
    (54, dualW words 0),
    (36, dualW words 0),
    (666, dualW words 14),
    (504, dualW words 1),
    (1080, dualW words 5),
    (1062, dualW words 13) ]
def memory2 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes2 words)

theorem run_chunk2 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template2 {s with pc := pc, stack := stack2 words rho} =
      some {s with
        pc := pcAfter pc template2
        stack := outputStack2 words rho
        memory := memory2 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template2, stack2, outputStack2, memory2, writes2, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk2

def template3 : List Instr :=
  [ .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 486),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 972),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 648),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 630),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 738),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MSTORE ]

def stack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 3,
    dualW words 8,
    dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def outputStack3 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def writes3 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (486, dualW words 5),
    (972, dualW words 3),
    (648, dualW words 15),
    (1008, dualW words 15),
    (630, dualW words 10),
    (612, dualW words 15),
    (738, dualW words 8),
    (288, dualW words 7) ]
def memory3 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes3 words)

theorem run_chunk3 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template3 {s with pc := pc, stack := stack3 words rho} =
      some {s with
        pc := pcAfter pc template3
        stack := outputStack3 words rho
        memory := memory3 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template3, stack3, outputStack3, memory3, writes3, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk3

def template4 : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 594),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1044),
    .op .MSTORE,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 414),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 360),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 720),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 270),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 396),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 468),
    .op .MSTORE ]

def stack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 11,
    dualW words 5,
    dualW words 15,
    dualW words 1,
    dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def outputStack4 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def writes4 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (594, dualW words 11),
    (1044, dualW words 6),
    (414, dualW words 6),
    (360, dualW words 2),
    (720, dualW words 5),
    (270, dualW words 15),
    (396, dualW words 4),
    (468, dualW words 1) ]
def memory4 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes4 words)

theorem run_chunk4 (s : State) (pc : UInt256) (words : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template4 {s with pc := pc, stack := stack4 words rho} =
      some {s with
        pc := pcAfter pc template4
        stack := outputStack4 words rho
        memory := memory4 s.memory words} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template4, stack4, outputStack4, memory4, writes4, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk4

def template5 : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 18),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 342),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 198),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 324),
    .op .MSTORE,
    .push ⟨3, by decide⟩ (UInt256.ofNat 252),
    .op .MSTORE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 450),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 162),
    .op .MSTORE ]

def stack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ dualW words 4,
    dualW words 2,
    dualW words 13,
    dualW words 10,
    dualW words 7,
    dualW words 6,
    dualW words 12,
    dualW words 14 ] ++ rho
def outputStack5 (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  rho
def writes5 (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (18, dualW words 4),
    (342, dualW words 2),
    (198, dualW words 13),
    (324, dualW words 10),
    (252, dualW words 7),
    (0, dualW words 6),
    (450, dualW words 12),
    (162, dualW words 14) ]
def memory5 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writes5 words)

theorem run_chunk5 (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hclean6 : (words 6).toNat < 2 ^ 32) :
    runInstrSeq template5
        {s with pc := pc, stack := stack5 words (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc template5
        stack := outputStack5 words (ret :: UInt256.ofNat 4294967295 :: rest)
        memory := memory5 s.memory words} := by
  have hbase : rest.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template5, stack5, outputStack5, memory5, writes5, writeChain,
     writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
     List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap,
     State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals try simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk5


def writerTemplate : List Instr := template0 ++ template1 ++ template2 ++ template3 ++ template4 ++ template5

def rawWrites (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (126, dualW words 11),
    (900, dualW words 9),
    (216, dualW words 10),
    (882, dualW words 3),
    (864, dualW words 11),
    (846, dualW words 3),
    (828, dualW words 9),
    (558, dualW words 8),
    (684, dualW words 6),
    (936, dualW words 8),
    (108, dualW words 5),
    (792, dualW words 1),
    (774, dualW words 1),
    (540, dualW words 1),
    (756, dualW words 9),
    (522, dualW words 0),
    (90, dualW words 12),
    (72, dualW words 4),
    (54, dualW words 0),
    (36, dualW words 0),
    (666, dualW words 14),
    (504, dualW words 1),
    (1080, dualW words 5),
    (1062, dualW words 13),
    (486, dualW words 5),
    (972, dualW words 3),
    (648, dualW words 15),
    (1008, dualW words 15),
    (630, dualW words 10),
    (612, dualW words 15),
    (738, dualW words 8),
    (288, dualW words 7),
    (594, dualW words 11),
    (1044, dualW words 6),
    (414, dualW words 6),
    (360, dualW words 2),
    (720, dualW words 5),
    (270, dualW words 15),
    (396, dualW words 4),
    (468, dualW words 1),
    (18, dualW words 4),
    (342, dualW words 2),
    (198, dualW words 13),
    (324, dualW words 10),
    (252, dualW words 7),
    (0, dualW words 6),
    (450, dualW words 12),
    (162, dualW words 14) ]

def sortedWrites (words : Nat → UInt256) : List (Nat × UInt256) :=
  [ (1080, dualW words 5),
    (1062, dualW words 13),
    (1044, dualW words 6),
    (1008, dualW words 15),
    (972, dualW words 3),
    (936, dualW words 8),
    (900, dualW words 9),
    (882, dualW words 3),
    (864, dualW words 11),
    (846, dualW words 3),
    (828, dualW words 9),
    (792, dualW words 1),
    (774, dualW words 1),
    (756, dualW words 9),
    (738, dualW words 8),
    (720, dualW words 5),
    (684, dualW words 6),
    (666, dualW words 14),
    (648, dualW words 15),
    (630, dualW words 10),
    (612, dualW words 15),
    (594, dualW words 11),
    (558, dualW words 8),
    (540, dualW words 1),
    (522, dualW words 0),
    (504, dualW words 1),
    (486, dualW words 5),
    (468, dualW words 1),
    (450, dualW words 12),
    (414, dualW words 6),
    (396, dualW words 4),
    (360, dualW words 2),
    (342, dualW words 2),
    (324, dualW words 10),
    (288, dualW words 7),
    (270, dualW words 15),
    (252, dualW words 7),
    (216, dualW words 10),
    (198, dualW words 13),
    (162, dualW words 14),
    (126, dualW words 11),
    (108, dualW words 5),
    (90, dualW words 12),
    (72, dualW words 4),
    (54, dualW words 0),
    (36, dualW words 0),
    (18, dualW words 4),
    (0, dualW words 6) ]

/-- The emitted stores in descending address order.  Each one stores exactly what the pool
left on the stack: the store eighteen bytes below keeps only bits 0..143 of a slot, so there is
nothing to normalise away and no bound on the source word is needed. -/
def writerWrites (words : Nat → UInt256) : List (Nat × UInt256) :=
  sortedWrites words

def writerMemory (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeChain memory (writerWrites words)

def slotOrder : List Nat :=
  [126, 900, 216, 882, 864, 846, 828, 558, 684, 936, 108, 792, 774, 540, 756, 522, 90, 72, 54,
   36, 666, 504, 1080, 1062, 486, 972, 648, 1008, 630, 612, 738, 288, 594, 1044, 414, 360,
   720, 270, 396, 468, 18, 342, 198, 324, 252, 0, 450, 162]

theorem slotOrder_eq (words : Nat → UInt256) :
    (rawWrites words).map Prod.fst = slotOrder := by rfl

/-- Every table-adjacent pair (eighteen bytes apart) is already emitted high-first, so the
insertion sort only ever swaps writes whose thirty-two byte windows are disjoint. -/
theorem slotOrder_ok : isortOKN slotOrder = true := by decide +kernel

/-! Reducing the forty-eight element sort is the expensive step.  `rfl` on the pair list does
not fit this module's heartbeats (measured), so the sort is carried out on a CLOSED list of
(slot, schedule-word) keys, where the kernel settles it, and transported along the payload map.
Key `16` is the slot-0 entry, whose value the writer has already masked back to a plain word. -/

def rawKeys : List (Nat × Nat) :=
  [(126, 11), (900, 9), (216, 10), (882, 3), (864, 11), (846, 3), (828, 9), (558, 8),
   (684, 6), (936, 8), (108, 5), (792, 1), (774, 1), (540, 1), (756, 9), (522, 0), (90, 12),
   (72, 4), (54, 0), (36, 0), (666, 14), (504, 1), (1080, 5), (1062, 13), (486, 5), (972, 3),
   (648, 15), (1008, 15), (630, 10), (612, 15), (738, 8), (288, 7), (594, 11), (1044, 6),
   (414, 6), (360, 2), (720, 5), (270, 15), (396, 4), (468, 1), (18, 4), (342, 2), (198, 13),
   (324, 10), (252, 7), (0, 6), (450, 12), (162, 14)]

def sortedKeys : List (Nat × Nat) :=
  [(1080, 5), (1062, 13), (1044, 6), (1008, 15), (972, 3), (936, 8), (900, 9), (882, 3), (864,
   11), (846, 3), (828, 9), (792, 1), (774, 1), (756, 9), (738, 8), (720, 5), (684, 6), (666,
   14), (648, 15), (630, 10), (612, 15), (594, 11), (558, 8), (540, 1), (522, 0), (504, 1),
   (486, 5), (468, 1), (450, 12), (414, 6), (396, 4), (360, 2), (342, 2), (324, 10), (288, 7),
   (270, 15), (252, 7), (216, 10), (198, 13), (162, 14), (126, 11), (108, 5), (90, 12), (72,
   4), (54, 0), (36, 0), (18, 4), (0, 6)]

def gW (words : Nat → UInt256) (p : Nat × Nat) : Nat × UInt256 :=
  (p.1, if p.2 < 16 then dualW words p.2 else words 6)

theorem gW_fst (words : Nat → UInt256) (p : Nat × Nat) : (gW words p).1 = p.1 := rfl

def insP (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys => if y.1 < x.1 then x :: y :: ys else y :: insP x ys

def isortP : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: xs => insP x (isortP xs)

theorem ins_map (words : Nat → UInt256) (x : Nat × Nat) (l : List (Nat × Nat)) :
    ins (gW words x) (l.map (gW words)) = (insP x l).map (gW words) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y.1 < x.1
    · simp only [List.map_cons, ins, insP, gW_fst, if_pos h]
    · simp only [List.map_cons, ins, insP, gW_fst, if_neg h, ih]

theorem isort_map (words : Nat → UInt256) (l : List (Nat × Nat)) :
    isort (l.map (gW words)) = (isortP l).map (gW words) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, isort, isortP, ih, ins_map]

theorem keys_sorted : isortP rawKeys = sortedKeys := by decide +kernel

theorem rawWrites_eq (words : Nat → UInt256) :
    rawWrites words = rawKeys.map (gW words) := by rfl

theorem sortedWrites_eq (words : Nat → UInt256) :
    sortedWrites words = sortedKeys.map (gW words) := by rfl

theorem sorted_eq (words : Nat → UInt256) :
    isort (rawWrites words) = sortedWrites words := by
  rw [rawWrites_eq, isort_map, keys_sorted, ← sortedWrites_eq]

/-- The emitted interleaving writes the same table image as the inherited descending order.
Sorting is the whole content: with `writerWrites = sortedWrites` there is no value to rewrite,
so this holds for ANY source words, junk included. -/
theorem raw_eq_writer (memory : ByteArray) (words : Nat → UInt256) :
    writeChain memory (rawWrites words) = writerMemory memory words := by
  rw [chain_isort memory (rawWrites words) (by rw [slotOrder_eq]; exact slotOrder_ok),
    sorted_eq]
  rfl

#print axioms keys_sorted
#print axioms slotOrder_ok
#print axioms sorted_eq
#print axioms raw_eq_writer

theorem run_writer (s : State) (pc ret : UInt256) (words : Nat → UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 898) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hclean6 : (words 6).toNat < 2 ^ 32) :
    runInstrSeq writerTemplate
        {s with
          pc := pc
          stack := Pair13PoolRaw.poolStack (dualW words) (ret :: UInt256.ofNat 4294967295 :: rest)} =
      some {s with
        pc := pcAfter pc writerTemplate
        stack := ret :: UInt256.ofNat 4294967295 :: rest
        memory := writerMemory s.memory words} := by
  have hrho : (ret :: UInt256.ofNat 4294967295 :: rest).length ≤ 900 := by
    simp only [List.length_cons]; omega
  let s0 := s
  let pc0 := pc
  have h0 := run_chunk0 s0 pc0 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s1 : State := {s0 with memory := memory0 s0.memory words}
  let pc1 := pcAfter pc0 template0
  have h1 := run_chunk1 s1 pc1 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s2 : State := {s1 with memory := memory1 s1.memory words}
  let pc2 := pcAfter pc1 template1
  have h2 := run_chunk2 s2 pc2 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s3 : State := {s2 with memory := memory2 s2.memory words}
  let pc3 := pcAfter pc2 template2
  have h3 := run_chunk3 s3 pc3 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s4 : State := {s3 with memory := memory3 s3.memory words}
  let pc4 := pcAfter pc3 template3
  have h4 := run_chunk4 s4 pc4 words (ret :: UInt256.ofNat 4294967295 :: rest) hrho hrun hactive
  let s5 : State := {s4 with memory := memory4 s4.memory words}
  let pc5 := pcAfter pc4 template4
  have h5 := run_chunk5 s5 pc5 ret words rest hstack hrun hactive hclean6
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have h02 := DenseScheduleTrace.runInstrSeq_append_running h01 (by exact hrun) h2
  have h03 := DenseScheduleTrace.runInstrSeq_append_running h02 (by exact hrun) h3
  have h04 := DenseScheduleTrace.runInstrSeq_append_running h03 (by exact hrun) h4
  have h05 := DenseScheduleTrace.runInstrSeq_append_running h04 (by exact hrun) h5
  have hmem : memory5 (memory4 (memory3 (memory2 (memory1
      (memory0 s.memory words) words) words) words) words) words
      = writerMemory s.memory words := by
    have h := raw_eq_writer s.memory words
    simp only [rawWrites, writeChain, List.foldl_cons, List.foldl_nil] at h
    simpa only [memory0, memory1, memory2, memory3, memory4, memory5,
      writes0, writes1, writes2, writes3, writes4, writes5,
      writeChain, List.foldl_cons, List.foldl_nil] using h
  simpa only [writerTemplate, DenseScheduleTrace.pcAfter_append,
    s0, s1, s2, s3, s4, s5, pc0, pc1, pc2, pc3, pc4, pc5,
    stack0, Pair13PoolRaw.poolStack, outputStack5, hmem] using h05
#print axioms run_writer

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13WriterRaw

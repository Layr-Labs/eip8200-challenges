import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridgeMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalWord
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ConsumedTerminalTail
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace Paired80WordRound Paired80WordBoolean Paired80WordRotate

def entryStack (factor : UInt256) (q : WordLane) (ret : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.a, q.e, factor, pairWord, upperWord, lowerWord] ++
    (Table80Raw.cache ++ ret :: rho)

def combineWord (memory : ByteArray) (address : Nat) (left right : UInt256) : UInt256 :=
  UInt256.land lowerWord (UInt256.add (MachineState.readWord memory address)
    (UInt256.add (UInt256.shiftRight right (UInt256.ofNat 80)) left))

def result0 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 864 q.c q.d
def result1 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 896 q.d q.e
def result2 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 928 q.e q.a
def result3 (memory : ByteArray) (q : WordLane) : UInt256 :=
  UInt256.land lowerWord (MachineState.readWord memory 960 +
    (UInt256.shiftRight q.a (UInt256.ofNat 80) + (q.b + q.a)))
def result4 (memory : ByteArray) (q : WordLane) : UInt256 :=
  UInt256.land lowerWord (MachineState.readWord memory 832 +
    (UInt256.shiftRight q.c (UInt256.ofNat 80) +
      (q.a + UInt256.shiftRight q.b (UInt256.ofNat 80))))

def writeWord (memory : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) address

theorem writeWord_comm (memory : ByteArray) (a b : Nat) (va vb : UInt256)
    (hab : a + 32 ≤ b ∨ b + 32 ≤ a) :
    writeWord (writeWord memory a va) b vb =
      writeWord (writeWord memory b vb) a va :=
  Table80FinalBridge.writeWord_comm memory a b va vb hab


def resultMemory (memory : ByteArray) (q : WordLane) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord (writeWord memory
    864 (result1 memory q)) 896 (result2 memory q)) 928 (result3 memory q))
    960 (result4 memory q)) 832 (result0 memory q)

/-- Last-use consumed tail, exact103 bytes. -/
def template : List Instr :=
  [ .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 896),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
    .op .MSTORE,
    .op (.Swap ⟨3, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 928),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 896),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 960),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 928),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op (.Swap ⟨0, by decide⟩),
    .op (.Swap ⟨1, by decide⟩),
    .op .ADD,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 832),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 960),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 832),
    .op .MSTORE,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .JUMP ]

def prefixTemplate : List Instr := template.dropLast

theorem template_length : template.length = 77 := by decide
theorem template_bytes : (template.map Instr.size).sum = 103 := by decide
theorem prefix_bytes : (prefixTemplate.map Instr.size).sum = 102 := by decide

private def chunk0 : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 864),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND]

private def chunk1 : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 896),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 864),
   .op .MSTORE]

private def chunk2 : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 928),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 896),
   .op .MSTORE]

private def chunk3 : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 960),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 928),
   .op .MSTORE]

private def chunk4 : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 80),
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 832),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 960),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 832),
   .op .MSTORE]

private def chunk5 : List Instr :=
  [.op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

private def stack1 (q : WordLane) (factor ret r0 : UInt256) (rho : List UInt256) : List UInt256 :=
  [r0, q.d, q.b, q.c, q.a, q.e, factor, pairWord, upperWord, lowerWord] ++ (Table80Raw.cache ++ ret :: rho)

private def stack2 (q : WordLane) (factor ret r0 : UInt256) (rho : List UInt256) : List UInt256 :=
  [r0, q.b, q.c, q.a, q.e, factor, pairWord, upperWord, lowerWord] ++ (Table80Raw.cache ++ ret :: rho)

private def stack3 (q : WordLane) (factor ret r0 : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.b, q.c, q.a, r0, factor, pairWord, upperWord, lowerWord] ++ (Table80Raw.cache ++ ret :: rho)

private def stack4 (q : WordLane) (factor ret r0 : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.b, q.c, q.a, r0, factor, pairWord, upperWord, lowerWord] ++ (Table80Raw.cache ++ ret :: rho)

private def stack5 (_q : WordLane) (factor ret _r0 : UInt256) (rho : List UInt256) : List UInt256 :=
  [factor, pairWord, upperWord, lowerWord] ++ (Table80Raw.cache ++ ret :: rho)

private def stack6 (_q : WordLane) (_factor ret _r0 : UInt256) (rho : List UInt256) : List UInt256 :=
  ret :: rho

private theorem prefix_split : prefixTemplate = ((((chunk0 ++ chunk1) ++ chunk2) ++ chunk3) ++ chunk4) ++ chunk5 := rfl

private theorem run_chunk0 (s : State) (pc ret : UInt256) (q : WordLane) (factor _r0 : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq chunk0 {s with pc := pc, stack := entryStack factor q ret rho} =
      some {s with
        pc := pcAfter pc chunk0
        stack := stack1 q factor ret (result0 s.memory q) rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [chunk0, stack1, entryStack, Table80Raw.cache,
    combineWord, result0, result1, result2, result3, result4, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk0

private theorem run_chunk1 (s : State) (pc ret : UInt256) (q : WordLane) (factor r0 : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq chunk1 {s with pc := pc, stack := stack1 q factor ret r0 rho} =
      some {s with
        pc := pcAfter pc chunk1
        stack := stack2 q factor ret r0 rho
        memory := writeWord s.memory 864 (result1 s.memory q)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [chunk1, stack2, stack1, Table80Raw.cache,
    combineWord, result0, result1, result2, result3, result4, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk1

private theorem run_chunk2 (s : State) (pc ret : UInt256) (q : WordLane) (factor r0 : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq chunk2 {s with pc := pc, stack := stack2 q factor ret r0 rho} =
      some {s with
        pc := pcAfter pc chunk2
        stack := stack3 q factor ret r0 rho
        memory := writeWord s.memory 896 (result2 s.memory q)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [chunk2, stack3, stack2, Table80Raw.cache,
    combineWord, result0, result1, result2, result3, result4, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk2

private theorem run_chunk3 (s : State) (pc ret : UInt256) (q : WordLane) (factor r0 : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq chunk3 {s with pc := pc, stack := stack3 q factor ret r0 rho} =
      some {s with
        pc := pcAfter pc chunk3
        stack := stack4 q factor ret r0 rho
        memory := writeWord s.memory 928 (result3 s.memory q)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [chunk3, stack4, stack3, Table80Raw.cache,
    combineWord, result0, result1, result2, result3, result4, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk3

private theorem run_chunk4 (s : State) (pc ret : UInt256) (q : WordLane) (factor r0 : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq chunk4 {s with pc := pc, stack := stack4 q factor ret r0 rho} =
      some {s with
        pc := pcAfter pc chunk4
        stack := stack5 q factor ret r0 rho
        memory := writeWord (writeWord s.memory 960 (result4 s.memory q)) 832 r0} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [chunk4, stack5, stack4, Table80Raw.cache,
    combineWord, result0, result1, result2, result3, result4, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk4

private theorem run_chunk5 (s : State) (pc ret : UInt256) (q : WordLane) (factor r0 : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq chunk5 {s with pc := pc, stack := stack5 q factor ret r0 rho} =
      some {s with
        pc := pcAfter pc chunk5
        stack := stack6 q factor ret r0 rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [chunk5, stack6, stack5, Table80Raw.cache,
    combineWord, result0, result1, result2, result3, result4, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk5
private theorem pcAfter_append (pc : UInt256) (first second : List Instr) :
    pcAfter pc (first ++ second) = pcAfter (pcAfter pc first) second := by
  induction first generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, pcAfter]
      exact ih (pc := pc + UInt256.ofNat instruction.size)

private theorem runInstrSeq_append_running
    {first second : List Instr} {s middle result : State}
    (hfirst : runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hsecond : runInstrSeq second middle = some result) :
    runInstrSeq (first ++ second) s = some result := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, runInstrSeq] at hfirst ⊢
      cases hfirst
      exact hsecond
  | cons instruction rest ih =>
      cases hrun : Challenge.EvmProof.Stepper.runInstr instruction s with
      | none =>
          simp [runInstrSeq, hrun] at hfirst
      | some next =>
          cases rest with
          | nil =>
              have hnext : next = middle := by
                simpa [runInstrSeq, hrun] using hfirst
              subst middle
              cases second with
              | nil =>
                  simpa [runInstrSeq, hrun] using hsecond
              | cons nextInstruction secondRest =>
                  simpa [runInstrSeq, hrun, hmiddle] using hsecond
          | cons nextInstruction restTail =>
              cases hhalt : next.halt with
              | Running =>
                  have htail :
                      runInstrSeq (nextInstruction :: restTail) next = some middle := by
                    simpa [runInstrSeq, hrun, hhalt] using hfirst
                  have hjoined := ih (s := next) (middle := middle)
                    htail hmiddle hsecond
                  simpa [runInstrSeq, hrun, hhalt] using hjoined
              | Success =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Returned =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Reverted =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Exception error =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst

private theorem read_write_ne (memory : ByteArray) (a b : Nat) (v : UInt256)
    (h : a + 32 ≤ b ∨ b + 32 ≤ a) :
    MachineState.readWord (writeWord memory b v) a = MachineState.readWord memory a := by
  apply Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h

private def memory1 (memory : ByteArray) (q : WordLane) : ByteArray :=
  writeWord memory 864 (result1 memory q)
private def memory2 (memory : ByteArray) (q : WordLane) : ByteArray :=
  writeWord (memory1 memory q) 896 (result2 memory q)
private def memory3 (memory : ByteArray) (q : WordLane) : ByteArray :=
  writeWord (memory2 memory q) 928 (result3 memory q)

theorem run_prefix (s : State) (pc ret : UInt256) (q : WordLane) (factor : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := entryStack factor q ret rho} =
      some {s with
        pc := pcAfter pc prefixTemplate
        stack := ret :: rho
        memory := resultMemory s.memory q} := by
  have hr2 : result2 (memory1 s.memory q) q = result2 s.memory q := by
    unfold result2 combineWord memory1
    rw [read_write_ne _ 928 864 _ (Or.inr (by decide))]
  have hr3 : result3 (memory2 s.memory q) q = result3 s.memory q := by
    unfold result3 memory2 memory1
    rw [read_write_ne _ 960 896 _ (Or.inr (by decide)),
      read_write_ne _ 960 864 _ (Or.inr (by decide))]
  have hr4 : result4 (memory3 s.memory q) q = result4 s.memory q := by
    unfold result4 memory3 memory2 memory1
    rw [read_write_ne _ 832 928 _ (Or.inl (by decide)),
      read_write_ne _ 832 896 _ (Or.inl (by decide)),
      read_write_ne _ 832 864 _ (Or.inl (by decide))]
  let r0 := result0 s.memory q
  let s1 : State := {s with pc := pcAfter pc chunk0, stack := stack1 q factor ret r0 rho}
  let s2 : State := {s with pc := pcAfter s1.pc chunk1, stack := stack2 q factor ret r0 rho, memory := memory1 s.memory q}
  let s3 : State := {s with pc := pcAfter s2.pc chunk2, stack := stack3 q factor ret r0 rho, memory := memory2 s.memory q}
  let s4 : State := {s with pc := pcAfter s3.pc chunk3, stack := stack4 q factor ret r0 rho, memory := memory3 s.memory q}
  let s5 : State := {s with pc := pcAfter s4.pc chunk4, stack := stack5 q factor ret r0 rho, memory := resultMemory s.memory q}
  have h0 : runInstrSeq chunk0 {s with pc := pc, stack := entryStack factor q ret rho} = some s1 :=
    run_chunk0 s pc ret q factor r0 rho hstack hrun hactive
  have h1 : runInstrSeq chunk1 s1 = some s2 :=
    run_chunk1 s1 s1.pc ret q factor r0 rho hstack hrun hactive
  have h2 : runInstrSeq chunk2 s2 = some s3 := by
    have h := run_chunk2 s2 s2.pc ret q factor r0 rho hstack hrun hactive
    exact h.trans (congrArg (fun v => some {s2 with
      pc := pcAfter s2.pc chunk2
      stack := stack3 q factor ret r0 rho
      memory := writeWord (memory1 s.memory q) 896 v}) hr2)
  have h3 : runInstrSeq chunk3 s3 = some s4 := by
    have h := run_chunk3 s3 s3.pc ret q factor r0 rho hstack hrun hactive
    exact h.trans (congrArg (fun v => some {s3 with
      pc := pcAfter s3.pc chunk3
      stack := stack4 q factor ret r0 rho
      memory := writeWord (memory2 s.memory q) 928 v}) hr3)
  have h4 : runInstrSeq chunk4 s4 = some s5 := by
    have h := run_chunk4 s4 s4.pc ret q factor r0 rho hstack hrun hactive
    exact h.trans (congrArg (fun v => some {s4 with
      pc := pcAfter s4.pc chunk4
      stack := stack5 q factor ret r0 rho
      memory := writeWord (writeWord (memory3 s.memory q) 960 v) 832 r0}) hr4)
  have h5 := run_chunk5 s5 s5.pc ret q factor r0 rho hstack hrun hactive
  have h01 := runInstrSeq_append_running h0 hrun h1
  have h012 := runInstrSeq_append_running h01 hrun h2
  have h0123 := runInstrSeq_append_running h012 hrun h3
  have h01234 := runInstrSeq_append_running h0123 hrun h4
  have h012345 := runInstrSeq_append_running h01234 hrun h5
  rw [prefix_split]
  simpa only [pcAfter_append, s1, s2, s3, s4, s5, stack6] using h012345

theorem run_template (s : State) (pc ret : UInt256) (q : WordLane) (factor : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq template {s with pc := pc, stack := entryStack factor q ret rho} =
      some {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  have hp := run_prefix s pc ret q factor rho hstack hrun hactive
  have hj : runInstrSeq [.op .JUMP]
      {s with pc := pcAfter pc prefixTemplate, stack := ret :: rho, memory := resultMemory s.memory q} =
      some {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
    have hc : rho.length + 1 < 1024 := by omega
    simp [runInstrSeq, Stepper.runInstr, hrun, hvalid, hc]
  have h := runInstrSeq_append_running hp hrun hj
  have hs : template = prefixTemplate ++ [.op .JUMP] := rfl
  rw [hs]
  exact h


open Paired80Compression Paired80Algorithm

def normalLane (q : WordLane) : WordLane :=
  {q with b := packed32 (high32 q.b + low32 q.a) (low32 q.b + high32 q.a)}

theorem mask_normalize (x : UInt256) :
    UInt256.land lowerWord x = Challenge.EvmProof.Word.ofUInt32 (low32 x) := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm]
  exact Challenge.EvmProof.Word.mask32_eq_ofUInt32 x

theorem result3_eq (memory : ByteArray) (q : WordLane) :
    result3 memory q = Table80Tail.result3 memory (normalLane q) := by
  rw [result3, mask_normalize, Table80Tail.result3, Table80Tail.tail_combine_normalized]
  have hb : Challenge.EvmProof.Word.toUInt32
      (UInt256.shiftRight (normalLane q).b (UInt256.ofNat 80)) =
      low32 q.b + high32 q.a := high32_packed _ _
  rw [hb]
  simp only [normalLane]
  change Challenge.EvmProof.Word.ofUInt32
      (Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory 960 +
        (UInt256.shiftRight q.a (UInt256.ofNat 80) + (q.b + q.a)))) = _
  simp only [Challenge.EvmProof.Word.toUInt32_add]
  congr 1
  change low32 (MachineState.readWord memory 960) + (high32 q.a + (low32 q.b + low32 q.a)) =
    low32 (MachineState.readWord memory 960) + ((low32 q.b + high32 q.a) + low32 q.a)
  rw [← UInt32.add_assoc (high32 q.a) (low32 q.b) (low32 q.a),
    UInt32.add_comm (high32 q.a) (low32 q.b)]

theorem result4_eq (memory : ByteArray) (q : WordLane) :
    result4 memory q = Table80Tail.result4 memory (normalLane q) := by
  rw [result4, mask_normalize, Table80Tail.result4, Table80Tail.tail_combine_normalized]
  have hb : Challenge.EvmProof.Word.toUInt32 (normalLane q).b =
      high32 q.b + low32 q.a := low32_packed _ _
  rw [hb]
  simp only [normalLane]
  change Challenge.EvmProof.Word.ofUInt32
      (Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory 832 +
        (UInt256.shiftRight q.c (UInt256.ofNat 80) +
          (q.a + UInt256.shiftRight q.b (UInt256.ofNat 80))))) = _
  simp only [Challenge.EvmProof.Word.toUInt32_add]
  congr 1
  change low32 (MachineState.readWord memory 832) + (high32 q.c + (low32 q.a + high32 q.b)) =
    low32 (MachineState.readWord memory 832) + (high32 q.c + (high32 q.b + low32 q.a))
  rw [UInt32.add_comm (low32 q.a)]

/-- Entire output memory, with no normalization or bounds premise on q. -/
theorem resultMemory_eq (memory : ByteArray) (q : WordLane) :
    resultMemory memory q = Table80Tail.resultMemory memory (normalLane q) := by
  unfold resultMemory
  rw [writeWord_comm _ 864 896 _ _ (Or.inl (by decide)),
    writeWord_comm _ 864 928 _ _ (Or.inl (by decide)),
    writeWord_comm _ 864 960 _ _ (Or.inl (by decide)),
    writeWord_comm _ 896 928 _ _ (Or.inl (by decide)),
    writeWord_comm _ 896 960 _ _ (Or.inl (by decide)),
    writeWord_comm _ 928 960 _ _ (Or.inl (by decide))]
  simp only [Table80Tail.resultMemory, result3_eq, result4_eq]
  rfl

#print axioms resultMemory_eq

#print axioms run_prefix
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80ConsumedTerminalTail

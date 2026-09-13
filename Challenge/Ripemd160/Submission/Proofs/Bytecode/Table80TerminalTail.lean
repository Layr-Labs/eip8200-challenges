import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalWord
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTail
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

def resultMemory (memory : ByteArray) (q : WordLane) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord (writeWord memory
    960 (result4 memory q)) 928 (result3 memory q)) 896 (result2 memory q))
    864 (result1 memory q)) 832 (result0 memory q)

/-- Generic tail with deferred final addition; exact 107 bytes. -/
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
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 896),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 928),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨11, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 960),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨12, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op (.Dup ⟨8, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 832),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨13, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 960),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 928),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 896),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 864),
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
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .JUMP ]

def prefixTemplate : List Instr := template.dropLast

theorem template_length : template.length = 81 := by decide
theorem template_bytes : (template.map Instr.size).sum = 107 := by decide
theorem prefix_bytes : (prefixTemplate.map Instr.size).sum = 106 := by decide

theorem run_prefix (s : State) (pc ret : UInt256) (q : WordLane) (factor : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := entryStack factor q ret rho} =
      some {s with
        pc := pcAfter pc prefixTemplate
        stack := ret :: rho
        memory := resultMemory s.memory q} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, prefixTemplate, entryStack, Table80Raw.cache, combineWord,
    result0, result1, result2, result3, result4, resultMemory, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, pcAfter, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl

theorem run_template (s : State) (pc ret : UInt256) (q : WordLane) (factor : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq template {s with pc := pc, stack := entryStack factor q ret rho} =
      some {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := Table80Raw.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, entryStack, Table80Raw.cache, combineWord,
    result0, result1, result2, result3, result4, resultMemory, writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    State.activeWordsAfterUInt256, hactiveAt, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl


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
  simp only [resultMemory, Table80Tail.resultMemory, result3_eq, result4_eq]
  rfl

#print axioms resultMemory_eq

#print axioms run_prefix
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTail

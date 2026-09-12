import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalWord
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace Paired80WordRound Paired80WordBoolean Paired80WordRotate

def entryStack (q : WordLane) (ret : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.a, q.e, factorWord, pairWord, upperWord, lowerWord] ++
    (Table80Raw.cache ++ ret :: rho)

def combineWord (memory : ByteArray) (address : Nat) (left right : UInt256) : UInt256 :=
  UInt256.land lowerWord (UInt256.add (MachineState.readWord memory address)
    (UInt256.add (UInt256.shiftRight right (UInt256.ofNat 80)) left))

def result0 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 864 q.c q.d
def result1 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 896 q.d q.e
def result2 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 928 q.e q.a
def result3 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 960 q.a q.b
def result4 (memory : ByteArray) (q : WordLane) : UInt256 := combineWord memory 832 q.b q.c

def writeWord (memory : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) address

def resultMemory (memory : ByteArray) (q : WordLane) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord (writeWord memory
    960 (result4 memory q)) 928 (result3 memory q)) 896 (result2 memory q))
    864 (result1 memory q)) 832 (result0 memory q)

/-- Exact raw byte interval4603..4704; JUMP is at4703. -/
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
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 960),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨12, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
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
    .op .POP,
    .op .JUMP ]

def prefixTemplate : List Instr := template.dropLast

theorem template_length : template.length = 76 := by decide
theorem template_bytes : (template.map Instr.size).sum = 101 := by decide
theorem prefix_bytes : (prefixTemplate.map Instr.size).sum = 100 := by decide

theorem run_prefix (s : State) (pc ret : UInt256) (q : WordLane)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := entryStack q ret rho} =
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

theorem run_template (s : State) (pc ret : UInt256) (q : WordLane)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq template {s with pc := pc, stack := entryStack q ret rho} =
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

#print axioms run_prefix
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail

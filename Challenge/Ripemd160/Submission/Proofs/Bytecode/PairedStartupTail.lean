import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.EvmProof.Memory

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace DenseScheduleTemplate

def lowerWord : UInt256 := UInt256.ofNat 0xffffffff
def upperWord : UInt256 := UInt256.ofNat 0xffffffff00000000000000000000000000000000
def pairWord : UInt256 := UInt256.ofNat 0xffffffff000000000000000000000000ffffffff
def factorWord : UInt256 := UInt256.ofNat 0x0100000001

def cacheTemplate : List Instr :=
  [.push ⟨4, by decide⟩ lowerWord,
   .push ⟨20, by decide⟩ upperWord,
   .push ⟨20, by decide⟩ pairWord,
   .push ⟨5, by decide⟩ factorWord]

def loadTemplate (address : Nat) (dup : Operation.DupOp) : List Instr :=
  [push2 (UInt256.ofNat address), .op .MLOAD, .op (.Dup dup), .op .AND,
   dup1, push1 (UInt256.ofNat 128), .op .SHL, .op .OR]

/-- Exact physical instructions 857..960 of the frozen 5315-byte candidate. -/
def template : List Instr :=
  cacheTemplate ++ loadTemplate 672 ⟨4, by decide⟩ ++
    loadTemplate 640 ⟨5, by decide⟩ ++ loadTemplate 608 ⟨6, by decide⟩ ++
    loadTemplate 576 ⟨7, by decide⟩ ++ loadTemplate 544 ⟨8, by decide⟩

/-- Arbitrary 256-bit words are explicitly normalized before duplicating lanes. -/
def packedHash (memory : ByteArray) (address : Nat) : UInt256 :=
  let value := UInt256.land lowerWord (MachineState.readWord memory address)
  UInt256.lor (UInt256.shiftLeft value (UInt256.ofNat 128)) value

def resultStack (memory : ByteArray) (rho : List UInt256) : List UInt256 :=
  [packedHash memory 544, packedHash memory 576, packedHash memory 608,
    packedHash memory 640, packedHash memory 672,
    factorWord, pairWord, upperWord, lowerWord] ++ rho

theorem active_preserved (current : UInt256) (address : Nat)
    (hcurrent : 23 ≤ current.toNat) (haddress : address ≤ 672) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have hwords : (address + 32 - 1) / 32 + 1 ≤ current.toNat := by omega
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  change UInt256.ofNat (max current.toNat ((address + 32 - 1) / 32 + 1)) = current
  rw [Nat.max_eq_left hwords]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat current).symm

theorem template_length : template.length = 44 := by
  norm_num [template, cacheTemplate, loadTemplate]

theorem template_bytes : (template.map Instr.size).sum = 108 := by
  norm_num [template, cacheTemplate, loadTemplate, push1, push2, dup1, Instr.size]

theorem run_template (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc template, stack := resultStack s.memory rho} := by
  have hcap (n : Nat) (hn : n ≤ 11) : rho.length + n < 1024 := by omega
  have h0 : rho.length < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 672) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, cacheTemplate, loadTemplate, push1, push2, dup1,
    packedHash, resultStack, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, h0, Nat.add_assoc,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rfl

#print axioms active_preserved
#print axioms template_length
#print axioms template_bytes
#print axioms run_template


open Challenge.EvmProof StackRoundTemplate

def frozenInstructions : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .push ⟨20, by decide⟩ (UInt256.ofNat 0xffffffff00000000000000000000000000000000),
   .push ⟨20, by decide⟩ (UInt256.ofNat 0xffffffff000000000000000000000000ffffffff),
   .push ⟨5, by decide⟩ (UInt256.ofNat 0x0100000001),
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x2a0),
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x280),
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x260),
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x240),
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x220),
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR]

theorem template_eq_frozenInstructions : template = frozenInstructions := by
  rfl

theorem template_advances :
    ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  rw [template_eq_frozenInstructions] at hmem
  simp only [frozenInstructions, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.and)
    | exact Or.inl (Or.inl StraightLine.or)
    | exact Or.inl (Or.inl StraightLine.shl)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl (StraightLine.dup _))

theorem runLocatedBlock_template {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      some {s with pc := site.endPC, stack := resultStack s.memory rho} := by
  have hend : site.endPC = pcAfter site.startPC template := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [DenseScheduleLift.runLocatedBlock_eq_raw site template_advances
    {s with pc := site.startPC, stack := rho} rfl]
  have h := run_template s site.startPC rho hstack hrun hactive
  rw [← hend] at h
  exact h

def gasSteps_template {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := rho}
      {s with pc := site.endPC, stack := resultStack s.memory rho} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_template site s rho hstack hrun hactive
  · exact hrun
  · exact hnp

#print axioms template_eq_frozenInstructions
#print axioms template_advances
#print axioms runLocatedBlock_template
#print axioms gasSteps_template

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedTailTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedStartupTrace

/-- The three unused cached values are arbitrary. -/
structure Frame where
  a : UInt256
  b : UInt256
  c : UInt256
  unused3 : UInt256
  e : UInt256
  unused5 : UInt256
  lower : UInt256
  unused6 : UInt256
  d : UInt256

def entryStack (q : Frame) (ret : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.unused3, q.e, q.unused5, q.unused6, q.a, q.lower, ret] ++ rho

/-- All five chaining combinations read the original memory before any store. -/
def combine (memory : ByteArray) (address : Nat) (lower left right : UInt256) : UInt256 :=
  UInt256.land lower (UInt256.add (MachineState.readWord memory address)
    (UInt256.add (UInt256.shiftRight right (UInt256.ofNat 128)) left))

def result0 (memory : ByteArray) (q : Frame) : UInt256 := combine memory 576 q.lower q.c q.d
def result1 (memory : ByteArray) (q : Frame) : UInt256 := combine memory 608 q.lower q.d q.e
def result2 (memory : ByteArray) (q : Frame) : UInt256 := combine memory 640 q.lower q.e q.a
def result3 (memory : ByteArray) (q : Frame) : UInt256 := combine memory 672 q.lower q.a q.b
def result4 (memory : ByteArray) (q : Frame) : UInt256 := combine memory 544 q.lower q.b q.c

def writeWord (memory : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) address

def resultMemory (memory : ByteArray) (q : Frame) : ByteArray :=
  writeWord (writeWord (writeWord (writeWord (writeWord memory
    672 (result4 memory q)) 640 (result3 memory q)) 608 (result2 memory q))
    576 (result1 memory q)) 544 (result0 memory q)

/-- Exact physical bytes5083..5231 (or relocated5068..5153), including the final indirect return. -/
def template : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x240),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x260),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x280),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x2a0),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x220),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x2a0),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x280),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x260),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x240),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x220),
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
   .op .JUMP]

theorem tail_template_length : template.length = 70 := by
  norm_num [template]

theorem tail_template_bytes : (template.map Instr.size).sum = 95 := by
  norm_num [template, Instr.size]

theorem run_tail_template (s : State) (pc ret : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq template {s with pc := pc, stack := entryStack q ret rho} =
      some {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 672) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := PairedStartupTrace.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, entryStack, combine,
    result0, result1, result2, result3, result4, resultMemory, writeWord,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    State.activeWordsAfterUInt256, hactiveAt, hvalid,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rfl

#print axioms tail_template_length
#print axioms tail_template_bytes
#print axioms run_tail_template


open Challenge.EvmProof

theorem tail_read_writeWord (memory : ByteArray) (address : Nat) (value : UInt256) :
    MachineState.readWord (writeWord memory address value) address = value :=
  Memory.readWord_writeWord memory address value

theorem tail_read_writeWord_disjoint (memory : ByteArray) (readStart writeStart : Nat)
    (value : UInt256)
    (hdisjoint : readStart + 32 ≤ writeStart ∨ writeStart + 32 ≤ readStart) :
    MachineState.readWord (writeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

theorem tail_read_results (memory : ByteArray) (q : Frame) :
    MachineState.readWord (resultMemory memory q) 544 = result0 memory q ∧
    MachineState.readWord (resultMemory memory q) 576 = result1 memory q ∧
    MachineState.readWord (resultMemory memory q) 608 = result2 memory q ∧
    MachineState.readWord (resultMemory memory q) 640 = result3 memory q ∧
    MachineState.readWord (resultMemory memory q) 672 = result4 memory q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (discharger := omega)
    [resultMemory, tail_read_writeWord, tail_read_writeWord_disjoint]

theorem tail_readPadded_writeWord_disjoint (memory : ByteArray)
    (readStart readSize writeStart : Nat) (value : UInt256)
    (hdisjoint : readStart + readSize ≤ writeStart ∨ writeStart + 32 ≤ readStart) :
    MachineState.readPadded (writeWord memory writeStart value) readStart readSize =
      MachineState.readPadded memory readStart readSize := by
  apply Memory.readPadded_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

theorem tail_readPadded_outside (memory : ByteArray) (q : Frame) (address size : Nat)
    (houtside : address + size ≤ 544 ∨ 704 ≤ address) :
    MachineState.readPadded (resultMemory memory q) address size =
      MachineState.readPadded memory address size := by
  simp (discharger := omega) [resultMemory, tail_readPadded_writeWord_disjoint]

theorem tail_getD_writeWord_outside (memory : ByteArray) (readAt writeAt : Nat)
    (value : UInt256) (houtside : readAt < writeAt ∨ writeAt + 32 ≤ readAt) :
    (writeWord memory writeAt value)[readAt]?.getD 0 = memory[readAt]?.getD 0 := by
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega)]

theorem tail_getD_outside (memory : ByteArray) (q : Frame) (address : Nat)
    (houtside : address < 544 ∨ 704 ≤ address) :
    (resultMemory memory q)[address]?.getD 0 = memory[address]?.getD 0 := by
  simp (discharger := omega) [resultMemory, tail_getD_writeWord_outside]

theorem tail_writeWord_size (memory : ByteArray) (address : Nat) (value : UInt256) :
    (writeWord memory address value).size = max memory.size (address + 32) := by
  simp only [writeWord, MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    if_neg (by decide : (32 : Nat) ≠ 0)]

theorem tail_resultMemory_size (memory : ByteArray) (q : Frame) :
    (resultMemory memory q).size = max memory.size 704 := by
  simp only [resultMemory, tail_writeWord_size]
  omega

theorem tail_resultMemory_size_of_ge (memory : ByteArray) (q : Frame)
    (hsize : 704 ≤ memory.size) : (resultMemory memory q).size = memory.size := by
  rw [tail_resultMemory_size, Nat.max_eq_left hsize]

theorem tail_combine_normalized (memory : ByteArray) (address : Nat) (left right : UInt256) :
    combine memory address lowerWord left right =
      Challenge.EvmProof.Word.ofUInt32
        (Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory address) +
          (Challenge.EvmProof.Word.toUInt32 (UInt256.shiftRight right (UInt256.ofNat 128)) +
            Challenge.EvmProof.Word.toUInt32 left)) := by
  unfold combine
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.Word.land_comm]
  change Challenge.EvmProof.Word.mask32
    (MachineState.readWord memory address +
      (UInt256.shiftRight right (UInt256.ofNat 128) + left)) = _
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.toUInt32_add, Challenge.EvmProof.Word.toUInt32_add]

#print axioms tail_read_writeWord
#print axioms tail_read_writeWord_disjoint
#print axioms tail_read_results
#print axioms tail_readPadded_writeWord_disjoint
#print axioms tail_readPadded_outside
#print axioms tail_getD_writeWord_outside
#print axioms tail_getD_outside
#print axioms tail_writeWord_size
#print axioms tail_resultMemory_size
#print axioms tail_resultMemory_size_of_ge
#print axioms tail_combine_normalized


open StackRoundTemplate

def prefixTemplate : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x240),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x260),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x280),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x2a0),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .op .ADD,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x220),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x2a0),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x280),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x260),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x240),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x220),
   .op .MSTORE,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

theorem tail_prefix_append_jump : prefixTemplate ++ [.op .JUMP] = template := by
  rfl

theorem run_tail_prefix (s : State) (pc ret : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := entryStack q ret rho} =
      some {s with
        pc := pcAfter pc prefixTemplate
        stack := ret :: rho
        memory := resultMemory s.memory q} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 672) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := PairedStartupTrace.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [prefixTemplate, entryStack, combine,
    result0, result1, result2, result3, result4, resultMemory, writeWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    State.activeWordsAfterUInt256, hactiveAt, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl⟩

theorem tail_prefix_advances :
    ∀ instruction ∈ prefixTemplate, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [prefixTemplate, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.add)
    | exact Or.inl (Or.inl StraightLine.and)
    | exact Or.inl (Or.inl StraightLine.shr)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl StraightLine.pop)
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inr (Or.inl rfl)

theorem runLocatedBlock_tail_prefix {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork prefixTemplate)
    (s : State) (ret : UInt256) (q : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := entryStack q ret rho} =
      some {s with pc := site.endPC, stack := ret :: rho, memory := resultMemory s.memory q} := by
  have hend : site.endPC = pcAfter site.startPC prefixTemplate := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [DenseScheduleLift.runLocatedBlock_eq_raw site tail_prefix_advances
    {s with pc := site.startPC, stack := entryStack q ret rho} rfl]
  have h := run_tail_prefix s site.startPC ret q rho hstack hrun hactive
  rw [← hend] at h
  exact h

structure TailSite (artifact : ProgramArtifact) (fork : Fork) where
  prefixSite : GenericRoundSite artifact fork prefixTemplate
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = prefixSite.endPC

def TailSite.path {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) : List (Stepper.Located artifact fork) :=
  site.prefixSite.path ++ [site.jump.located]

theorem runLocatedBlock_tail {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) (s : State) (ret : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Stepper.runLocatedBlock site.path
      {s with pc := site.prefixSite.startPC, stack := entryStack q ret rho} =
      some {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  apply Stepper.runLocatedBlock_append site.prefixSite.path [site.jump.located]
    _ {s with
      pc := site.prefixSite.endPC
      stack := ret :: rho
      memory := resultMemory s.memory q}
  · exact runLocatedBlock_tail_prefix site.prefixSite s ret q rho hstack hrun hactive
  · exact hrun
  · have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr
      {s with memory := resultMemory s.memory q} ret rho (by omega) hvalid
    rw [site.jump_pc] at h
    simp only [Stepper.runLocatedBlock, h]

def gasSteps_tail {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) (s : State) (ret : UInt256) (q : Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.prefixSite.startPC, stack := entryStack q ret rho}
      {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_tail site s ret q rho hstack hrun hactive hvalid
  · exact hrun
  · exact hnp

#print axioms tail_prefix_append_jump
#print axioms run_tail_prefix
#print axioms tail_prefix_advances
#print axioms runLocatedBlock_tail_prefix
#print axioms runLocatedBlock_tail
#print axioms gasSteps_tail

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedTailTrace

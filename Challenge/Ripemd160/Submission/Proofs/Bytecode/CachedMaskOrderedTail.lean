import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskOrderedTail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word
open QuadTailTemplate QuadSwapLemmas StackRoundTemplate

abbrev runInstrSeq := StackRoundTrace.runInstrSeq

open private
  activeWordsAfter_tail
  readWord_writeHashWord_disjoint
  read96_write64
  read128_write64
  read128_write96
  read160_write64
  read160_write96
  read160_write128
  read32_write64
  read32_write96
  read32_write128
  read32_write160
  mask32_push
  add3_comm_right
  tailCapacity
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume

theorem writeHashWord_comm (bs : ByteArray) (first second a b : Nat)
    (hab : a + 32 ≤ b) :
    MachineState.writeBytes
      (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded second 32) b)
      (Data.Bytes.natToBytesPadded first 32) a =
    MachineState.writeBytes
      (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded first 32) a)
      (Data.Bytes.natToBytesPadded second 32) b := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    simp [Nat.max_comm, Nat.max_left_comm]
  · intro i hleft hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright]
    simp only [MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases hfirst : a ≤ i ∧ i < a + 32
    · rw [if_pos hfirst, if_neg (by omega), if_pos hfirst]
    · by_cases hsecond : b ≤ i ∧ i < b + 32
      · rw [if_neg hfirst, if_pos hsecond, if_pos hsecond]
      · rw [if_neg hfirst, if_neg hsecond, if_neg hsecond, if_neg hfirst]

theorem add_assoc (u v w : UInt256) : (u + v) + w = u + (v + w) := by
  apply Word.word_ext
  change ((u.val + v.val) + w.val).val = (u.val + (v.val + w.val)).val
  simp [Fin.add_def, Nat.add_assoc]

theorem add_left_comm (u v w : UInt256) : u + (v + w) = v + (u + w) := by
  rw [← add_assoc, Word.word_add_comm u v, add_assoc]

#print axioms writeHashWord_comm

def template : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .push 1 (UInt256.ofNat 32),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .push 1 (UInt256.ofNat 64),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push 1 (UInt256.ofNat 32),
   .op .MSTORE,
   .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .push 1 (UInt256.ofNat 128),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .push 1 (UInt256.ofNat 160),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .push 1 (UInt256.ofNat 128),
   .op .MSTORE,
   .push 1 (UInt256.ofNat 160),
   .op .MSTORE,
   .op .ADD,
   .push 1 (UInt256.ofNat 96),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 1 (UInt256.ofNat 64),
   .op .MSTORE,
   .push 1 (UInt256.ofNat 96),
   .op .MSTORE,
   .op .POP,
   .op .JUMP]

def entry (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) : State :=
  {s with pc := tailStartPC, stack := workingStack left right mask (ret :: rest)}

set_option linter.unusedSimpArgs false in
theorem run (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256)
    (rest : List UInt256)
    (hrun : s.halt = .Running)
    (_hfork : s.fork = .Osaka)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1006)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq template (entry s left right ret rest) =
      some (finalResult s left right ret rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hcap8 : rest.length + 8 < 1024 := by omega
  have hcap9 : rest.length + 9 < 1024 := by omega
  have hcap10 : rest.length + 10 < 1024 := by omega
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hcap16 : rest.length + 16 < 1024 := by omega
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [runInstrSeq, StackRoundTrace.runInstrSeq, template, quadTailBeforeJumpTemplate,
      c0Instructions, c1Instructions, c2Instructions, c3Instructions,
      c4Instructions, storeH0Instructions, cleanupInstructions,
      swap5H, swap6H, swap7H, swap1, swap2, swap3, op, push1, push4, mask,
      entry, tailEntry, workingStack, tailStartPC, tailJumpPC, factor,
      finalResult, beforeJumpResult, StackTail.preJumpResult, StackTail.combined,
      Challenge.EvmProof.Stepper.runInstr, StackMemory.storeHash,
      activeWordsAfter_tail, readWord_writeHashWord_disjoint,
      read96_write64, read128_write64, read128_write96, read160_write64,
      read160_write96, read160_write128, read32_write64, read32_write96,
      read32_write128, read32_write160, mask32_push,
      exchange_swap1, exchange_swap2, exchange_swap3, exchange_swap5,
      exchange_swap6, exchange_swap7, exchange_swap8, exchange_swap4, hrun, hactive, hstack, hvalid,
      hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, hcap7, hcap8, hcap9,
      hcap10, hcap11, hcap12, hcap13, hcap14, hcap15, hcap16,
      add_assoc, add_left_comm, Word.word_add_comm, Nat.add_assoc,
      writeHashWord_comm,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Challenge.EvmProof.Word.mask32_toNat, Compression.evmCombine,
      StackMemory.hashAt]
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    simp [Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]
  · intro i hleft hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright]
    simp only [MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> first | rfl | omega


#print axioms run

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskOrderedTail

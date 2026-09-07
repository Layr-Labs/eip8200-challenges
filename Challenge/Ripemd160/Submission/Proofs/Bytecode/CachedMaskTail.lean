import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadTailConsume
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskTail

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

def template : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨6, by decide⟩),
   .push 1 (UInt256.ofNat 64),
   .op .MLOAD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨6, by decide⟩),
   .push 1 (UInt256.ofNat 96),
   .op .MLOAD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push 1 (UInt256.ofNat 64),
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .push 1 (UInt256.ofNat 128),
   .op .MLOAD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .push 1 (UInt256.ofNat 96),
   .op .MSTORE,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .push 1 (UInt256.ofNat 160),
   .op .MLOAD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .push 1 (UInt256.ofNat 128),
   .op .MSTORE,
   .push 1 (UInt256.ofNat 32),
   .op .MLOAD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 1 (UInt256.ofNat 160),
   .op .MSTORE,
   .push 1 (UInt256.ofNat 32),
   .op .MSTORE,
   .op .POP,
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
    (hactive : 61 ≤ s.activeWords.toNat)
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
      exchange_swap6, exchange_swap7, hrun, hactive, hstack, hvalid,
      hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, hcap7, hcap8, hcap9,
      hcap10, hcap11, hcap12, hcap13, hcap14, hcap15, hcap16,
      add3_comm_right, Nat.add_assoc,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Challenge.EvmProof.Word.mask32_toNat, Compression.evmCombine,
      StackMemory.hashAt]


#print axioms run

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskTail

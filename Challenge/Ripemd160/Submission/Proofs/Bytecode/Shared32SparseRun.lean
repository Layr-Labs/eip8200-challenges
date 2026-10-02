import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Lower
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory Pair13Endian
open Shared32Scratch

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

/-- `PUSH0 SWAP13 DUP1 ADD` at 113: zero the limit slot (the single block then finishes on its
own offset) and double the old limit `1088` into the sentinel value `0x880`. -/
def headTemplate : List Instr :=
  [ .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op (.Swap ⟨12, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    .op .ADD ]

theorem run_head (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running) :
    runInstrSeq headTemplate
      {s with
        pc := pc
        stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho} =
      some {s with
        pc := pcAfter pc headTemplate
        stack := (lim + lim) ::
          stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) (UInt256.ofNat 0) rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [headTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, stk, Nat.add_assoc,
    List.getElem?_cons_zero, List.exchange, add_eq_hAdd]
  rfl

/-- The two sparse padding bytes: the doubled limit's low byte `0x80` at 165 and `1` at 188. -/
def template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 165),
    .op .MSTORE8,
    .push ⟨1, by decide⟩ (UInt256.ofNat 1),
    .push ⟨1, by decide⟩ (UInt256.ofNat 188),
    .op .MSTORE8 ]

theorem run_sparse (s : State) (pc v : UInt256) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34)
    (hbyte : UInt8.ofNat (v.toNat % 256) = 128) :
    runInstrSeq template {s with pc := pc, stack := v :: F} =
      some {s with
        pc := pcAfter pc template
        stack := F
        memory := sparseMemory s.memory} := by
  have hcap (n : Nat) (hn : n ≤ 27) : F.length + n < 1024 := by omega
  have hcap0 : F.length < 1024 := by omega
  simp (discharger := omega) [template, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, hcap0, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256,
    hactive, MachineState.activeWordsAfter, hbyte, sparseMemory, add_eq_hAdd]

theorem bytes_exact : assembleBytes template = [96,165,83,96,1,96,188,83] := by decide

theorem sparse_read_input (input : ByteArray) (hn : 0 < input.size) :
    MachineState.readWord (sparseMemory (copiedMemory input)) 1056 =
      MachineState.readWord (copiedMemory input) 1056 := by
  rw [copiedMemory_sparse input hn]
  exact read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))

#print axioms run_head
#print axioms run_sparse
#print axioms bytes_exact
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun

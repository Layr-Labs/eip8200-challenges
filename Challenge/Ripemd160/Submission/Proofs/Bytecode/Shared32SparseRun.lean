import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
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

/-- `PUSH2 0x1280 SWAP13 POP` at 144: the continuation slot becomes the output entry 4736 (the
single block then jumps straight to the output). -/
def headTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 4729),
    .op (.Swap ⟨12, by decide⟩),
    .op .POP ]

theorem run_head (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running) :
    runInstrSeq headTemplate
      {s with
        pc := pc
        stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho} =
      some {s with
        pc := pcAfter pc headTemplate
        stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) (UInt256.ofNat 4729) rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [headTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, stk, Nat.add_assoc,
    List.getElem?_cons_zero, List.exchange]
  rfl

/-- The `PUSH1 0x80` at 149: the sentinel byte for 165. -/
def foldTemplate : List Instr := [ .push ⟨1, by decide⟩ (UInt256.ofNat 128) ]

theorem run_fold (s : State) (pc : UInt256) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running) :
    runInstrSeq foldTemplate {s with pc := pc, stack := F} =
      some {s with pc := pcAfter pc foldTemplate, stack := UInt256.ofNat 128 :: F} := by
  have hcap : F.length < 1024 := by omega
  simp [foldTemplate, runInstrSeq, DataStepper.runInstr, pcAfter, hrun, hcap, Instr.size,
    UInt256.succ, Word.literal_eq_ofNat]

/-- The two sparse padding bytes: `0x80` at 165 and the low byte `1` of the resident coefficient
word in stack slot 4 at 188. -/
def template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 165),
    .op .MSTORE8,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 188),
    .op .MSTORE8 ]

theorem run_sparse (s : State) (pc v x0 x1 x2 x3 x4 : UInt256) (G : List UInt256)
    (hstack : G.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 34)
    (hbyte : UInt8.ofNat (v.toNat % 256) = 128)
    (hone : UInt8.ofNat (x4.toNat % 256) = 1) :
    runInstrSeq template {s with pc := pc, stack := v :: x0 :: x1 :: x2 :: x3 :: x4 :: G} =
      some {s with
        pc := pcAfter pc template
        stack := x0 :: x1 :: x2 :: x3 :: x4 :: G
        memory := sparseMemory s.memory} := by
  have hcap (n : Nat) (hn : n ≤ 27) : G.length + n < 1024 := by omega
  have hcap0 : G.length < 1024 := by omega
  simp (discharger := omega) [template, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, hcap0, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256,
    hactive, MachineState.activeWordsAfter, hbyte, hone, sparseMemory, add_eq_hAdd]

theorem bytes_exact : Challenge.EvmProof.PcEncoding.assembleBytes template = [96,165,83,132,96,188,83] := by decide

theorem sparse_read_input (input : ByteArray) (hn : 0 < input.size) :
    MachineState.readWord (sparseMemory (copiedMemory input)) 1056 =
      MachineState.readWord (copiedMemory input) 1056 := by
  rw [copiedMemory_sparse input hn]
  exact read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))

#print axioms run_head
#print axioms run_fold
#print axioms run_sparse
#print axioms bytes_exact
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun

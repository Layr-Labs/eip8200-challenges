import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Lower
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory Pair13Endian
open Shared32Scratch

def template : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 63), .op .MSTORE8,
   .op (.Dup ⟨4, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 86), .op .MSTORE8]

theorem run_sparse (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running)
    (hactive : s.activeWords = UInt256.ofNat 36)
    (hbyte : UInt8.ofNat (a4.toNat % 256) = 1) :
    runInstrSeq template
      {s with
        pc := pc
        stack := UInt256.ofNat 1152 ::
          stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho} =
      some {s with
        pc := pcAfter pc template
        stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 0) lim rho
        memory := sparseMemory s.memory} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, stk, Nat.add_assoc,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256,
    hactive, MachineState.activeWordsAfter, hbyte, sparseMemory]
  rfl

theorem bytes_exact : assembleBytes template = [96,63,83,132,96,86,83] := by decide

theorem sparse_read_input (input : ByteArray) (hn : 0 < input.size) :
    MachineState.readWord (sparseMemory (copiedMemory input)) 1120 =
      MachineState.readWord (copiedMemory input) 1120 := by
  rw [copiedMemory_sparse input hn]
  exact read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))

theorem sparse_lower_memory (input : ByteArray) (hn : 0 < input.size) :
    writeWord (sparseMemory (copiedMemory input)) 28
      (PairedScheduleData.reversedWord
        (MachineState.readWord (sparseMemory (copiedMemory input)) 1120)) =
      StaggerScratch.scratchMemory (copiedMemory input)
        (PairedScheduleData.reversedWord (MachineState.readWord (copiedMemory input) 1120))
        highWord := by
  rw [sparse_read_input input hn, copiedMemory_sparse input hn]
  rfl

#print axioms run_sparse
#print axioms bytes_exact
#print axioms sparse_lower_memory
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun

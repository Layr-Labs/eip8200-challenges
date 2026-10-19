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

/-- `PUSH2 9667 SWAP13 PUSH1 32 EQ` at144: the continuation slot becomes the output entry 9667 (the
single block then jumps straight to the output). The displaced length is retained as the 32-byte predicate. -/
def headTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 9667),
    .op (.Swap ⟨12, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .EQ ]

theorem run_head (s : State) (pc ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 lim : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 880) (hrun : s.halt = .Running) :
    runInstrSeq headTemplate
      {s with
        pc := pc
        stack := stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) lim rho} =
      some {s with
        pc := pcAfter pc headTemplate
        stack := UInt256.eq (UInt256.ofNat 32) lim :: stk ret mw a2 a3 a4 a5 a6 a7 a8 a9 a10 (UInt256.ofNat 1056) (UInt256.ofNat 9667) rho} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [headTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, stk, Nat.add_assoc,
    List.getElem?_cons_zero, List.exchange]
  rfl

/-- The `PUSH1 0x80` at151: the sentinel byte for 165. -/
def foldTemplate : List Instr := [ .push ⟨1, by decide⟩ (UInt256.ofNat 32) ]

theorem run_fold (s : State) (pc : UInt256) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running) :
    runInstrSeq foldTemplate {s with pc := pc, stack := F} =
      some {s with pc := pcAfter pc foldTemplate, stack := UInt256.ofNat 32 :: F} := by
  have hcap : F.length < 1024 := by omega
  simp [foldTemplate, runInstrSeq, DataStepper.runInstr, pcAfter, hrun, hcap, Instr.size,
    UInt256.succ, Word.literal_eq_ofNat]

/-- The two sparse padding bytes: `0x80` at 165 and the low byte `1` of the resident coefficient
word (below the retained flag) at188. -/
def template : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 5000),
   .push ⟨1, by decide⟩ (UInt256.ofNat 162), .op .CODECOPY, .op .JUMPDEST]

def copied (memory code : ByteArray) : ByteArray :=
  MachineState.writeBytes memory (MachineState.readPadded code 5000 32) 162

theorem run_sparse (s : State) (pc flag : UInt256) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := UInt256.ofNat 32 :: flag :: F} =
      some {s with
        pc := pcAfter pc template
        stack := flag :: F
        memory := copied s.memory s.executionEnv.code} := by
  have hcap (n : Nat) (hn : n ≤ 27) : F.length + n < 1024 := by omega
  have hword : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 162 32) = s.activeWords := by
    have h : MachineState.activeWordsAfter s.activeWords.toNat 162 32 = s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      omega
    rw [h]
    exact (Word.word_eq_ofNat_toNat _).symm
  simp (discharger := omega) [template, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hword, copied, add_eq_hAdd]

theorem bytes_exact : Challenge.EvmProof.PcEncoding.assembleBytes template = [97,19,136,96,162,57,91] := by decide

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

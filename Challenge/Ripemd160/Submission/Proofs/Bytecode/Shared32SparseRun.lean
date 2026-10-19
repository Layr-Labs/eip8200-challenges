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
   .push ⟨2, by decide⟩ (UInt256.ofNat 162), .op .CODECOPY]

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

/-- The reordered `151..165` slice: the `CODECOPY` arguments keep their order, the branch target
`497` is pushed before them, and `PC` supplies the displaced destination constant `162`. -/
def combinedTemplate : List Instr :=
  [.push ⟨5, by decide⟩ (UInt256.ofNat 497),
   .push ⟨1, by decide⟩ (UInt256.ofNat 32),
   .push ⟨2, by decide⟩ (UInt256.ofNat 5000),
   .op .PC, .op .CODECOPY, .op .JUMPI]

theorem combined_bytes : Challenge.EvmProof.PcEncoding.assembleBytes combinedTemplate =
    [100,0,0,0,1,241,96,32,97,19,136,88,57,87] := by decide

private theorem combined_hcap (F : List UInt256) (hstack : F.length ≤ 900) :
    ∀ n : Nat, n ≤ 27 → F.length + n < 1024 := by
  intro n hn
  omega

private theorem combined_hword (s : State) (hactive : 34 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 162 32) = s.activeWords := by
  have h : MachineState.activeWordsAfter s.activeWords.toNat 162 32 = s.activeWords.toNat := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_eq_left
    omega
  rw [h]
  exact (Word.word_eq_ofNat_toNat _).symm

theorem run_combined_hit (s : State) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hv : Decode.isValidJumpDest s.executionEnv.code 497 = true) :
    runInstrSeq combinedTemplate
      {s with pc := UInt256.ofNat 151, stack := UInt256.ofNat 1 :: F} =
      some {s with
        pc := UInt256.ofNat 497
        stack := F
        memory := copied s.memory s.executionEnv.code} := by
  have hcap := combined_hcap F hstack
  have hword := combined_hword s hactive
  have e1 : UInt256.ofNat 151 + UInt256.ofNat 6 = UInt256.ofNat 157 := by
    rw [Word.ofNat_add_ofNat (by decide : 151 + 6 < 2 ^ 256)]
  have e2 : UInt256.ofNat 157 + UInt256.ofNat 2 = UInt256.ofNat 159 := by
    rw [Word.ofNat_add_ofNat (by decide : 157 + 2 < 2 ^ 256)]
  have e3 : UInt256.ofNat 159 + UInt256.ofNat 3 = UInt256.ofNat 162 := by
    rw [Word.ofNat_add_ofNat (by decide : 159 + 3 < 2 ^ 256)]
  have e4 : UInt256.ofNat 162 + UInt256.ofNat 1 = UInt256.ofNat 163 := by
    rw [Word.ofNat_add_ofNat (by decide : 162 + 1 < 2 ^ 256)]
  have e5 : UInt256.ofNat 163 + UInt256.ofNat 1 = UInt256.ofNat 164 := by
    rw [Word.ofNat_add_ofNat (by decide : 163 + 1 < 2 ^ 256)]
  have e6 : UInt256.ofNat 164 + UInt256.ofNat 1 = UInt256.ofNat 165 := by
    rw [Word.ofNat_add_ofNat (by decide : 164 + 1 < 2 ^ 256)]
  simp (discharger := omega) [combinedTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hword, copied, add_eq_hAdd,
    UInt256.isTrue, hv, e1, e2, e3, e4, e5, e6]

theorem run_combined_miss (s : State) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq combinedTemplate
      {s with pc := UInt256.ofNat 151, stack := UInt256.ofNat 0 :: F} =
      some {s with
        pc := UInt256.ofNat 165
        stack := F
        memory := copied s.memory s.executionEnv.code} := by
  have hcap := combined_hcap F hstack
  have hword := combined_hword s hactive
  have e1 : UInt256.ofNat 151 + UInt256.ofNat 6 = UInt256.ofNat 157 := by
    rw [Word.ofNat_add_ofNat (by decide : 151 + 6 < 2 ^ 256)]
  have e2 : UInt256.ofNat 157 + UInt256.ofNat 2 = UInt256.ofNat 159 := by
    rw [Word.ofNat_add_ofNat (by decide : 157 + 2 < 2 ^ 256)]
  have e3 : UInt256.ofNat 159 + UInt256.ofNat 3 = UInt256.ofNat 162 := by
    rw [Word.ofNat_add_ofNat (by decide : 159 + 3 < 2 ^ 256)]
  have e4 : UInt256.ofNat 162 + UInt256.ofNat 1 = UInt256.ofNat 163 := by
    rw [Word.ofNat_add_ofNat (by decide : 162 + 1 < 2 ^ 256)]
  have e5 : UInt256.ofNat 163 + UInt256.ofNat 1 = UInt256.ofNat 164 := by
    rw [Word.ofNat_add_ofNat (by decide : 163 + 1 < 2 ^ 256)]
  have e6 : UInt256.ofNat 164 + UInt256.ofNat 1 = UInt256.ofNat 165 := by
    rw [Word.ofNat_add_ofNat (by decide : 164 + 1 < 2 ^ 256)]
  simp (discharger := omega) [combinedTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hword, copied, add_eq_hAdd,
    UInt256.isTrue, e1, e2, e3, e4, e5, e6]

theorem bytes_exact : Challenge.EvmProof.PcEncoding.assembleBytes template = [97,19,136,97,0,162,57] := by decide

theorem sparse_read_input (input : ByteArray) (hn : 0 < input.size) :
    MachineState.readWord (sparseMemory (copiedMemory input)) 1056 =
      MachineState.readWord (copiedMemory input) 1056 := by
  rw [copiedMemory_sparse input hn]
  exact read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))

#print axioms run_head
#print axioms run_fold
#print axioms run_sparse
#print axioms run_combined_hit
#print axioms run_combined_miss
#print axioms bytes_exact
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun

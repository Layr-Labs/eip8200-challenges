import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Lower
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32SparseRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory HoistedInherited.Pair13Endian
open HoistedInherited.Shared32Scratch

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

/-- The fast path plants `highWord` at memory 162. `code` is unused: the retired
`CODECOPY`'s source offset 5000 is never read again. -/
def copied (memory _code : ByteArray) : ByteArray :=
  PairedScheduleMemory.writeWord memory 162 highWord

/-- The reordered `151..188` fast path: the 32-byte constant is pushed inline as a 29-byte
immediate (its top three bytes are zero) and stored with `MSTORE`; the branch target `497`
follows. The retired `CODECOPY` read code offset 5000, which nothing reads now. -/
def combinedTemplate : List Instr :=
  [.push ⟨29, by decide⟩ highWord,
   .push ⟨1, by decide⟩ (UInt256.ofNat 162),
   .op .MSTORE,
   .push ⟨2, by decide⟩ (UInt256.ofNat 497),
   .op .JUMPI]

theorem combined_bytes : Challenge.EvmProof.PcEncoding.assembleBytes combinedTemplate =
    [124,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,96,162,82,97,1,241,87] := by decide

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
  have e1 : UInt256.ofNat 151 + UInt256.ofNat 30 = UInt256.ofNat 181 := by
    rw [Word.ofNat_add_ofNat (by decide : 151 + 30 < 2 ^ 256)]
  have e2 : UInt256.ofNat 181 + UInt256.ofNat 2 = UInt256.ofNat 183 := by
    rw [Word.ofNat_add_ofNat (by decide : 181 + 2 < 2 ^ 256)]
  have e3 : UInt256.ofNat 183 + UInt256.ofNat 1 = UInt256.ofNat 184 := by
    rw [Word.ofNat_add_ofNat (by decide : 183 + 1 < 2 ^ 256)]
  have e4 : UInt256.ofNat 184 + UInt256.ofNat 3 = UInt256.ofNat 187 := by
    rw [Word.ofNat_add_ofNat (by decide : 184 + 3 < 2 ^ 256)]
  have e5 : UInt256.ofNat 187 + UInt256.ofNat 1 = UInt256.ofNat 188 := by
    rw [Word.ofNat_add_ofNat (by decide : 187 + 1 < 2 ^ 256)]
  simp (discharger := omega) [combinedTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hword, copied, add_eq_hAdd,
    UInt256.isTrue, hv, PairedScheduleMemory.writeWord, Word.literal_eq_ofNat,
    e1, e2, e3, e4, e5]

theorem run_combined_miss (s : State) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq combinedTemplate
      {s with pc := UInt256.ofNat 151, stack := UInt256.ofNat 0 :: F} =
      some {s with
        pc := UInt256.ofNat 188
        stack := F
        memory := copied s.memory s.executionEnv.code} := by
  have hcap := combined_hcap F hstack
  have hword := combined_hword s hactive
  have e1 : UInt256.ofNat 151 + UInt256.ofNat 30 = UInt256.ofNat 181 := by
    rw [Word.ofNat_add_ofNat (by decide : 151 + 30 < 2 ^ 256)]
  have e2 : UInt256.ofNat 181 + UInt256.ofNat 2 = UInt256.ofNat 183 := by
    rw [Word.ofNat_add_ofNat (by decide : 181 + 2 < 2 ^ 256)]
  have e3 : UInt256.ofNat 183 + UInt256.ofNat 1 = UInt256.ofNat 184 := by
    rw [Word.ofNat_add_ofNat (by decide : 183 + 1 < 2 ^ 256)]
  have e4 : UInt256.ofNat 184 + UInt256.ofNat 3 = UInt256.ofNat 187 := by
    rw [Word.ofNat_add_ofNat (by decide : 184 + 3 < 2 ^ 256)]
  have e5 : UInt256.ofNat 187 + UInt256.ofNat 1 = UInt256.ofNat 188 := by
    rw [Word.ofNat_add_ofNat (by decide : 187 + 1 < 2 ^ 256)]
  simp (discharger := omega) [combinedTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    hrun, hcap, Instr.size, UInt256.succ, Nat.add_assoc, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hword, copied, add_eq_hAdd,
    UInt256.isTrue, PairedScheduleMemory.writeWord, Word.literal_eq_ofNat,
    e1, e2, e3, e4, e5]

/-- The miss fall-through: `PUSH2 9715 JUMP` into the relocated cold path. -/
def missJumpTemplate : List Instr := PadJump.template 9715

theorem run_missJump (s : State) (F : List UInt256)
    (hstack : F.length ≤ 900) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9715 = true) :
    runInstrSeq missJumpTemplate
      {s with pc := UInt256.ofNat 188, stack := F} =
      some {s with pc := UInt256.ofNat 9715, stack := F} := by
  have hmod : (9715 : Nat) % 2 ^ 256 = 9715 := by norm_num
  have hv' : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 9715).toNat = true := by
    simpa only [Word.word_toNat_ofNat, hmod] using hv
  simpa only [missJumpTemplate, Word.word_toNat_ofNat, hmod] using
    PadJump.run_template s (UInt256.ofNat 188) F 9715 (by omega) hrun hv'

theorem sparse_read_input (input : ByteArray) (hn : 0 < input.size) :
    MachineState.readWord (sparseMemory (copiedMemory input)) 1056 =
      MachineState.readWord (copiedMemory input) 1056 := by
  rw [copiedMemory_sparse input hn]
  exact read_writeWord_disjoint _ _ _ _ (Or.inr (by decide))

#print axioms run_head
#print axioms run_combined_hit
#print axioms run_combined_miss
#print axioms run_missJump
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32SparseRun

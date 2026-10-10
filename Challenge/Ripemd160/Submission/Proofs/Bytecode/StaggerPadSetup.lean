import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadZeroPrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPadStore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Setup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadShiftDiet
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPad
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory
open PairTableActive StaggerTableSparse StaggerTableLayout

/-- Pad-only low block (pc 130..183): copy zero calldata over the table (the copy offset is the
advanced block offset the exit left on top, which is past the calldata), store the unmasked
low bit-length word `n <<< 3` and `0x80`, and leave `CODESIZE` on top as the loop-exit sentinel. The early `PUSH19` mark is
consumed by the final memory store.
The address-162 store uses `PC`; this theorem fixes the template entry at PC130.  Only the fast entry (lengths 64, 128, 192) reaches
this block, so the high length words are always zero and no guard follows. -/
def lowTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 1084),
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .CALLDATACOPY,
    .push ⟨19, by decide⟩ (UInt256.ofNat (128 * (1 + 2 ^ 144))),
    .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .SHL,
    .op (.Dup ⟨0, by decide⟩),
    .op .PC,
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨4, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .op .CODESIZE ]

/-- `SWAP11 PUSH2 0328 JUMP` at 184: park the exit sentinel in slot 12 (so the block exit finishes)
and go straight to the rounds. -/
def branchTemplate : List Instr :=
  [ .op (.Swap ⟨10, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 808),
    .op .JUMP ]

/-- Pad-only high block (pc 4833..4860), reached only when `n >>> 29 ≠ 0`. -/
def highTemplate : List Instr :=
  [ .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 29),
    .op .SHR,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 1008),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 990),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 648),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 612),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 270),
    .op .MSTORE ]

private theorem add_literals (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b

private theorem hadd_literals (a b : Nat) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  add_literals a b

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

/-- The fast padding path is valid for lengths below the artifact's byte size. -/
def highZero (n : UInt256) : UInt256 := UInt256.lt n (UInt256.ofNat 5248)

theorem highZero_true_iff (n : UInt256) :
    UInt256.isTrue (highZero n) ↔ n.toNat < 5248 := by
  change (UInt256.lt n (UInt256.ofNat 5248)).toNat ≠ 0 ↔ n.toNat < 5248
  rw [Word.word_toNat_lt]
  have hc : (UInt256.ofNat 5248).toNat = 5248 := by decide
  rw [hc]
  by_cases hn : n.toNat < 5248 <;> simp [hn]

theorem highZero_true_imp (n : UInt256) (h : UInt256.isTrue (highZero n)) :
    StaggerTablePad.highDirty n = UInt256.ofNat 0 := by
  have hbound := (highZero_true_iff n).mp h
  apply Word.word_ext
  unfold StaggerTablePad.highDirty
  rw [Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow]
  have h0 : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [h0]
  simp only [Nat.reducePow]
  omega

theorem run_low (s : State) (pc off : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 995) (hrun : s.halt = .Running) (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hoff : s.executionEnv.calldata.size ≤ off.toNat) (hpc : pc = UInt256.ofNat 130) :
    runInstrSeq lowTemplate {s with pc := pc, stack := off :: UInt256.ofNat 4294967295 :: rest} =
      some {s with
             pc := pcAfter pc lowTemplate
             stack := UInt256.ofNat s.executionEnv.code.size :: UInt256.ofNat 4294967295 :: rest
             memory := StaggerTablePad.padRealChain s.memory
               (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have hcap (n : Nat) (hn : n ≤ 28) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved _ _ hactive ha
  have hcopyActive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 28 1084) = s.activeWords := by
    have he : MachineState.activeWordsAfter s.activeWords.toNat 28 1084 = s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (1084 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      omega
    rw [he]
    exact (Word.word_eq_ofNat_toNat _).symm
  have hz : ∀ i, 36 ≤ i → i < 54 →
      (MachineState.writeBytes s.memory PadZeroPrefix.zeroBytes 28)[i]?.getD 0 = 0 := by
    intro i hlo hhi
    rw [MachineState.writeBytes_getElem?_getD, PadZeroPrefix.zeroBytes_size,
      if_pos (by omega), PadZeroPrefix.zeroBytes_getD]
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hzero : MachineState.readPadded s.executionEnv.calldata off.toNat 1084 = PadZeroPrefix.zeroBytes :=
    PadZeroPrefix.readPadded_ge _ _ hoff
  have hpacked := PackedPadStore.after_length_stores_gen
    (MachineState.writeBytes s.memory PadZeroPrefix.zeroBytes 28)
    (StaggerTablePad.lowDirty (UInt256.ofNat s.executionEnv.calldata.size)) hz
  change StaggerTablePad.padRealChain s.memory
    (UInt256.ofNat s.executionEnv.calldata.size) = _ at hpacked
  rw [hpacked]
  simp (discharger := omega) [hpc, add_literals, hadd_literals, lowTemplate, StaggerTablePad.padRealChain,
    StaggerTablePad.lowChainOver, StaggerTableSparse.zeroSuffix, StaggerTablePad.lowDirty,
    zeroMemory, writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    PairedHelperBooleanTrace.push0_toNat,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, hcopyActive, hsize, hzero,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]

theorem run_high (s : State) (pc returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256) :
    runInstrSeq highTemplate {s with pc := pc, stack := returnPC :: rest} =
      some {s with
             pc := pcAfter pc highTemplate
             stack := returnPC :: rest
             memory := StaggerTablePad.highStores s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved _ _ hactive ha
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  simp (discharger := omega) [highTemplate, StaggerTablePad.highStores, StaggerTablePad.highDirty,
    writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, hsize, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [add_eq_hAdd]

theorem run_branch_taken (s : State) (pc : UInt256)
    (a b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 c : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 808).toNat = true) :
    runInstrSeq branchTemplate
        {s with pc := pc, stack := a :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: c :: rho} =
      some {s with
        pc := UInt256.ofNat 808
        stack := c :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: a :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 13) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [branchTemplate, runInstrSeq, DataStepper.runInstr, hrun, hcap,
    hvalid, List.length_cons, List.exchange, List.getElem?_cons_zero, pcAfter, UInt256.succ,
    Instr.size, Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat]

#print axioms run_low
#print axioms run_high
#print axioms run_branch_taken
#print axioms highZero_true_iff
#print axioms highZero_true_imp
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPad

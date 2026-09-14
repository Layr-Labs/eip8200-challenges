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

/-- Pad-only low block at PCs 4761..4803: clear the sparse table, store the low
bit-length word and padding marker, then leave `lt n 65535` for the branch at 4804.
An accepted length has zero high lanes; rejected lengths use the unconditional high stores. -/
def lowTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 1112),
    .op .CALLDATASIZE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .CALLDATACOPY,
    .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .SHL,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 162),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op .OR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 65535),
    .op .CALLDATASIZE,
    .op .LT ]

/-- `PUSH2 890 JUMPI` at PC 4804: skip high stores when the guard accepts. -/
def branchTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 890),
    .op .JUMPI ]

/-- Pad-only high block at PCs 4808..4835, reached when the length guard rejects. -/
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

private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

/-- The branch condition left by the low block: the packed length guard `lt n 65535`. -/
def highZero (n : UInt256) : UInt256 := UInt256.lt n (UInt256.ofNat 65535)

theorem highZero_true_imp (n : UInt256) (h : UInt256.isTrue (highZero n)) :
    StaggerTablePad.highDirty n = UInt256.ofNat 0 := by
  have hnum : (UInt256.ofNat 65535).toNat = 65535 := by decide
  have hbound : n.toNat < 65535 := by
    by_cases hc : n.toNat < 65535
    · exact hc
    · refine absurd ?_ h
      show (highZero n).toNat = 0
      unfold highZero
      rw [Word.word_toNat_lt]
      simp only [hnum]
      exact if_neg hc
  apply Word.word_ext
  unfold StaggerTablePad.highDirty
  rw [Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow]
  have h0 : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [h0]
  simp only [Nat.reducePow]
  omega

theorem run_low (s : State) (pc returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 995) (hrun : s.halt = .Running) (hactive : 35 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256) :
    runInstrSeq lowTemplate {s with pc := pc, stack := returnPC :: UInt256.ofNat 4294967295 :: rest} =
      some {s with
             pc := pcAfter pc lowTemplate
             stack := highZero (UInt256.ofNat s.executionEnv.calldata.size) :: returnPC :: UInt256.ofNat 4294967295 :: rest
             memory := StaggerTablePad.lowChain s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have hcap (n : Nat) (hn : n ≤ 28) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved _ _ hactive ha
  have hcopyActive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 1112) = s.activeWords := by
    have he : MachineState.activeWordsAfter s.activeWords.toNat 0 1112 = s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (1112 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      omega
    rw [he]
    exact (Word.word_eq_ofNat_toNat _).symm
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hconstant : UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 128) (UInt256.ofNat 144)) (UInt256.ofNat 128) = UInt256.ofNat (128 * (1 + 2 ^ 144)) := by decide
  have hconstantRev : UInt256.lor (UInt256.ofNat 128) (UInt256.shiftLeft (UInt256.ofNat 128) (UInt256.ofNat 144)) = UInt256.ofNat (128 * (1 + 2 ^ 144)) := by decide
  have hpacked := PackedPadStore.after_length_stores s.memory
    (StaggerTablePad.lowDirty (UInt256.ofNat s.executionEnv.calldata.size))
  change StaggerTablePad.lowChain s.memory (UInt256.ofNat s.executionEnv.calldata.size) = _ at hpacked
  rw [hpacked]
  simp (discharger := omega) [lowTemplate, hconstant, hconstantRev, StaggerTablePad.lowChain, StaggerTablePad.lowDirty,
    highZero, zeroMemory, writeWord, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    PairedHelperBooleanTrace.push0_toNat,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, hcopyActive, hsize,
    StaggerTablePad.readPadded_end, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [add_eq_hAdd]

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

theorem run_branch_taken (s : State) (pc c : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) (hc : UInt256.isTrue c)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 890).toNat = true) :
    runInstrSeq branchTemplate {s with pc := pc, stack := c :: rho} =
      some {s with pc := UInt256.ofNat 890, stack := rho} := by
  have hcap : rho.length < 1024 := by omega
  have hcap1 : rho.length + 1 < 1024 := by omega
  have hcap2 : rho.length + 2 < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [branchTemplate, runInstrSeq, DataStepper.runInstr, hrun, hcap,
    hcap1, hcap2, hc, hvalid, List.length_cons]

theorem run_branch_fall (s : State) (pc c : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) (hc : ¬ UInt256.isTrue c) :
    runInstrSeq branchTemplate {s with pc := pc, stack := c :: rho} =
      some {s with pc := pcAfter pc branchTemplate, stack := rho} := by
  have hcap : rho.length < 1024 := by omega
  have hcap1 : rho.length + 1 < 1024 := by omega
  have hcap2 : rho.length + 2 < 1024 := by omega
  simp (discharger := omega) [branchTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, hrun, hcap, hcap1, hcap2, hc, List.length_cons]
  all_goals simp only [add_eq_hAdd]

#print axioms run_low
#print axioms run_high
#print axioms run_branch_taken
#print axioms run_branch_fall
#print axioms highZero_true_imp
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPad

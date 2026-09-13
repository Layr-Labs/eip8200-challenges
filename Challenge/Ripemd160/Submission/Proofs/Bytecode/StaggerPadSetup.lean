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

/-- Pad-only low block (pc 4784..4826): copy zero calldata over the table, store the unmasked
low bit-length word `n <<< 3` (two `JUMPDEST`s keep the block's length where the mask used
to be applied; the resident `0xffffffff` stays four deep on the stack) and `0x80`, then leave
`iszero (n >>> 29)` for the branch at 4827. -/
def lowTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 1112),
    .op .CALLDATASIZE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .CALLDATACOPY,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 3),
    .op .SHL,
    .op .JUMPDEST,
    .op .JUMPDEST,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 162),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 666),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 522),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 54),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 36),
    .op .MSTORE,
    .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 29),
    .op .SHR,
    .op .ISZERO ]

/-- `PUSH2 0398 JUMPI` at 4769: straight to the rounds when the high word is zero. -/
def branchTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 925), .op .JUMPI ]

/-- Pad-only high block (pc 4831..4858), reached only when `n >>> 29 ≠ 0`. -/
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

/-- The branch condition left by the low block. -/
def highZero (n : UInt256) : UInt256 := UInt256.isZero (UInt256.shiftRight n (UInt256.ofNat 29))

theorem highZero_true_iff (n : UInt256) :
    UInt256.isTrue (highZero n) ↔ StaggerTablePad.highDirty n = UInt256.ofNat 0 := by
  have hx : StaggerTablePad.highDirty n = UInt256.ofNat 0 ↔
      (UInt256.shiftRight n (UInt256.ofNat 29)).toNat = 0 := by
    constructor
    · intro h
      change (StaggerTablePad.highDirty n).toNat = 0
      rw [h]
      decide
    · intro h
      apply Word.word_ext
      change (UInt256.shiftRight n (UInt256.ofNat 29)).toNat = _
      rw [h]
      decide
  rw [hx]
  unfold highZero UInt256.isZero
  by_cases h : (UInt256.shiftRight n (UInt256.ofNat 29)).toNat = 0
  · rw [if_pos h]
    constructor
    · intro _
      exact h
    · intro _
      show (UInt256.ofNat 1).toNat ≠ 0
      decide
  · rw [if_neg h]
    constructor
    · intro h'
      exact absurd h' (by show ¬ (UInt256.ofNat 0).toNat ≠ 0; decide)
    · intro h'
      exact absurd h' h

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
  simp (discharger := omega) [lowTemplate, StaggerTablePad.lowChain, StaggerTablePad.lowDirty,
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
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 925).toNat = true) :
    runInstrSeq branchTemplate {s with pc := pc, stack := c :: rho} =
      some {s with pc := UInt256.ofNat 925, stack := rho} := by
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
#print axioms highZero_true_iff
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPad

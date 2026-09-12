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

def padTemplate : List Instr :=
  [ .push ⟨2, by decide⟩ (UInt256.ofNat 632),
    .op .CALLDATASIZE,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .CALLDATACOPY,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 227),
    .op .SHL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .SHR,
    .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 195),
    .op .SHL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .SHR,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 580),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 550),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 500),
    .op .MSTORE,
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 490),
    .op .MSTORE,
    .op (.Swap ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 470),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 330),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 320),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 310),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 300),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 90),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 80),
    .op .MSTORE ]
private theorem add_eq_hAdd (x y : UInt256) : UInt256.add x y = x + y := rfl

theorem run_pad (s : State) (pc returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length ≤ 996) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256) :
    runInstrSeq padTemplate {s with pc := pc, stack := returnPC :: rest} =
      some {s with pc := pcAfter pc padTemplate, stack := returnPC :: rest, memory := StaggerTablePad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size)} := by
  have hcap (n : Nat) (hn : n ≤ 27) : rest.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (ha : address ≤ 1056) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    word_active_preserved _ _ hactive ha
  have hcopyActive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 632) = s.activeWords := by
    have he : MachineState.activeWordsAfter s.activeWords.toNat 0 632 = s.activeWords.toNat := by
      simp only [MachineState.activeWordsAfter, if_neg (by decide : (632 : Nat) ≠ 0)]
      apply Nat.max_eq_left
      omega
    rw [he]
    exact (Word.word_eq_ofNat_toNat _).symm
  have hsize : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hfit]
  simp (discharger := omega) [padTemplate, StaggerTablePad.resultMemory,
    storeSelected, StaggerTablePad.keepPad, tableWords, slots, zeroMemory,
    PadOnlySchedule.padWords, PadOnlySchedule.lowDiet_eq_lowLength,
    PadOnlySchedule.lowLength, PadOnlySchedule.highLength,
    writeWord, PadShiftDiet.high, PadShiftDiet.low, Word.land_comm,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    PairedHelperBooleanTrace.push0_toNat,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    State.activeWordsAfterUInt256, hactiveAt, hcopyActive, hsize,
    StaggerTablePad.readPadded_end, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [add_eq_hAdd]
#print axioms run_pad
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPad

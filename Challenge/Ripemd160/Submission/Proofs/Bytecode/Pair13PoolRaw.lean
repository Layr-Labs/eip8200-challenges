import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace PairedScheduleMemory

def coefficient : UInt256 := UInt256.ofNat 22300745198530623141535718272648361505980417
def poolWord (memory : ByteArray) (mask : UInt256) (i : Nat) : UInt256 :=
  if i = 0 ∨ i = 1 ∨ i = 2 then MachineState.readWord memory (4 * i)
  else UInt256.land mask (MachineState.readWord memory (4 * i))
def poolStack (words : Nat → UInt256) (rho : List UInt256) : List UInt256 :=
  [ words 3, words 9, words 8, words 1, words 2, words 15, words 7, words 10, words 13, words 14, coefficient, words 11, words 5, words 12, words 0, words 6, words 4 ] ++ rho
def template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .MLOAD,
    .op (.Dup ⟨1, by decide⟩),
    .op .AND,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 48),
    .op .MLOAD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 44),
    .op .MLOAD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .push ⟨19, by decide⟩ (UInt256.ofNat 22300745198530623141535718272648361505980417),
    .push ⟨1, by decide⟩ (UInt256.ofNat 56),
    .op .MLOAD,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 52),
    .op .MLOAD,
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 40),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .MLOAD,
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨10, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 60),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 4),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .MLOAD,
    .op (.Dup ⟨14, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 36),
    .op .MLOAD,
    .op (.Dup ⟨15, by decide⟩),
    .op .AND,
    .op (.Dup ⟨15, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .MLOAD,
    .op .AND,
    .op (.Swap ⟨15, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 12),
    .op .MLOAD,
    .op .AND ]

theorem run_actual (s : State) (pc mask : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := mask :: rho} =
      some {s with pc := pcAfter pc template, stack := poolStack (poolWord s.memory mask) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 40) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [template, poolStack, poolWord, coefficient, runInstrSeq, DataStepper.runInstr,
     pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
     Nat.add_assoc, hrun, hbase, hzero, hcap, State.activeWordsAfterUInt256,
     hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
     RawExpressionAC.land_comm]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13PoolRaw

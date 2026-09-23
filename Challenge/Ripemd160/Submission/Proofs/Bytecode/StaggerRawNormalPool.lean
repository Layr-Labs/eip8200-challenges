import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Stagger144Active
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalPool
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl
def template : List Instr :=
  [ .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .MLOAD,
    .op (.Dup ⟨1, by decide⟩),
    .op .AND,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MLOAD,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 48),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 20),
    .op .MLOAD,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 44),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 56),
    .op .MLOAD,
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 52),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 40),
    .op .MLOAD,
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .op (.Dup ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 28),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 60),
    .op .MLOAD,
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .MLOAD,
    .push ⟨1, by decide⟩ (UInt256.ofNat 4),
    .op .MLOAD,
    .op (.Dup ⟨12, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .MLOAD,
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 36),
    .op .MLOAD,
    .op (.Dup ⟨14, by decide⟩),
    .op .AND,
    .op (.Dup ⟨14, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 24),
    .op .MLOAD,
    .op .AND,
    .op (.Swap ⟨14, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 12),
    .op .MLOAD,
    .op .AND ]
def inputStack (x : Input) (rho : List UInt256) : List UInt256 :=
  [ x.v0 ] ++ rho
def outputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land (MachineState.readWord memory 12) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 36)),
    (UInt256.land x.v0 (MachineState.readWord memory 32)),
    (MachineState.readWord memory 4),
    (MachineState.readWord memory 8),
    (UInt256.land x.v0 (MachineState.readWord memory 60)),
    (UInt256.land x.v0 (MachineState.readWord memory 28)),
    (UInt256.land x.v0 (MachineState.readWord memory 40)),
    (UInt256.land x.v0 (MachineState.readWord memory 52)),
    (UInt256.land x.v0 (MachineState.readWord memory 56)),
    (UInt256.land x.v0 (MachineState.readWord memory 44)),
    (UInt256.land x.v0 (MachineState.readWord memory 20)),
    (UInt256.land x.v0 (MachineState.readWord memory 48)),
    (MachineState.readWord memory 0),
    (UInt256.land x.v0 (MachineState.readWord memory 16)),
    (UInt256.land x.v0 (MachineState.readWord memory 24)) ] ++ rho
def actualOutput (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [ (UInt256.land (MachineState.readWord memory 12) x.v0),
    (UInt256.land (MachineState.readWord memory 36) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 32)),
    (MachineState.readWord memory 4),
    (MachineState.readWord memory 8),
    (UInt256.land (MachineState.readWord memory 60) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 28)),
    (UInt256.land (MachineState.readWord memory 40) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 52)),
    (UInt256.land (MachineState.readWord memory 56) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 44)),
    (UInt256.land (MachineState.readWord memory 20) x.v0),
    (UInt256.land x.v0 (MachineState.readWord memory 48)),
    (MachineState.readWord memory 0),
    (UInt256.land x.v0 (MachineState.readWord memory 16)),
    (UInt256.land x.v0 (MachineState.readWord memory 24)) ] ++ rho
private theorem actualOutput_eq (memory : ByteArray) (x : Input) (rho : List UInt256) :
    actualOutput memory x rho = outputStack memory x rho := by
  simp only [actualOutput, outputStack, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.mulMod_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
private theorem run_generated (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (halias : rho[1]? = some x.v0) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := actualOutput s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 37) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 1088) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    Stagger144Active.word_active_preserved s.activeWords address hactive haddress
  simp (config := { maxSteps := 600000 }) (discharger := omega) [template, inputStack, actualOutput,
    runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hzero, hcap, halias,
    State.activeWordsAfterUInt256, hactiveAt, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [neutral_hadd, neutral_hmul, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.mulMod_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (halias : rho[1]? = some x.v0) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := pc, stack := inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := outputStack s.memory x rho} := by
  simpa only [actualOutput_eq] using run_generated s pc x rho hstack halias hrun hactive
#print axioms run_actual

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawNormalPool

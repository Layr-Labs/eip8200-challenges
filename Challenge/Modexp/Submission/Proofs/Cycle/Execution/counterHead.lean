import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def counterHeadpart0Program : List Instr :=
  [.op .JUMPDEST,
   .push 2 1728,
   .op .MLOAD,
   .op .ISZERO,
   .push 2 8110]

def counterHeadpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := UInt256.isZero v0
  {s with pc := UInt256.ofNat 8094, memory := s.memory, stack := (UInt256.ofNat 8110) :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem counterHeadpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions counterHeadpart0Program {s with pc := UInt256.ofNat 8085, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (counterHeadpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha1728 : (1728 : UInt256).toNat = 1728 := rfl
  have hf1728 := Monpro.activeWords_fix s 1728 32 (by decide) (by norm_num) hact
  simp [hz, hzn, counterHeadpart0Program, counterHeadpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1728, hf1728]


def counterHeadProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 1728,
   .op .MLOAD,
   .op .ISZERO,
   .push 2 8110]

def counterHeadModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := UInt256.isZero v0
  {s with pc := UInt256.ofNat 8094, memory := s.memory, stack := (UInt256.ofNat 8110) :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem counterHead_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions counterHeadProgram {s with pc := UInt256.ofNat 8085, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (counterHeadModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := UInt256.isZero v0
  have h0 : runInstructions counterHeadpart0Program {s with pc := UInt256.ofNat 8085, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := UInt256.ofNat 8094, memory := s.memory, stack := (UInt256.ofNat 8110) :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [counterHeadpart0Model, v0, v1] using counterHeadpart0_run (s) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  exact h0


end CycleSubmission.Execution

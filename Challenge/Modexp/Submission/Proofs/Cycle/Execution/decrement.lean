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

def decrementpart0Program : List Instr :=
  [.push 1 1,
   .push 2 1728,
   .op .MLOAD,
   .op .SUB,
   .push 2 1728,
   .op .MSTORE,
   .push 2 6152]

def decrementpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := v0 - (UInt256.ofNat 1)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1728
  {s with pc := UInt256.ofNat 8109, memory := v2, stack := (UInt256.ofNat 6152) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem decrementpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions decrementpart0Program {s with pc := UInt256.ofNat 8095, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (decrementpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha1728 : (1728 : UInt256).toNat = 1728 := rfl
  have hf1728 := Monpro.activeWords_fix s 1728 32 (by decide) (by norm_num) hact
  simp [hz, hzn, decrementpart0Program, decrementpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1728, hf1728]


def decrementProgram : List Instr :=
  [.push 1 1,
   .push 2 1728,
   .op .MLOAD,
   .op .SUB,
   .push 2 1728,
   .op .MSTORE,
   .push 2 6152]

def decrementModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := v0 - (UInt256.ofNat 1)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1728
  {s with pc := UInt256.ofNat 8109, memory := v2, stack := (UInt256.ofNat 6152) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem decrement_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions decrementProgram {s with pc := UInt256.ofNat 8095, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (decrementModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := v0 - (UInt256.ofNat 1)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1728
  have h0 : runInstructions decrementpart0Program {s with pc := UInt256.ofNat 8095, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := UInt256.ofNat 8109, memory := v2, stack := (UInt256.ofNat 6152) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [decrementpart0Model, v0, v1, v2] using decrementpart0_run (s) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  exact h0


end CycleSubmission.Execution

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

def packFinalpart0Program : List Instr :=
  [.op .JUMPDEST,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 240,
   .op .SHL,
   .op .OR,
   .push 2 2336,
   .op .MSTORE]

def packFinalpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := UInt256.shiftLeft x3 (UInt256.ofNat 240)
  let v2 : UInt256 := UInt256.lor v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 2336
  {s with pc := UInt256.ofNat 10423, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem packFinalpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart0Program {s with pc := UInt256.ofNat 10409, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (packFinalpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2336 : (2336 : UInt256).toNat = 2336 := rfl
  have hf2336 := Monpro.activeWords_fix s 2336 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart0Program, packFinalpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha2336, hf2336]


def packFinalpart1Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .push 1 224,
   .op .SHL,
   .op .OR,
   .push 2 2304,
   .op .MSTORE]

def packFinalpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x3 (UInt256.ofNat 16)
  let v1 : UInt256 := UInt256.shiftLeft x4 (UInt256.ofNat 224)
  let v2 : UInt256 := UInt256.lor v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 2304
  {s with pc := UInt256.ofNat 10436, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem packFinalpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart1Program {s with pc := UInt256.ofNat 10423, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (packFinalpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha2304 : (2304 : UInt256).toNat = 2304 := rfl
  have hf2304 := Monpro.activeWords_fix s 2304 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart1Program, packFinalpart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2304, hf2304]


def packFinalpart2Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .push 1 32,
   .op .SHR,
   .push 1 32,
   .op .MLOAD,
   .push 1 208,
   .op .SHL,
   .op .OR]

def packFinalpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x4 (UInt256.ofNat 32)
  let v1 : UInt256 := MachineState.readWord s.memory 32
  let v2 : UInt256 := UInt256.shiftLeft v1 (UInt256.ofNat 208)
  let v3 : UInt256 := UInt256.lor v2 v0
  {s with pc := UInt256.ofNat 10447, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem packFinalpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart2Program {s with pc := UInt256.ofNat 10436, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (packFinalpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart2Program, packFinalpart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32]


def packFinalpart3Program : List Instr :=
  [.push 2 2272,
   .op .MSTORE,
   .push 1 32,
   .op .MLOAD,
   .push 1 48,
   .op .SHR,
   .push 1 64,
   .op .MLOAD]

def packFinalpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 2272
  let v1 : UInt256 := MachineState.readWord v0 32
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 48)
  let v3 : UInt256 := MachineState.readWord v0 64
  {s with pc := UInt256.ofNat 10460, memory := v0, stack := v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem packFinalpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart3Program {s with pc := UInt256.ofNat 10447, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (packFinalpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha2272 : (2272 : UInt256).toNat = 2272 := rfl
  have hf2272 := Monpro.activeWords_fix s 2272 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart3Program, packFinalpart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha64, hf64, ha2272, hf2272]


def packFinalpart4Program : List Instr :=
  [.push 1 192,
   .op .SHL,
   .op .OR,
   .push 2 2240,
   .op .MSTORE,
   .push 1 64,
   .op .MLOAD,
   .push 1 64]

def packFinalpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 192)
  let v1 : UInt256 := UInt256.lor v0 x1
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2240
  let v3 : UInt256 := MachineState.readWord v2 64
  {s with pc := UInt256.ofNat 10473, memory := v2, stack := (UInt256.ofNat 64) :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem packFinalpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart4Program {s with pc := UInt256.ofNat 10460, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (packFinalpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha2240 : (2240 : UInt256).toNat = 2240 := rfl
  have hf2240 := Monpro.activeWords_fix s 2240 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart4Program, packFinalpart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha2240, hf2240]


def packFinalpart5Program : List Instr :=
  [.op .SHR,
   .push 1 96,
   .op .MLOAD,
   .push 1 176,
   .op .SHL,
   .op .OR,
   .push 2 2208,
   .op .MSTORE]

def packFinalpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x1 x0
  let v1 : UInt256 := MachineState.readWord s.memory 96
  let v2 : UInt256 := UInt256.shiftLeft v1 (UInt256.ofNat 176)
  let v3 : UInt256 := UInt256.lor v2 v0
  let v4 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v3.toNat 32) 2208
  {s with pc := UInt256.ofNat 10485, memory := v4, stack := x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem packFinalpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart5Program {s with pc := UInt256.ofNat 10473, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (packFinalpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha2208 : (2208 : UInt256).toNat = 2208 := rfl
  have hf2208 := Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart5Program, packFinalpart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha2208, hf2208]


def packFinalpart6Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .push 1 80,
   .op .SHR,
   .push 1 128,
   .op .MLOAD,
   .push 1 160,
   .op .SHL]

def packFinalpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 80)
  let v2 : UInt256 := MachineState.readWord s.memory 128
  let v3 : UInt256 := UInt256.shiftLeft v2 (UInt256.ofNat 160)
  {s with pc := UInt256.ofNat 10497, memory := s.memory, stack := v3 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem packFinalpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart6Program {s with pc := UInt256.ofNat 10485, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (packFinalpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart6Program, packFinalpart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha128, hf128]


def packFinalpart7Program : List Instr :=
  [.op .OR,
   .push 2 2176,
   .op .MSTORE,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .SHR,
   .push 1 160,
   .op .MLOAD]

def packFinalpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lor x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 2176
  let v2 : UInt256 := MachineState.readWord v1 128
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 96)
  let v4 : UInt256 := MachineState.readWord v1 160
  {s with pc := UInt256.ofNat 10511, memory := v1, stack := v4 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem packFinalpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart7Program {s with pc := UInt256.ofNat 10497, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (packFinalpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha2176 : (2176 : UInt256).toNat = 2176 := rfl
  have hf2176 := Monpro.activeWords_fix s 2176 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart7Program, packFinalpart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha160, hf160, ha2176, hf2176]


def packFinalpart8Program : List Instr :=
  [.push 1 144,
   .op .SHL,
   .op .OR,
   .push 2 2144,
   .op .MSTORE,
   .push 1 160,
   .op .MLOAD,
   .push 1 112]

def packFinalpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 144)
  let v1 : UInt256 := UInt256.lor v0 x1
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2144
  let v3 : UInt256 := MachineState.readWord v2 160
  {s with pc := UInt256.ofNat 10524, memory := v2, stack := (UInt256.ofNat 112) :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem packFinalpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart8Program {s with pc := UInt256.ofNat 10511, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (packFinalpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha2144 : (2144 : UInt256).toNat = 2144 := rfl
  have hf2144 := Monpro.activeWords_fix s 2144 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart8Program, packFinalpart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160, ha2144, hf2144]


def packFinalpart9Program : List Instr :=
  [.op .SHR,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 128,
   .op .SHL,
   .op .OR,
   .push 10 2112,
   .op .MSTORE]

def packFinalpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x1 x0
  let v1 : UInt256 := UInt256.shiftLeft x15 (UInt256.ofNat 128)
  let v2 : UInt256 := UInt256.lor v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 2112
  {s with pc := UInt256.ofNat 10542, memory := v3, stack := x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem packFinalpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalpart9Program {s with pc := UInt256.ofNat 10524, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (packFinalpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hf2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact
  simp [hz, hzn, packFinalpart9Program, packFinalpart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2112, hf2112]


def packFinalProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 240,
   .op .SHL,
   .op .OR,
   .push 2 2336,
   .op .MSTORE,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨5, by decide⟩),
   .push 1 224,
   .op .SHL,
   .op .OR,
   .push 2 2304,
   .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 32,
   .op .SHR,
   .push 1 32,
   .op .MLOAD,
   .push 1 208,
   .op .SHL,
   .op .OR,
   .push 2 2272,
   .op .MSTORE,
   .push 1 32,
   .op .MLOAD,
   .push 1 48,
   .op .SHR,
   .push 1 64,
   .op .MLOAD,
   .push 1 192,
   .op .SHL,
   .op .OR,
   .push 2 2240,
   .op .MSTORE,
   .push 1 64,
   .op .MLOAD,
   .push 1 64,
   .op .SHR,
   .push 1 96,
   .op .MLOAD,
   .push 1 176,
   .op .SHL,
   .op .OR,
   .push 2 2208,
   .op .MSTORE,
   .push 1 96,
   .op .MLOAD,
   .push 1 80,
   .op .SHR,
   .push 1 128,
   .op .MLOAD,
   .push 1 160,
   .op .SHL,
   .op .OR,
   .push 2 2176,
   .op .MSTORE,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .SHR,
   .push 1 160,
   .op .MLOAD,
   .push 1 144,
   .op .SHL,
   .op .OR,
   .push 2 2144,
   .op .MSTORE,
   .push 1 160,
   .op .MLOAD,
   .push 1 112,
   .op .SHR,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 128,
   .op .SHL,
   .op .OR,
   .push 10 2112,
   .op .MSTORE]

def packFinalModel (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := UInt256.shiftLeft a1 (UInt256.ofNat 240)
  let v2 : UInt256 := UInt256.lor v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 2336
  let v4 : UInt256 := UInt256.shiftRight a1 (UInt256.ofNat 16)
  let v5 : UInt256 := UInt256.shiftLeft a2 (UInt256.ofNat 224)
  let v6 : UInt256 := UInt256.lor v5 v4
  let v7 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded v6.toNat 32) 2304
  let v8 : UInt256 := UInt256.shiftRight a2 (UInt256.ofNat 32)
  let v9 : UInt256 := MachineState.readWord v7 32
  let v10 : UInt256 := UInt256.shiftLeft v9 (UInt256.ofNat 208)
  let v11 : UInt256 := UInt256.lor v10 v8
  let v12 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v11.toNat 32) 2272
  let v13 : UInt256 := MachineState.readWord v12 32
  let v14 : UInt256 := UInt256.shiftRight v13 (UInt256.ofNat 48)
  let v15 : UInt256 := MachineState.readWord v12 64
  let v16 : UInt256 := UInt256.shiftLeft v15 (UInt256.ofNat 192)
  let v17 : UInt256 := UInt256.lor v16 v14
  let v18 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v17.toNat 32) 2240
  let v19 : UInt256 := MachineState.readWord v18 64
  let v20 : UInt256 := UInt256.shiftRight v19 (UInt256.ofNat 64)
  let v21 : UInt256 := MachineState.readWord v18 96
  let v22 : UInt256 := UInt256.shiftLeft v21 (UInt256.ofNat 176)
  let v23 : UInt256 := UInt256.lor v22 v20
  let v24 : ByteArray := MachineState.writeBytes v18 (Data.Bytes.natToBytesPadded v23.toNat 32) 2208
  let v25 : UInt256 := MachineState.readWord v24 96
  let v26 : UInt256 := UInt256.shiftRight v25 (UInt256.ofNat 80)
  let v27 : UInt256 := MachineState.readWord v24 128
  let v28 : UInt256 := UInt256.shiftLeft v27 (UInt256.ofNat 160)
  let v29 : UInt256 := UInt256.lor v28 v26
  let v30 : ByteArray := MachineState.writeBytes v24 (Data.Bytes.natToBytesPadded v29.toNat 32) 2176
  let v31 : UInt256 := MachineState.readWord v30 128
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 96)
  let v33 : UInt256 := MachineState.readWord v30 160
  let v34 : UInt256 := UInt256.shiftLeft v33 (UInt256.ofNat 144)
  let v35 : UInt256 := UInt256.lor v34 v32
  let v36 : ByteArray := MachineState.writeBytes v30 (Data.Bytes.natToBytesPadded v35.toNat 32) 2144
  let v37 : UInt256 := MachineState.readWord v36 160
  let v38 : UInt256 := UInt256.shiftRight v37 (UInt256.ofNat 112)
  let v39 : UInt256 := UInt256.shiftLeft a8 (UInt256.ofNat 128)
  let v40 : UInt256 := UInt256.lor v39 v38
  let v41 : ByteArray := MachineState.writeBytes v36 (Data.Bytes.natToBytesPadded v40.toNat 32) 2112
  {s with pc := UInt256.ofNat 10542, memory := v41, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest}

theorem packFinal_run (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions packFinalProgram {s with pc := UInt256.ofNat 10409, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} =
      some (packFinalModel s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := UInt256.shiftLeft a1 (UInt256.ofNat 240)
  let v2 : UInt256 := UInt256.lor v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 2336
  let v4 : UInt256 := UInt256.shiftRight a1 (UInt256.ofNat 16)
  let v5 : UInt256 := UInt256.shiftLeft a2 (UInt256.ofNat 224)
  let v6 : UInt256 := UInt256.lor v5 v4
  let v7 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded v6.toNat 32) 2304
  let v8 : UInt256 := UInt256.shiftRight a2 (UInt256.ofNat 32)
  let v9 : UInt256 := MachineState.readWord v7 32
  let v10 : UInt256 := UInt256.shiftLeft v9 (UInt256.ofNat 208)
  let v11 : UInt256 := UInt256.lor v10 v8
  let v12 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v11.toNat 32) 2272
  let v13 : UInt256 := MachineState.readWord v12 32
  let v14 : UInt256 := UInt256.shiftRight v13 (UInt256.ofNat 48)
  let v15 : UInt256 := MachineState.readWord v12 64
  let v16 : UInt256 := UInt256.shiftLeft v15 (UInt256.ofNat 192)
  let v17 : UInt256 := UInt256.lor v16 v14
  let v18 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v17.toNat 32) 2240
  let v19 : UInt256 := MachineState.readWord v18 64
  let v20 : UInt256 := UInt256.shiftRight v19 (UInt256.ofNat 64)
  let v21 : UInt256 := MachineState.readWord v18 96
  let v22 : UInt256 := UInt256.shiftLeft v21 (UInt256.ofNat 176)
  let v23 : UInt256 := UInt256.lor v22 v20
  let v24 : ByteArray := MachineState.writeBytes v18 (Data.Bytes.natToBytesPadded v23.toNat 32) 2208
  let v25 : UInt256 := MachineState.readWord v24 96
  let v26 : UInt256 := UInt256.shiftRight v25 (UInt256.ofNat 80)
  let v27 : UInt256 := MachineState.readWord v24 128
  let v28 : UInt256 := UInt256.shiftLeft v27 (UInt256.ofNat 160)
  let v29 : UInt256 := UInt256.lor v28 v26
  let v30 : ByteArray := MachineState.writeBytes v24 (Data.Bytes.natToBytesPadded v29.toNat 32) 2176
  let v31 : UInt256 := MachineState.readWord v30 128
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 96)
  let v33 : UInt256 := MachineState.readWord v30 160
  let v34 : UInt256 := UInt256.shiftLeft v33 (UInt256.ofNat 144)
  let v35 : UInt256 := UInt256.lor v34 v32
  let v36 : ByteArray := MachineState.writeBytes v30 (Data.Bytes.natToBytesPadded v35.toNat 32) 2144
  let v37 : UInt256 := MachineState.readWord v36 160
  let v38 : UInt256 := UInt256.shiftRight v37 (UInt256.ofNat 112)
  let v39 : UInt256 := UInt256.shiftLeft a8 (UInt256.ofNat 128)
  let v40 : UInt256 := UInt256.lor v39 v38
  let v41 : ByteArray := MachineState.writeBytes v36 (Data.Bytes.natToBytesPadded v40.toNat 32) 2112
  have h0 : runInstructions packFinalpart0Program {s with pc := UInt256.ofNat 10409, memory := s.memory, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10423, memory := v3, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart0Model, v0, v1, v2, v3] using packFinalpart0_run (s) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h1 : runInstructions packFinalpart1Program {s with pc := UInt256.ofNat 10423, memory := v3, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10436, memory := v7, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart1Model, v4, v5, v6, v7] using packFinalpart1_run ({s with memory := v3}) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h2 : runInstructions packFinalpart2Program {s with pc := UInt256.ofNat 10436, memory := v7, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10447, memory := v7, stack := v11 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart2Model, v8, v9, v10, v11] using packFinalpart2_run ({s with memory := v7}) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h3 : runInstructions packFinalpart3Program {s with pc := UInt256.ofNat 10447, memory := v7, stack := v11 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10460, memory := v12, stack := v15 :: v14 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart3Model, v12, v13, v14, v15] using packFinalpart3_run ({s with memory := v7}) (v11) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h4 : runInstructions packFinalpart4Program {s with pc := UInt256.ofNat 10460, memory := v12, stack := v15 :: v14 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10473, memory := v18, stack := (UInt256.ofNat 64) :: v19 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart4Model, v16, v17, v18, v19] using packFinalpart4_run ({s with memory := v12}) (v15) (v14) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h5 : runInstructions packFinalpart5Program {s with pc := UInt256.ofNat 10473, memory := v18, stack := (UInt256.ofNat 64) :: v19 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10485, memory := v24, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart5Model, v20, v21, v22, v23, v24] using packFinalpart5_run ({s with memory := v18}) ((UInt256.ofNat 64)) (v19) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h6 : runInstructions packFinalpart6Program {s with pc := UInt256.ofNat 10485, memory := v24, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10497, memory := v24, stack := v28 :: v26 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart6Model, v25, v26, v27, v28] using packFinalpart6_run ({s with memory := v24}) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h7 : runInstructions packFinalpart7Program {s with pc := UInt256.ofNat 10497, memory := v24, stack := v28 :: v26 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10511, memory := v30, stack := v33 :: v32 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart7Model, v29, v30, v31, v32, v33] using packFinalpart7_run ({s with memory := v24}) (v28) (v26) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h8 : runInstructions packFinalpart8Program {s with pc := UInt256.ofNat 10511, memory := v30, stack := v33 :: v32 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10524, memory := v36, stack := (UInt256.ofNat 112) :: v37 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart8Model, v34, v35, v36, v37] using packFinalpart8_run ({s with memory := v30}) (v33) (v32) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h9 : runInstructions packFinalpart9Program {s with pc := UInt256.ofNat 10524, memory := v36, stack := (UInt256.ofNat 112) :: v37 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10542, memory := v41, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [packFinalpart9Model, v38, v39, v40, v41] using packFinalpart9_run ({s with memory := v36}) ((UInt256.ofNat 112)) (v37) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))


end CycleSubmission.Execution

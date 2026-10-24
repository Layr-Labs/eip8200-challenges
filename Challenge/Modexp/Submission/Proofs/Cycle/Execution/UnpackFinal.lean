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

def unpackFinalpart0Program : List Instr :=
  [.op .JUMPDEST,
   .push 2 480,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1792,
   .op .MSTORE,
   .push 2 450,
   .op .MLOAD]

def unpackFinalpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 480
  let v1 : UInt256 := UInt256.land x10 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1792
  let v3 : UInt256 := MachineState.readWord v2 450
  {s with pc := UInt256.ofNat 8125, memory := v2, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem unpackFinalpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalpart0Program {s with pc := UInt256.ofNat 8110, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (unpackFinalpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha450 : (450 : UInt256).toNat = 450 := rfl
  have hf450 := Monpro.activeWords_fix s 450 32 (by decide) (by norm_num) hact
  have ha480 : (480 : UInt256).toNat = 480 := rfl
  have hf480 := Monpro.activeWords_fix s 480 32 (by decide) (by norm_num) hact
  have ha1792 : (1792 : UInt256).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, unpackFinalpart0Program, unpackFinalpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha450, hf450, ha480, hf480, ha1792, hf1792]


def unpackFinalpart1Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1824,
   .op .MSTORE,
   .push 2 420,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND]

def unpackFinalpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x11 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1824
  let v2 : UInt256 := MachineState.readWord v1 420
  let v3 : UInt256 := UInt256.land x11 v2
  {s with pc := UInt256.ofNat 8137, memory := v1, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem unpackFinalpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalpart1Program {s with pc := UInt256.ofNat 8125, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (unpackFinalpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha420 : (420 : UInt256).toNat = 420 := rfl
  have hf420 := Monpro.activeWords_fix s 420 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : UInt256).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, unpackFinalpart1Program, unpackFinalpart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha420, hf420, ha1824, hf1824]


def unpackFinalpart2Program : List Instr :=
  [.push 2 1856,
   .op .MSTORE,
   .push 2 390,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1888,
   .op .MSTORE]

def unpackFinalpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1856
  let v1 : UInt256 := MachineState.readWord v0 390
  let v2 : UInt256 := UInt256.land x11 v1
  let v3 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v2.toNat 32) 1888
  {s with pc := UInt256.ofNat 8151, memory := v3, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem unpackFinalpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalpart2Program {s with pc := UInt256.ofNat 8137, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (unpackFinalpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha390 : (390 : UInt256).toNat = 390 := rfl
  have hf390 := Monpro.activeWords_fix s 390 32 (by decide) (by norm_num) hact
  have ha1856 : (1856 : UInt256).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : UInt256).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, unpackFinalpart2Program, unpackFinalpart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha390, hf390, ha1856, hf1856, ha1888, hf1888]


def unpackFinalpart3Program : List Instr :=
  [.push 2 360,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1920,
   .op .MSTORE,
   .push 2 330,
   .op .MLOAD]

def unpackFinalpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 360
  let v1 : UInt256 := UInt256.land x10 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1920
  let v3 : UInt256 := MachineState.readWord v2 330
  {s with pc := UInt256.ofNat 8165, memory := v2, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem unpackFinalpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalpart3Program {s with pc := UInt256.ofNat 8151, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (unpackFinalpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha330 : (330 : UInt256).toNat = 330 := rfl
  have hf330 := Monpro.activeWords_fix s 330 32 (by decide) (by norm_num) hact
  have ha360 : (360 : UInt256).toNat = 360 := rfl
  have hf360 := Monpro.activeWords_fix s 360 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : UInt256).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz, hzn, unpackFinalpart3Program, unpackFinalpart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha330, hf330, ha360, hf360, ha1920, hf1920]


def unpackFinalpart4Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1952,
   .op .MSTORE,
   .push 2 300,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND]

def unpackFinalpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x11 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1952
  let v2 : UInt256 := MachineState.readWord v1 300
  let v3 : UInt256 := UInt256.land x11 v2
  {s with pc := UInt256.ofNat 8177, memory := v1, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem unpackFinalpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalpart4Program {s with pc := UInt256.ofNat 8165, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (unpackFinalpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha300 : (300 : UInt256).toNat = 300 := rfl
  have hf300 := Monpro.activeWords_fix s 300 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : UInt256).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, unpackFinalpart4Program, unpackFinalpart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha300, hf300, ha1952, hf1952]


def unpackFinalpart5Program : List Instr :=
  [.push 2 1984,
   .op .MSTORE,
   .push 2 270,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 2016,
   .op .MSTORE]

def unpackFinalpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1984
  let v1 : UInt256 := MachineState.readWord v0 270
  let v2 : UInt256 := UInt256.land x11 v1
  let v3 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v2.toNat 32) 2016
  {s with pc := UInt256.ofNat 8191, memory := v3, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem unpackFinalpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalpart5Program {s with pc := UInt256.ofNat 8177, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (unpackFinalpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha270 : (270 : UInt256).toNat = 270 := rfl
  have hf270 := Monpro.activeWords_fix s 270 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : UInt256).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : UInt256).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, unpackFinalpart5Program, unpackFinalpart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha270, hf270, ha1984, hf1984, ha2016, hf2016]


def unpackFinalpart6Program : List Instr :=
  [.push 2 256,
   .op .MLOAD,
   .push 1 128,
   .op .SHR,
   .push 2 2048,
   .op .MSTORE]

def unpackFinalpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 256
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 128)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2048
  {s with pc := UInt256.ofNat 8202, memory := v2, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem unpackFinalpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalpart6Program {s with pc := UInt256.ofNat 8191, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (unpackFinalpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha256 : (256 : UInt256).toNat = 256 := rfl
  have hf256 := Monpro.activeWords_fix s 256 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : UInt256).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, unpackFinalpart6Program, unpackFinalpart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha256, hf256, ha2048, hf2048]


def unpackFinalProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 480,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1792,
   .op .MSTORE,
   .push 2 450,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1824,
   .op .MSTORE,
   .push 2 420,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1856,
   .op .MSTORE,
   .push 2 390,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1888,
   .op .MSTORE,
   .push 2 360,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1920,
   .op .MSTORE,
   .push 2 330,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1952,
   .op .MSTORE,
   .push 2 300,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 1984,
   .op .MSTORE,
   .push 2 270,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 2016,
   .op .MSTORE,
   .push 2 256,
   .op .MLOAD,
   .push 1 128,
   .op .SHR,
   .push 2 2048,
   .op .MSTORE]

def unpackFinalModel (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 480
  let v1 : UInt256 := UInt256.land MASK v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1792
  let v3 : UInt256 := MachineState.readWord v2 450
  let v4 : UInt256 := UInt256.land MASK v3
  let v5 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded v4.toNat 32) 1824
  let v6 : UInt256 := MachineState.readWord v5 420
  let v7 : UInt256 := UInt256.land MASK v6
  let v8 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v7.toNat 32) 1856
  let v9 : UInt256 := MachineState.readWord v8 390
  let v10 : UInt256 := UInt256.land MASK v9
  let v11 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v10.toNat 32) 1888
  let v12 : UInt256 := MachineState.readWord v11 360
  let v13 : UInt256 := UInt256.land MASK v12
  let v14 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v13.toNat 32) 1920
  let v15 : UInt256 := MachineState.readWord v14 330
  let v16 : UInt256 := UInt256.land MASK v15
  let v17 : ByteArray := MachineState.writeBytes v14 (Data.Bytes.natToBytesPadded v16.toNat 32) 1952
  let v18 : UInt256 := MachineState.readWord v17 300
  let v19 : UInt256 := UInt256.land MASK v18
  let v20 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v19.toNat 32) 1984
  let v21 : UInt256 := MachineState.readWord v20 270
  let v22 : UInt256 := UInt256.land MASK v21
  let v23 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v22.toNat 32) 2016
  let v24 : UInt256 := MachineState.readWord v23 256
  let v25 : UInt256 := UInt256.shiftRight v24 (UInt256.ofNat 128)
  let v26 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v25.toNat 32) 2048
  {s with pc := UInt256.ofNat 8202, memory := v26, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest}

theorem unpackFinal_run (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalProgram {s with pc := UInt256.ofNat 8110, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} =
      some (unpackFinalModel s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 480
  let v1 : UInt256 := UInt256.land MASK v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1792
  let v3 : UInt256 := MachineState.readWord v2 450
  let v4 : UInt256 := UInt256.land MASK v3
  let v5 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded v4.toNat 32) 1824
  let v6 : UInt256 := MachineState.readWord v5 420
  let v7 : UInt256 := UInt256.land MASK v6
  let v8 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v7.toNat 32) 1856
  let v9 : UInt256 := MachineState.readWord v8 390
  let v10 : UInt256 := UInt256.land MASK v9
  let v11 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v10.toNat 32) 1888
  let v12 : UInt256 := MachineState.readWord v11 360
  let v13 : UInt256 := UInt256.land MASK v12
  let v14 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v13.toNat 32) 1920
  let v15 : UInt256 := MachineState.readWord v14 330
  let v16 : UInt256 := UInt256.land MASK v15
  let v17 : ByteArray := MachineState.writeBytes v14 (Data.Bytes.natToBytesPadded v16.toNat 32) 1952
  let v18 : UInt256 := MachineState.readWord v17 300
  let v19 : UInt256 := UInt256.land MASK v18
  let v20 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v19.toNat 32) 1984
  let v21 : UInt256 := MachineState.readWord v20 270
  let v22 : UInt256 := UInt256.land MASK v21
  let v23 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v22.toNat 32) 2016
  let v24 : UInt256 := MachineState.readWord v23 256
  let v25 : UInt256 := UInt256.shiftRight v24 (UInt256.ofNat 128)
  let v26 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v25.toNat 32) 2048
  have h0 : runInstructions unpackFinalpart0Program {s with pc := UInt256.ofNat 8110, memory := s.memory, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 8125, memory := v2, stack := v3 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [unpackFinalpart0Model, v0, v1, v2, v3] using unpackFinalpart0_run (s) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h1 : runInstructions unpackFinalpart1Program {s with pc := UInt256.ofNat 8125, memory := v2, stack := v3 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 8137, memory := v5, stack := v7 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [unpackFinalpart1Model, v4, v5, v6, v7] using unpackFinalpart1_run ({s with memory := v2}) (v3) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h2 : runInstructions unpackFinalpart2Program {s with pc := UInt256.ofNat 8137, memory := v5, stack := v7 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 8151, memory := v11, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [unpackFinalpart2Model, v8, v9, v10, v11] using unpackFinalpart2_run ({s with memory := v5}) (v7) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h3 : runInstructions unpackFinalpart3Program {s with pc := UInt256.ofNat 8151, memory := v11, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 8165, memory := v14, stack := v15 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [unpackFinalpart3Model, v12, v13, v14, v15] using unpackFinalpart3_run ({s with memory := v11}) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h4 : runInstructions unpackFinalpart4Program {s with pc := UInt256.ofNat 8165, memory := v14, stack := v15 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 8177, memory := v17, stack := v19 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [unpackFinalpart4Model, v16, v17, v18, v19] using unpackFinalpart4_run ({s with memory := v14}) (v15) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h5 : runInstructions unpackFinalpart5Program {s with pc := UInt256.ofNat 8177, memory := v17, stack := v19 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 8191, memory := v23, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [unpackFinalpart5Model, v20, v21, v22, v23] using unpackFinalpart5_run ({s with memory := v17}) (v19) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h6 : runInstructions unpackFinalpart6Program {s with pc := UInt256.ofNat 8191, memory := v23, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 8202, memory := v26, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [unpackFinalpart6Model, v24, v25, v26] using unpackFinalpart6_run ({s with memory := v23}) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 h6))))))


end CycleSubmission.Execution

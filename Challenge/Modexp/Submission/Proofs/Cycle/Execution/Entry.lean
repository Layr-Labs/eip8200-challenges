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

def entrypart0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push 5 16,
   .op .SHR,
   .push 2 2368,
   .op .MLOAD]

def entrypart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := s.memory
  let v1 : UInt256 := UInt256.shiftRight x5 (UInt256.ofNat 16)
  let v2 : UInt256 := MachineState.readWord v0 2368
  {s with pc := UInt256.ofNat 5978, memory := v0, stack := v2 :: v1 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem entrypart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart0Program {s with pc := UInt256.ofNat 5964, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (entrypart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2368 : (2368 : UInt256).toNat = 2368 := rfl
  have hf2368 := Monpro.activeWords_fix s 2368 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart0Program, entrypart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2368, hf2368]


def entrypart1Program : List Instr :=
  [.push 1 16,
   .op .SHR,
   .push 1 134,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 1 224,
   .op .MLOAD]

def entrypart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 16)
  let v1 : UInt256 := MachineState.readWord s.memory 134
  let v2 : UInt256 := UInt256.land x1 v1
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 5989, memory := s.memory, stack := v3 :: v2 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem entrypart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart1Program {s with pc := UInt256.ofNat 5978, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (entrypart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha134 : (134 : UInt256).toNat = 134 := rfl
  have hf134 := Monpro.activeWords_fix s 134 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart1Program, entrypart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha134, hf134, ha224, hf224]


def entrypart2Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1344,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨2, by decide⟩)]

def entrypart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x3 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1344
  {s with pc := UInt256.ofNat 5999, memory := v1, stack := x3 :: v0 :: x1 :: x2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem entrypart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart2Program {s with pc := UInt256.ofNat 5989, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (entrypart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart2Program, entrypart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1344, hf1344]


def entrypart3Program : List Instr :=
  [.push 1 194,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1376,
   .op .MSTORE,
   .push 0 0,
   .op .MLOAD]

def entrypart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 194
  let v1 : UInt256 := UInt256.land x0 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1376
  let v3 : UInt256 := MachineState.readWord v2 0
  {s with pc := UInt256.ofNat 6011, memory := v2, stack := v3 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem entrypart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart3Program {s with pc := UInt256.ofNat 5999, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (entrypart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha194 : (194 : UInt256).toNat = 194 := rfl
  have hf194 := Monpro.activeWords_fix s 194 32 (by decide) (by norm_num) hact
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart3Program, entrypart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha194, hf194, ha1376, hf1376]


def entrypart4Program : List Instr :=
  [.push 1 128,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1600,
   .op .MSTORE,
   .push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,
   .push 1 14,
   .op .MLOAD]

def entrypart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 128)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1600
  let v2 : UInt256 := MachineState.readWord v1 14
  {s with pc := UInt256.ofNat 6055, memory := v1, stack := v2 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest}

theorem entrypart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart4Program {s with pc := UInt256.ofNat 6011, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest} =
      some (entrypart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 24) : rest.length + j < 1024 := by omega
  have ha14 : (14 : UInt256).toNat = 14 := rfl
  have hf14 := Monpro.activeWords_fix s 14 32 (by decide) (by norm_num) hact
  have ha1600 : (1600 : UInt256).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart4Program, entrypart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha14, hf14, ha1600, hf1600]


def entrypart5Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1568,
   .op .MSTORE,
   .push 1 74,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩)]

def entrypart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x4 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1568
  let v2 : UInt256 := MachineState.readWord v1 74
  {s with pc := UInt256.ofNat 6066, memory := v1, stack := x4 :: v2 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest}

theorem entrypart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart5Program {s with pc := UInt256.ofNat 6055, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest} =
      some (entrypart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  have ha74 : (74 : UInt256).toNat = 74 := rfl
  have hf74 := Monpro.activeWords_fix s 74 32 (by decide) (by norm_num) hact
  have ha1568 : (1568 : UInt256).toNat = 1568 := rfl
  have hf1568 := Monpro.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart5Program, entrypart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha74, hf74, ha1568, hf1568]


def entrypart6Program : List Instr :=
  [.op .AND,
   .push 2 2546,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .push 2 2576,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩)]

def entrypart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : UInt256 := MachineState.readWord s.memory 2546
  let v2 : UInt256 := UInt256.land x6 v1
  let v3 : UInt256 := MachineState.readWord s.memory 2576
  {s with pc := UInt256.ofNat 6078, memory := s.memory, stack := x6 :: v3 :: v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest}

theorem entrypart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart6Program {s with pc := UInt256.ofNat 6066, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest} =
      some (entrypart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 28) : rest.length + j < 1024 := by omega
  have ha2546 : (2546 : UInt256).toNat = 2546 := rfl
  have hf2546 := Monpro.activeWords_fix s 2546 32 (by decide) (by norm_num) hact
  have ha2576 : (2576 : UInt256).toNat = 2576 := rfl
  have hf2576 := Monpro.activeWords_fix s 2576 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart6Program, entrypart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2546, hf2546, ha2576, hf2576]


def entrypart7Program : List Instr :=
  [.op .AND,
   .push 1 104,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push 1 44,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def entrypart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : UInt256 := MachineState.readWord s.memory 104
  let v2 : UInt256 := UInt256.land x8 v1
  let v3 : UInt256 := MachineState.readWord s.memory 44
  {s with pc := UInt256.ofNat 6088, memory := s.memory, stack := x8 :: v3 :: v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest}

theorem entrypart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart7Program {s with pc := UInt256.ofNat 6078, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest} =
      some (entrypart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have ha44 : (44 : UInt256).toNat = 44 := rfl
  have hf44 := Monpro.activeWords_fix s 44 32 (by decide) (by norm_num) hact
  have ha104 : (104 : UInt256).toNat = 104 := rfl
  have hf104 := Monpro.activeWords_fix s 104 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart7Program, entrypart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha44, hf44, ha104, hf104]


def entrypart8Program : List Instr :=
  [.op .AND,
   .push 1 164,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push 2 2592,
   .op .MLOAD,
   .push 1 112]

def entrypart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : UInt256 := MachineState.readWord s.memory 164
  let v2 : UInt256 := UInt256.land x10 v1
  let v3 : UInt256 := MachineState.readWord s.memory 2592
  {s with pc := UInt256.ofNat 6100, memory := s.memory, stack := (UInt256.ofNat 112) :: v3 :: v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: rest}

theorem entrypart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart8Program {s with pc := UInt256.ofNat 6088, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: rest} =
      some (entrypart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have ha164 : (164 : UInt256).toNat = 164 := rfl
  have hf164 := Monpro.activeWords_fix s 164 32 (by decide) (by norm_num) hact
  have ha2592 : (2592 : UInt256).toNat = 2592 := rfl
  have hf2592 := Monpro.activeWords_fix s 2592 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart8Program, entrypart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha164, hf164, ha2592, hf2592]


def entrypart9Program : List Instr :=
  [.op .SHL,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 2 2516,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩)]

def entrypart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 x0
  let v1 : UInt256 := UInt256.land x12 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  let v3 : UInt256 := MachineState.readWord v2 2516
  {s with pc := UInt256.ofNat 6112, memory := v2, stack := x12 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: rest}

theorem entrypart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart9Program {s with pc := UInt256.ofNat 6100, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: rest} =
      some (entrypart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2516 : (2516 : UInt256).toNat = 2516 := rfl
  have hf2516 := Monpro.activeWords_fix s 2516 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart9Program, entrypart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha2516, hf2516]


def entrypart10Program : List Instr :=
  [.op .AND,
   .push 1 32,
   .op .MSTORE,
   .push 2 2486,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 64,
   .op .MSTORE]

def entrypart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 32
  let v2 : UInt256 := MachineState.readWord v1 2486
  let v3 : UInt256 := UInt256.land x12 v2
  let v4 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v3.toNat 32) 64
  {s with pc := UInt256.ofNat 6125, memory := v4, stack := x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: rest}

theorem entrypart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart10Program {s with pc := UInt256.ofNat 6112, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: rest} =
      some (entrypart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha2486 : (2486 : UInt256).toNat = 2486 := rfl
  have hf2486 := Monpro.activeWords_fix s 2486 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart10Program, entrypart10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha64, hf64, ha2486, hf2486]


def entrypart11Program : List Instr :=
  [.push 2 2456,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 96,
   .op .MSTORE,
   .push 2 2426,
   .op .MLOAD]

def entrypart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2456
  let v1 : UInt256 := UInt256.land x10 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 96
  let v3 : UInt256 := MachineState.readWord v2 2426
  {s with pc := UInt256.ofNat 6138, memory := v2, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: rest}

theorem entrypart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart11Program {s with pc := UInt256.ofNat 6125, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: rest} =
      some (entrypart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha2426 : (2426 : UInt256).toNat = 2426 := rfl
  have hf2426 := Monpro.activeWords_fix s 2426 32 (by decide) (by norm_num) hact
  have ha2456 : (2456 : UInt256).toNat = 2456 := rfl
  have hf2456 := Monpro.activeWords_fix s 2456 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart11Program, entrypart11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha2426, hf2426, ha2456, hf2456]


def entrypart12Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 128,
   .op .MSTORE,
   .push 2 2396,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND]

def entrypart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x11 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 128
  let v2 : UInt256 := MachineState.readWord v1 2396
  let v3 : UInt256 := UInt256.land x11 v2
  {s with pc := UInt256.ofNat 6149, memory := v1, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: rest}

theorem entrypart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart12Program {s with pc := UInt256.ofNat 6138, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: rest} =
      some (entrypart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha2396 : (2396 : UInt256).toNat = 2396 := rfl
  have hf2396 := Monpro.activeWords_fix s 2396 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart12Program, entrypart12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha2396, hf2396]


def entrypart13Program : List Instr :=
  [.push 1 160,
   .op .MSTORE]

def entrypart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 160
  {s with pc := UInt256.ofNat 6152, memory := v0, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: rest}

theorem entrypart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart13Program {s with pc := UInt256.ofNat 6149, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: rest} =
      some (entrypart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart13Program, entrypart13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push 5 16,
   .op .SHR,
   .push 2 2368,
   .op .MLOAD,
   .push 1 16,
   .op .SHR,
   .push 1 134,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1344,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .push 1 194,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1376,
   .op .MSTORE,
   .push 0 0,
   .op .MLOAD,
   .push 1 128,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1600,
   .op .MSTORE,
   .push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,
   .push 1 14,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1568,
   .op .MSTORE,
   .push 1 74,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .push 2 2546,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .push 2 2576,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .push 1 104,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push 1 44,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push 1 164,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .push 2 2592,
   .op .MLOAD,
   .push 1 112,
   .op .SHL,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 2 2516,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 32,
   .op .MSTORE,
   .push 2 2486,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 64,
   .op .MSTORE,
   .push 2 2456,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 96,
   .op .MSTORE,
   .push 2 2426,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 128,
   .op .MSTORE,
   .push 2 2396,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .push 1 160,
   .op .MSTORE]

def entryModel (s : State) (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := s.memory
  let v1 : UInt256 := UInt256.shiftRight allones (UInt256.ofNat 16)
  let v2 : UInt256 := MachineState.readWord v0 2368
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  let v4 : UInt256 := MachineState.readWord v0 134
  let v5 : UInt256 := UInt256.land v1 v4
  let v6 : UInt256 := MachineState.readWord v0 224
  let v7 : UInt256 := UInt256.land v1 v6
  let v8 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v7.toNat 32) 1344
  let v9 : UInt256 := MachineState.readWord v8 194
  let v10 : UInt256 := UInt256.land v1 v9
  let v11 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v10.toNat 32) 1376
  let v12 : UInt256 := MachineState.readWord v11 0
  let v13 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 128)
  let v14 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v13.toNat 32) 1600
  let v15 : UInt256 := MachineState.readWord v14 14
  let v16 : UInt256 := UInt256.land v1 v15
  let v17 : ByteArray := MachineState.writeBytes v14 (Data.Bytes.natToBytesPadded v16.toNat 32) 1568
  let v18 : UInt256 := MachineState.readWord v17 74
  let v19 : UInt256 := UInt256.land v1 v18
  let v20 : UInt256 := MachineState.readWord v17 2546
  let v21 : UInt256 := UInt256.land v1 v20
  let v22 : UInt256 := MachineState.readWord v17 2576
  let v23 : UInt256 := UInt256.land v1 v22
  let v24 : UInt256 := MachineState.readWord v17 104
  let v25 : UInt256 := UInt256.land v1 v24
  let v26 : UInt256 := MachineState.readWord v17 44
  let v27 : UInt256 := UInt256.land v1 v26
  let v28 : UInt256 := MachineState.readWord v17 164
  let v29 : UInt256 := UInt256.land v1 v28
  let v30 : UInt256 := MachineState.readWord v17 2592
  let v31 : UInt256 := UInt256.shiftLeft v30 (UInt256.ofNat 112)
  let v32 : UInt256 := UInt256.land v1 v31
  let v33 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v32.toNat 32) 768
  let v34 : UInt256 := MachineState.readWord v33 2516
  let v35 : UInt256 := UInt256.land v1 v34
  let v36 : ByteArray := MachineState.writeBytes v33 (Data.Bytes.natToBytesPadded v35.toNat 32) 32
  let v37 : UInt256 := MachineState.readWord v36 2486
  let v38 : UInt256 := UInt256.land v1 v37
  let v39 : ByteArray := MachineState.writeBytes v36 (Data.Bytes.natToBytesPadded v38.toNat 32) 64
  let v40 : UInt256 := MachineState.readWord v39 2456
  let v41 : UInt256 := UInt256.land v1 v40
  let v42 : ByteArray := MachineState.writeBytes v39 (Data.Bytes.natToBytesPadded v41.toNat 32) 96
  let v43 : UInt256 := MachineState.readWord v42 2426
  let v44 : UInt256 := UInt256.land v1 v43
  let v45 : ByteArray := MachineState.writeBytes v42 (Data.Bytes.natToBytesPadded v44.toNat 32) 128
  let v46 : UInt256 := MachineState.readWord v45 2396
  let v47 : UInt256 := UInt256.land v1 v46
  let v48 : ByteArray := MachineState.writeBytes v45 (Data.Bytes.natToBytesPadded v47.toNat 32) 160
  {s with pc := UInt256.ofNat 6152, memory := v48, stack := v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}

theorem entry_run (s : State) (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram {s with pc := UInt256.ofNat 5964, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
      some (entryModel s pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  let v0 : ByteArray := s.memory
  let v1 : UInt256 := UInt256.shiftRight allones (UInt256.ofNat 16)
  let v2 : UInt256 := MachineState.readWord v0 2368
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  let v4 : UInt256 := MachineState.readWord v0 134
  let v5 : UInt256 := UInt256.land v1 v4
  let v6 : UInt256 := MachineState.readWord v0 224
  let v7 : UInt256 := UInt256.land v1 v6
  let v8 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v7.toNat 32) 1344
  let v9 : UInt256 := MachineState.readWord v8 194
  let v10 : UInt256 := UInt256.land v1 v9
  let v11 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v10.toNat 32) 1376
  let v12 : UInt256 := MachineState.readWord v11 0
  let v13 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 128)
  let v14 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v13.toNat 32) 1600
  let v15 : UInt256 := MachineState.readWord v14 14
  let v16 : UInt256 := UInt256.land v1 v15
  let v17 : ByteArray := MachineState.writeBytes v14 (Data.Bytes.natToBytesPadded v16.toNat 32) 1568
  let v18 : UInt256 := MachineState.readWord v17 74
  let v19 : UInt256 := UInt256.land v1 v18
  let v20 : UInt256 := MachineState.readWord v17 2546
  let v21 : UInt256 := UInt256.land v1 v20
  let v22 : UInt256 := MachineState.readWord v17 2576
  let v23 : UInt256 := UInt256.land v1 v22
  let v24 : UInt256 := MachineState.readWord v17 104
  let v25 : UInt256 := UInt256.land v1 v24
  let v26 : UInt256 := MachineState.readWord v17 44
  let v27 : UInt256 := UInt256.land v1 v26
  let v28 : UInt256 := MachineState.readWord v17 164
  let v29 : UInt256 := UInt256.land v1 v28
  let v30 : UInt256 := MachineState.readWord v17 2592
  let v31 : UInt256 := UInt256.shiftLeft v30 (UInt256.ofNat 112)
  let v32 : UInt256 := UInt256.land v1 v31
  let v33 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v32.toNat 32) 768
  let v34 : UInt256 := MachineState.readWord v33 2516
  let v35 : UInt256 := UInt256.land v1 v34
  let v36 : ByteArray := MachineState.writeBytes v33 (Data.Bytes.natToBytesPadded v35.toNat 32) 32
  let v37 : UInt256 := MachineState.readWord v36 2486
  let v38 : UInt256 := UInt256.land v1 v37
  let v39 : ByteArray := MachineState.writeBytes v36 (Data.Bytes.natToBytesPadded v38.toNat 32) 64
  let v40 : UInt256 := MachineState.readWord v39 2456
  let v41 : UInt256 := UInt256.land v1 v40
  let v42 : ByteArray := MachineState.writeBytes v39 (Data.Bytes.natToBytesPadded v41.toNat 32) 96
  let v43 : UInt256 := MachineState.readWord v42 2426
  let v44 : UInt256 := UInt256.land v1 v43
  let v45 : ByteArray := MachineState.writeBytes v42 (Data.Bytes.natToBytesPadded v44.toNat 32) 128
  let v46 : UInt256 := MachineState.readWord v45 2396
  let v47 : UInt256 := UInt256.land v1 v46
  let v48 : ByteArray := MachineState.writeBytes v45 (Data.Bytes.natToBytesPadded v47.toNat 32) 160
  have htail : (ret :: rest).length ≤ 960 := by
    simp only [List.length_cons]
    omega
  have h0 : runInstructions entrypart0Program {s with pc := UInt256.ofNat 5964, memory := s.memory, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5978, memory := v0, stack := v2 :: v1 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart0Model, v0, v1, v2] using entrypart0_run (s) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest (by omega) hact
  have h1 : runInstructions entrypart1Program {s with pc := UInt256.ofNat 5978, memory := v0, stack := v2 :: v1 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5989, memory := v0, stack := v6 :: v5 :: v3 :: v1 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart1Model, v3, v4, v5, v6] using entrypart1_run ({s with memory := v0}) (v2) (v1) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h2 : runInstructions entrypart2Program {s with pc := UInt256.ofNat 5989, memory := v0, stack := v6 :: v5 :: v3 :: v1 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5999, memory := v8, stack := v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart2Model, v7, v8] using entrypart2_run ({s with memory := v0}) (v6) (v5) (v3) (v1) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h3 : runInstructions entrypart3Program {s with pc := UInt256.ofNat 5999, memory := v8, stack := v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6011, memory := v11, stack := v12 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart3Model, v9, v10, v11, v12] using entrypart3_run ({s with memory := v8}) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h4 : runInstructions entrypart4Program {s with pc := UInt256.ofNat 6011, memory := v11, stack := v12 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6055, memory := v14, stack := v15 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart4Model, v13, v14, v15] using entrypart4_run ({s with memory := v11}) (v12) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h5 : runInstructions entrypart5Program {s with pc := UInt256.ofNat 6055, memory := v14, stack := v15 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6066, memory := v17, stack := v1 :: v18 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart5Model, v16, v17, v18] using entrypart5_run ({s with memory := v14}) (v15) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h6 : runInstructions entrypart6Program {s with pc := UInt256.ofNat 6066, memory := v17, stack := v1 :: v18 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6078, memory := v17, stack := v1 :: v22 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart6Model, v19, v20, v21, v22] using entrypart6_run ({s with memory := v17}) (v1) (v18) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h7 : runInstructions entrypart7Program {s with pc := UInt256.ofNat 6078, memory := v17, stack := v1 :: v22 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6088, memory := v17, stack := v1 :: v26 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart7Model, v23, v24, v25, v26] using entrypart7_run ({s with memory := v17}) (v1) (v22) (v21) (v19) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h8 : runInstructions entrypart8Program {s with pc := UInt256.ofNat 6088, memory := v17, stack := v1 :: v26 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6100, memory := v17, stack := (UInt256.ofNat 112) :: v30 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart8Model, v27, v28, v29, v30] using entrypart8_run ({s with memory := v17}) (v1) (v26) (v25) (v23) (v21) (v19) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h9 : runInstructions entrypart9Program {s with pc := UInt256.ofNat 6100, memory := v17, stack := (UInt256.ofNat 112) :: v30 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6112, memory := v33, stack := v1 :: v34 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart9Model, v31, v32, v33, v34] using entrypart9_run ({s with memory := v17}) ((UInt256.ofNat 112)) (v30) (v29) (v27) (v25) (v23) (v21) (v19) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h10 : runInstructions entrypart10Program {s with pc := UInt256.ofNat 6112, memory := v33, stack := v1 :: v34 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6125, memory := v39, stack := v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart10Model, v35, v36, v37, v38, v39] using entrypart10_run ({s with memory := v33}) (v1) (v34) (v29) (v27) (v25) (v23) (v21) (v19) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h11 : runInstructions entrypart11Program {s with pc := UInt256.ofNat 6125, memory := v39, stack := v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6138, memory := v42, stack := v43 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart11Model, v40, v41, v42, v43] using entrypart11_run ({s with memory := v39}) (v29) (v27) (v25) (v23) (v21) (v19) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h12 : runInstructions entrypart12Program {s with pc := UInt256.ofNat 6138, memory := v42, stack := v43 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6149, memory := v45, stack := v47 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart12Model, v44, v45, v46, v47] using entrypart12_run ({s with memory := v42}) (v43) (v29) (v27) (v25) (v23) (v21) (v19) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  have h13 : runInstructions entrypart13Program {s with pc := UInt256.ofNat 6149, memory := v45, stack := v47 :: v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 6152, memory := v48, stack := v29 :: v27 :: v25 :: v23 :: v21 :: v19 :: v16 :: (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v13 :: v10 :: v1 :: v7 :: v5 :: v3 :: counter :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart13Model, v48] using entrypart13_run ({s with memory := v45}) (v47) (v29) (v27) (v25) (v23) (v21) (v19) (v16) ((UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247)) (v13) (v10) (v1) (v7) (v5) (v3) (counter) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret :: rest) htail hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution

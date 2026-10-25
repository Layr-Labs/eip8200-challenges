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

def productColumn6part0Program : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 0 0,
   .op .MLOAD]

def productColumn6part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 192
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  let v3 : UInt256 := MachineState.readWord s.memory 0
  {s with pc := UInt256.ofNat 8523, memory := s.memory, stack := v3 :: x16 :: x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn6part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part0Program {s with pc := UInt256.ofNat 8514, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn6part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part0Program, productColumn6part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha192, hf192]


def productColumn6part1Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def productColumn6part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 224
  let v3 : UInt256 := UInt256.mulMod v2 x5 x12
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 8532, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn6part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part1Program {s with pc := UInt256.ofNat 8523, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn6part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part1Program, productColumn6part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def productColumn6part2Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def productColumn6part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1216
  let v1 : UInt256 := UInt256.mulMod v0 x11 x9
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 8542, memory := s.memory, stack := x13 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn6part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part2Program {s with pc := UInt256.ofNat 8532, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn6part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part2Program, productColumn6part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def productColumn6part3Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def productColumn6part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2720
  let v1 : UInt256 := x3 * v0
  let v2 : UInt256 := UInt256.land x14 v1
  {s with pc := UInt256.ofNat 8552, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn6part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part3Program {s with pc := UInt256.ofNat 8542, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn6part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part3Program, productColumn6part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2720, hf2720]


def productColumn6part4Program : List Instr :=
  [.push 2 1248,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1568,
   .op .MLOAD]

def productColumn6part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1248
  let v1 : UInt256 := UInt256.mulMod x1 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v2 x5
  let v4 : UInt256 := MachineState.readWord v0 1568
  {s with pc := UInt256.ofNat 8566, memory := v0, stack := v4 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn6part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part4Program {s with pc := UInt256.ofNat 8552, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn6part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha1568 : (1568 : UInt256).toNat = 1568 := rfl
  have hf1568 := Monpro.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part4Program, productColumn6part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248, ha1568, hf1568]


def productColumn6part5Program : List Instr :=
  [.op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩)]

def productColumn6part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 2016
  {s with pc := UInt256.ofNat 8578, memory := s.memory, stack := x1 :: v0 :: x9 :: x1 :: x8 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x0 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn6part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part5Program {s with pc := UInt256.ofNat 8566, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn6part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : UInt256).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part5Program, productColumn6part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha2016, hf2016]


def productColumn6part6Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩)]

def productColumn6part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x5 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 8586, memory := s.memory, stack := x13 :: v3 :: x4 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn6part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part6Program {s with pc := UInt256.ofNat 8578, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn6part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn6part6Program, productColumn6part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn6part7Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn6part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1984
  let v1 : UInt256 := v0 * x7
  let v2 : UInt256 := v1 + x3
  {s with pc := UInt256.ofNat 8596, memory := s.memory, stack := v2 :: x7 :: x0 :: x1 :: x2 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn6part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part7Program {s with pc := UInt256.ofNat 8586, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn6part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha1984 : (1984 : UInt256).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part7Program, productColumn6part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1984, hf1984]


def productColumn6part8Program : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩)]

def productColumn6part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 1952
  {s with pc := UInt256.ofNat 8606, memory := s.memory, stack := x0 :: x10 :: x13 :: v1 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn6part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part8Program {s with pc := UInt256.ofNat 8596, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn6part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1952 : (1952 : UInt256).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part8Program, productColumn6part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1952, hf1952]


def productColumn6part9Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩)]

def productColumn6part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x5 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 8614, memory := s.memory, stack := x13 :: v3 :: x4 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn6part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part9Program {s with pc := UInt256.ofNat 8606, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn6part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn6part9Program, productColumn6part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn6part10Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL]

def productColumn6part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := MachineState.readWord s.memory 1920
  let v2 : UInt256 := v1 * v0
  {s with pc := UInt256.ofNat 8625, memory := s.memory, stack := v2 :: x3 :: v0 :: x0 :: x1 :: x2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn6part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part10Program {s with pc := UInt256.ofNat 8614, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn6part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : UInt256).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part10Program, productColumn6part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha1920, hf1920]


def productColumn6part11Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD]

def productColumn6part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x6 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := MachineState.readWord s.memory 1888
  {s with pc := UInt256.ofNat 8637, memory := s.memory, stack := v4 :: v3 :: x14 :: v2 :: x5 :: v0 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn6part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part11Program {s with pc := UInt256.ofNat 8625, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn6part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : UInt256).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn6part11Program, productColumn6part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha1888, hf1888]


def productColumn6part12Program : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn6part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x5
  {s with pc := UInt256.ofNat 8642, memory := s.memory, stack := v1 :: x1 :: x2 :: x3 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn6part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6part12Program {s with pc := UInt256.ofNat 8637, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn6part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn6part12Program, productColumn6part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn6Program : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1248,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1568,
   .op .MLOAD,
   .op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn6Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 192
  let v1 : UInt256 := UInt256.mulMod v0 carry word0
  let v2 : UInt256 := v1 + word1
  let v3 : UInt256 := MachineState.readWord s.memory 0
  let v4 : UInt256 := UInt256.mulMod v3 word15 word10
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 224
  let v7 : UInt256 := UInt256.mulMod v6 word3 word10
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 1216
  let v10 : UInt256 := UInt256.mulMod v9 word12 word10
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := MachineState.readWord s.memory 2720
  let v13 : UInt256 := word2 * v12
  let v14 : UInt256 := UInt256.land word13 v13
  let v15 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v14.toNat 32) 1248
  let v16 : UInt256 := UInt256.mulMod v14 word14 word10
  let v17 : UInt256 := v16 + v11
  let v18 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v17 word10
  let v19 : UInt256 := MachineState.readWord v15 1568
  let v20 : UInt256 := MachineState.readWord v15 768
  let v21 : UInt256 := MachineState.readWord v15 2016
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v18
  let v24 : UInt256 := UInt256.mulMod v21 v20 word10
  let v25 : UInt256 := v24 + v18
  let v26 : UInt256 := MachineState.readWord v15 1984
  let v27 : UInt256 := v26 * word6
  let v28 : UInt256 := v27 + v23
  let v29 : UInt256 := UInt256.mulMod v26 word6 word10
  let v30 : UInt256 := v29 + v25
  let v31 : UInt256 := MachineState.readWord v15 1952
  let v32 : UInt256 := v31 * word7
  let v33 : UInt256 := v32 + v28
  let v34 : UInt256 := UInt256.mulMod v31 word7 word10
  let v35 : UInt256 := v34 + v30
  let v36 : UInt256 := MachineState.readWord v15 32
  let v37 : UInt256 := MachineState.readWord v15 1920
  let v38 : UInt256 := v37 * v36
  let v39 : UInt256 := v38 + v33
  let v40 : UInt256 := UInt256.mulMod v37 v36 word10
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := MachineState.readWord v15 64
  let v43 : UInt256 := MachineState.readWord v15 1888
  let v44 : UInt256 := v43 * v42
  let v45 : UInt256 := v44 + v39
  {s with pc := UInt256.ofNat 8642, memory := v15, stack := v45 :: v42 :: word10 :: v41 :: word9 :: v43 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest}

theorem productColumn6_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6Program {s with pc := UInt256.ofNat 8514, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} =
      some (productColumn6Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 192
  let v1 : UInt256 := UInt256.mulMod v0 carry word0
  let v2 : UInt256 := v1 + word1
  let v3 : UInt256 := MachineState.readWord s.memory 0
  let v4 : UInt256 := UInt256.mulMod v3 word15 word10
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 224
  let v7 : UInt256 := UInt256.mulMod v6 word3 word10
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 1216
  let v10 : UInt256 := UInt256.mulMod v9 word12 word10
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := MachineState.readWord s.memory 2720
  let v13 : UInt256 := word2 * v12
  let v14 : UInt256 := UInt256.land word13 v13
  let v15 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v14.toNat 32) 1248
  let v16 : UInt256 := UInt256.mulMod v14 word14 word10
  let v17 : UInt256 := v16 + v11
  let v18 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v17 word10
  let v19 : UInt256 := MachineState.readWord v15 1568
  let v20 : UInt256 := MachineState.readWord v15 768
  let v21 : UInt256 := MachineState.readWord v15 2016
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v18
  let v24 : UInt256 := UInt256.mulMod v21 v20 word10
  let v25 : UInt256 := v24 + v18
  let v26 : UInt256 := MachineState.readWord v15 1984
  let v27 : UInt256 := v26 * word6
  let v28 : UInt256 := v27 + v23
  let v29 : UInt256 := UInt256.mulMod v26 word6 word10
  let v30 : UInt256 := v29 + v25
  let v31 : UInt256 := MachineState.readWord v15 1952
  let v32 : UInt256 := v31 * word7
  let v33 : UInt256 := v32 + v28
  let v34 : UInt256 := UInt256.mulMod v31 word7 word10
  let v35 : UInt256 := v34 + v30
  let v36 : UInt256 := MachineState.readWord v15 32
  let v37 : UInt256 := MachineState.readWord v15 1920
  let v38 : UInt256 := v37 * v36
  let v39 : UInt256 := v38 + v33
  let v40 : UInt256 := UInt256.mulMod v37 v36 word10
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := MachineState.readWord v15 64
  let v43 : UInt256 := MachineState.readWord v15 1888
  let v44 : UInt256 := v43 * v42
  let v45 : UInt256 := v44 + v39
  have h0 : runInstructions productColumn6part0Program {s with pc := UInt256.ofNat 8514, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8523, memory := s.memory, stack := v3 :: word15 :: word10 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part0Model, v0, v1, v2, v3] using productColumn6part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h1 : runInstructions productColumn6part1Program {s with pc := UInt256.ofNat 8523, memory := s.memory, stack := v3 :: word15 :: word10 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8532, memory := s.memory, stack := v8 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part1Model, v4, v5, v6, v7, v8] using productColumn6part1_run (s) (v3) (word15) (word10) (v2) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h2 : runInstructions productColumn6part2Program {s with pc := UInt256.ofNat 8532, memory := s.memory, stack := v8 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8542, memory := s.memory, stack := word14 :: word10 :: v11 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part2Model, v9, v10, v11] using productColumn6part2_run (s) (v8) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h3 : runInstructions productColumn6part3Program {s with pc := UInt256.ofNat 8542, memory := s.memory, stack := word14 :: word10 :: v11 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8552, memory := s.memory, stack := v14 :: v14 :: word14 :: word10 :: v11 :: word10 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part3Model, v12, v13, v14] using productColumn6part3_run (s) (word14) (word10) (v11) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h4 : runInstructions productColumn6part4Program {s with pc := UInt256.ofNat 8552, memory := s.memory, stack := v14 :: v14 :: word14 :: word10 :: v11 :: word10 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8566, memory := v15, stack := v19 :: v18 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part4Model, v15, v16, v17, v18, v19] using productColumn6part4_run (s) (v14) (v14) (word14) (word10) (v11) (word10) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h5 : runInstructions productColumn6part5Program {s with pc := UInt256.ofNat 8566, memory := v15, stack := v19 :: v18 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8578, memory := v15, stack := v18 :: v20 :: word10 :: v18 :: word9 :: v21 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part5Model, v20, v21] using productColumn6part5_run ({s with memory := v15}) (v19) (v18) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h6 : runInstructions productColumn6part6Program {s with pc := UInt256.ofNat 8578, memory := v15, stack := v18 :: v20 :: word10 :: v18 :: word9 :: v21 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8586, memory := v15, stack := word10 :: v25 :: word9 :: v23 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part6Model, v22, v23, v24, v25] using productColumn6part6_run ({s with memory := v15}) (v18) (v20) (word10) (v18) (word9) (v21) (word3) (word4) (word5) (word6) (word7) (word8) (v19) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h7 : runInstructions productColumn6part7Program {s with pc := UInt256.ofNat 8586, memory := v15, stack := word10 :: v25 :: word9 :: v23 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8596, memory := v15, stack := v28 :: word6 :: word10 :: v25 :: word9 :: v26 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part7Model, v26, v27, v28] using productColumn6part7_run ({s with memory := v15}) (word10) (v25) (word9) (v23) (word3) (word4) (word5) (word6) (word7) (word8) (v19) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h8 : runInstructions productColumn6part8Program {s with pc := UInt256.ofNat 8596, memory := v15, stack := v28 :: word6 :: word10 :: v25 :: word9 :: v26 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8606, memory := v15, stack := v28 :: word7 :: word10 :: v30 :: word9 :: v31 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part8Model, v29, v30, v31] using productColumn6part8_run ({s with memory := v15}) (v28) (word6) (word10) (v25) (word9) (v26) (word3) (word4) (word5) (word6) (word7) (word8) (v19) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h9 : runInstructions productColumn6part9Program {s with pc := UInt256.ofNat 8606, memory := v15, stack := v28 :: word7 :: word10 :: v30 :: word9 :: v31 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8614, memory := v15, stack := word10 :: v35 :: word9 :: v33 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part9Model, v32, v33, v34, v35] using productColumn6part9_run ({s with memory := v15}) (v28) (word7) (word10) (v30) (word9) (v31) (word3) (word4) (word5) (word6) (word7) (word8) (v19) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h10 : runInstructions productColumn6part10Program {s with pc := UInt256.ofNat 8614, memory := v15, stack := word10 :: v35 :: word9 :: v33 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8625, memory := v15, stack := v38 :: v33 :: v36 :: word10 :: v35 :: word9 :: v37 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part10Model, v36, v37, v38] using productColumn6part10_run ({s with memory := v15}) (word10) (v35) (word9) (v33) (word3) (word4) (word5) (word6) (word7) (word8) (v19) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h11 : runInstructions productColumn6part11Program {s with pc := UInt256.ofNat 8625, memory := v15, stack := v38 :: v33 :: v36 :: word10 :: v35 :: word9 :: v37 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8637, memory := v15, stack := v43 :: v42 :: word10 :: v41 :: word9 :: v39 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part11Model, v39, v40, v41, v42, v43] using productColumn6part11_run ({s with memory := v15}) (v38) (v33) (v36) (word10) (v35) (word9) (v37) (word3) (word4) (word5) (word6) (word7) (word8) (v19) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h12 : runInstructions productColumn6part12Program {s with pc := UInt256.ofNat 8637, memory := v15, stack := v43 :: v42 :: word10 :: v41 :: word9 :: v39 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 8642, memory := v15, stack := v45 :: v42 :: word10 :: v41 :: word9 :: v43 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: v19 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [productColumn6part12Model, v44, v45] using productColumn6part12_run ({s with memory := v15}) (v43) (v42) (word10) (v41) (word9) (v39) (word3) (word4) (word5) (word6) (word7) (word8) (v19) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution

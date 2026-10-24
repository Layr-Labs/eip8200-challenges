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

def productColumn11part0Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn11part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x4
  let v2 : UInt256 := UInt256.mulMod x0 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 9622, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn11part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part0Program {s with pc := UInt256.ofNat 9614, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn11part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn11part0Program, productColumn11part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn11part1Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn11part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 1888
  {s with pc := UInt256.ofNat 9633, memory := s.memory, stack := v1 :: v0 :: x1 :: v0 :: x9 :: x0 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn11part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part1Program {s with pc := UInt256.ofNat 9622, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn11part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : UInt256).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part1Program, productColumn11part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha1888, hf1888]


def productColumn11part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def productColumn11part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x6 x3 x4
  let v3 : UInt256 := v2 + x5
  let v4 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 9642, memory := s.memory, stack := v4 :: x14 :: v3 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn11part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part2Program {s with pc := UInt256.ofNat 9633, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn11part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part2Program, productColumn11part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def productColumn11part3Program : List Instr :=
  [.push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn11part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1856
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x3
  {s with pc := UInt256.ofNat 9652, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn11part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part3Program {s with pc := UInt256.ofNat 9642, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn11part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : UInt256).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part3Program, productColumn11part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1856, hf1856]


def productColumn11part4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩)]

def productColumn11part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 1824
  {s with pc := UInt256.ofNat 9662, memory := s.memory, stack := x5 :: x4 :: x5 :: x12 :: v1 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn11part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part4Program {s with pc := UInt256.ofNat 9652, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn11part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1824 : (1824 : UInt256).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part4Program, productColumn11part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1824, hf1824]


def productColumn11part5Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1088,
   .op .MLOAD]

def productColumn11part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x5 x2 x3
  let v3 : UInt256 := v2 + x4
  let v4 : UInt256 := MachineState.readWord s.memory 1088
  {s with pc := UInt256.ofNat 9673, memory := s.memory, stack := v4 :: v1 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn11part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part5Program {s with pc := UInt256.ofNat 9662, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn11part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part5Program, productColumn11part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def productColumn11part6Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn11part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x11 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 192
  let v3 : UInt256 := x9 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 9682, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn11part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part6Program {s with pc := UInt256.ofNat 9673, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn11part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part6Program, productColumn11part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def productColumn11part7Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩)]

def productColumn11part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := x3 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 9691, memory := s.memory, stack := x7 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn11part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part7Program {s with pc := UInt256.ofNat 9682, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn11part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part7Program, productColumn11part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha224, hf224]


def productColumn11part8Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩)]

def productColumn11part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  let v3 : UInt256 := x6 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 9701, memory := s.memory, stack := x7 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn11part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part8Program {s with pc := UInt256.ofNat 9691, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn11part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part8Program, productColumn11part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def productColumn11part9Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def productColumn11part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x15 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1280
  let v3 : UInt256 := v2 * x16
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 9711, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn11part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part9Program {s with pc := UInt256.ofNat 9701, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn11part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part9Program, productColumn11part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def productColumn11part10Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD]

def productColumn11part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x11 * x13
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  {s with pc := UInt256.ofNat 9721, memory := s.memory, stack := v2 :: x9 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn11part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part10Program {s with pc := UInt256.ofNat 9711, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn11part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part10Program, productColumn11part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def productColumn11part11Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def productColumn11part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x12 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 192
  let v3 : UInt256 := UInt256.mulMod x10 v2 x11
  {s with pc := UInt256.ofNat 9730, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn11part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part11Program {s with pc := UInt256.ofNat 9721, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn11part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part11Program, productColumn11part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def productColumn11part12Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn11part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 0
  let v2 : UInt256 := UInt256.mulMod x4 v1 x10
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 9738, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn11part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part12Program {s with pc := UInt256.ofNat 9730, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn11part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part12Program, productColumn11part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def productColumn11part13Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn11part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 9742, memory := s.memory, stack := x8 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn11part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11part13Program {s with pc := UInt256.ofNat 9738, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn11part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn11part13Program, productColumn11part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def productColumn11Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn11Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word3
  let v2 : UInt256 := UInt256.mulMod carry word0 word1
  let v3 : UInt256 := v2 + word2
  let v4 : UInt256 := MachineState.readWord s.memory 128
  let v5 : UInt256 := MachineState.readWord s.memory 1888
  let v6 : UInt256 := v5 * v4
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.mulMod v5 v4 word11
  let v9 : UInt256 := v8 + v3
  let v10 : UInt256 := MachineState.readWord s.memory 160
  let v11 : UInt256 := MachineState.readWord s.memory 1856
  let v12 : UInt256 := v11 * v10
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := UInt256.mulMod v11 v10 word11
  let v15 : UInt256 := v14 + v9
  let v16 : UInt256 := MachineState.readWord s.memory 1824
  let v17 : UInt256 := v16 * word4
  let v18 : UInt256 := v17 + v13
  let v19 : UInt256 := UInt256.mulMod v16 word4 word11
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := MachineState.readWord s.memory 1088
  let v22 : UInt256 := word12 * v21
  let v23 : UInt256 := v22 + v18
  let v24 : UInt256 := MachineState.readWord s.memory 192
  let v25 : UInt256 := word10 * v24
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := MachineState.readWord s.memory 0
  let v28 : UInt256 := word5 * v27
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord s.memory 224
  let v31 : UInt256 := word9 * v30
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 1216
  let v34 : UInt256 := word6 * v33
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := word16 * word7
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := MachineState.readWord s.memory 1280
  let v39 : UInt256 := v38 * word17
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := word13 * word15
  let v42 : UInt256 := v41 + v40
  let v43 : UInt256 := MachineState.readWord s.memory 1088
  let v44 : UInt256 := UInt256.mulMod word12 v43 word11
  let v45 : UInt256 := v44 + v20
  let v46 : UInt256 := MachineState.readWord s.memory 192
  let v47 : UInt256 := UInt256.mulMod word10 v46 word11
  let v48 : UInt256 := v47 + v45
  let v49 : UInt256 := MachineState.readWord s.memory 0
  let v50 : UInt256 := UInt256.mulMod word5 v49 word11
  let v51 : UInt256 := v50 + v48
  let v52 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 9742, memory := s.memory, stack := word9 :: v52 :: word11 :: v51 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest}

theorem productColumn11_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11Program {s with pc := UInt256.ofNat 9614, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} =
      some (productColumn11Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 rest) := by
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word3
  let v2 : UInt256 := UInt256.mulMod carry word0 word1
  let v3 : UInt256 := v2 + word2
  let v4 : UInt256 := MachineState.readWord s.memory 128
  let v5 : UInt256 := MachineState.readWord s.memory 1888
  let v6 : UInt256 := v5 * v4
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.mulMod v5 v4 word11
  let v9 : UInt256 := v8 + v3
  let v10 : UInt256 := MachineState.readWord s.memory 160
  let v11 : UInt256 := MachineState.readWord s.memory 1856
  let v12 : UInt256 := v11 * v10
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := UInt256.mulMod v11 v10 word11
  let v15 : UInt256 := v14 + v9
  let v16 : UInt256 := MachineState.readWord s.memory 1824
  let v17 : UInt256 := v16 * word4
  let v18 : UInt256 := v17 + v13
  let v19 : UInt256 := UInt256.mulMod v16 word4 word11
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := MachineState.readWord s.memory 1088
  let v22 : UInt256 := word12 * v21
  let v23 : UInt256 := v22 + v18
  let v24 : UInt256 := MachineState.readWord s.memory 192
  let v25 : UInt256 := word10 * v24
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := MachineState.readWord s.memory 0
  let v28 : UInt256 := word5 * v27
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord s.memory 224
  let v31 : UInt256 := word9 * v30
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 1216
  let v34 : UInt256 := word6 * v33
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := word16 * word7
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := MachineState.readWord s.memory 1280
  let v39 : UInt256 := v38 * word17
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := word13 * word15
  let v42 : UInt256 := v41 + v40
  let v43 : UInt256 := MachineState.readWord s.memory 1088
  let v44 : UInt256 := UInt256.mulMod word12 v43 word11
  let v45 : UInt256 := v44 + v20
  let v46 : UInt256 := MachineState.readWord s.memory 192
  let v47 : UInt256 := UInt256.mulMod word10 v46 word11
  let v48 : UInt256 := v47 + v45
  let v49 : UInt256 := MachineState.readWord s.memory 0
  let v50 : UInt256 := UInt256.mulMod word5 v49 word11
  let v51 : UInt256 := v50 + v48
  let v52 : UInt256 := MachineState.readWord s.memory 224
  have h0 : runInstructions productColumn11part0Program {s with pc := UInt256.ofNat 9614, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9622, memory := s.memory, stack := v3 :: v1 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part0Model, v0, v1, v2, v3] using productColumn11part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h1 : runInstructions productColumn11part1Program {s with pc := UInt256.ofNat 9622, memory := s.memory, stack := v3 :: v1 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9633, memory := s.memory, stack := v5 :: v4 :: v1 :: v4 :: word11 :: v3 :: v5 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part1Model, v4, v5] using productColumn11part1_run (s) (v3) (v1) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h2 : runInstructions productColumn11part2Program {s with pc := UInt256.ofNat 9633, memory := s.memory, stack := v5 :: v4 :: v1 :: v4 :: word11 :: v3 :: v5 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9642, memory := s.memory, stack := v10 :: word11 :: v9 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part2Model, v6, v7, v8, v9, v10] using productColumn11part2_run (s) (v5) (v4) (v1) (v4) (word11) (v3) (v5) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h3 : runInstructions productColumn11part3Program {s with pc := UInt256.ofNat 9642, memory := s.memory, stack := v10 :: word11 :: v9 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9652, memory := s.memory, stack := v11 :: v10 :: word11 :: v9 :: v13 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part3Model, v11, v12, v13] using productColumn11part3_run (s) (v10) (word11) (v9) (v7) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h4 : runInstructions productColumn11part4Program {s with pc := UInt256.ofNat 9652, memory := s.memory, stack := v11 :: v10 :: word11 :: v9 :: v13 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9662, memory := s.memory, stack := word4 :: v13 :: word4 :: word11 :: v15 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part4Model, v14, v15, v16] using productColumn11part4_run (s) (v11) (v10) (word11) (v9) (v13) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h5 : runInstructions productColumn11part5Program {s with pc := UInt256.ofNat 9662, memory := s.memory, stack := word4 :: v13 :: word4 :: word11 :: v15 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9673, memory := s.memory, stack := v21 :: v18 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part5Model, v17, v18, v19, v20, v21] using productColumn11part5_run (s) (word4) (v13) (word4) (word11) (v15) (v16) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h6 : runInstructions productColumn11part6Program {s with pc := UInt256.ofNat 9673, memory := s.memory, stack := v21 :: v18 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9682, memory := s.memory, stack := v26 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part6Model, v22, v23, v24, v25, v26] using productColumn11part6_run (s) (v21) (v18) (v20) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h7 : runInstructions productColumn11part7Program {s with pc := UInt256.ofNat 9682, memory := s.memory, stack := v26 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9691, memory := s.memory, stack := word9 :: v30 :: v29 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part7Model, v27, v28, v29, v30] using productColumn11part7_run (s) (v26) (v20) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h8 : runInstructions productColumn11part8Program {s with pc := UInt256.ofNat 9691, memory := s.memory, stack := word9 :: v30 :: v29 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9701, memory := s.memory, stack := word7 :: v35 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part8Model, v31, v32, v33, v34, v35] using productColumn11part8_run (s) (word9) (v30) (v29) (v20) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h9 : runInstructions productColumn11part9Program {s with pc := UInt256.ofNat 9701, memory := s.memory, stack := word7 :: v35 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9711, memory := s.memory, stack := v40 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part9Model, v36, v37, v38, v39, v40] using productColumn11part9_run (s) (word7) (v35) (v20) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h10 : runInstructions productColumn11part10Program {s with pc := UInt256.ofNat 9711, memory := s.memory, stack := v40 :: v20 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9721, memory := s.memory, stack := v43 :: word11 :: v20 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part10Model, v41, v42, v43] using productColumn11part10_run (s) (v40) (v20) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h11 : runInstructions productColumn11part11Program {s with pc := UInt256.ofNat 9721, memory := s.memory, stack := v43 :: word11 :: v20 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9730, memory := s.memory, stack := v47 :: v45 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part11Model, v44, v45, v46, v47] using productColumn11part11_run (s) (v43) (word11) (v20) (v42) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h12 : runInstructions productColumn11part12Program {s with pc := UInt256.ofNat 9730, memory := s.memory, stack := v47 :: v45 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9738, memory := s.memory, stack := word11 :: v51 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part12Model, v48, v49, v50, v51] using productColumn11part12_run (s) (v47) (v45) (v42) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h13 : runInstructions productColumn11part13Program {s with pc := UInt256.ofNat 9738, memory := s.memory, stack := word11 :: v51 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9742, memory := s.memory, stack := word9 :: v52 :: word11 :: v51 :: v42 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn11part13Model, v52] using productColumn11part13_run (s) (word11) (v51) (v42) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution

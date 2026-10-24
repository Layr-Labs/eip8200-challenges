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

def productColumn4part0Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD]

def productColumn4part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x6 x3 x4
  let v3 : UInt256 := v2 + x5
  let v4 : UInt256 := MachineState.readWord s.memory 96
  {s with pc := UInt256.ofNat 8725, memory := s.memory, stack := v4 :: x14 :: v3 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn4part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part0Program {s with pc := UInt256.ofNat 8716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn4part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part0Program, productColumn4part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]


def productColumn4part1Program : List Instr :=
  [.push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn4part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1792
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x3
  {s with pc := UInt256.ofNat 8735, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn4part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part1Program {s with pc := UInt256.ofNat 8725, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn4part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : UInt256).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part1Program, productColumn4part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1792, hf1792]


def productColumn4part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩)]

def productColumn4part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := x13 * x10
  let v3 : UInt256 := v2 + x4
  {s with pc := UInt256.ofNat 8743, memory := s.memory, stack := x7 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn4part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part2Program {s with pc := UInt256.ofNat 8735, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn4part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn4part2Program, productColumn4part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn4part3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def productColumn4part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x9 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 192
  let v3 : UInt256 := v2 * x15
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 8752, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn4part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part3Program {s with pc := UInt256.ofNat 8743, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn4part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part3Program, productColumn4part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def productColumn4part4Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def productColumn4part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := v0 * x2
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 8761, memory := s.memory, stack := v3 :: x11 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn4part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part4Program {s with pc := UInt256.ofNat 8752, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn4part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part4Program, productColumn4part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha224, hf224]


def productColumn4part5Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn4part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x12 x9 x11
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 8769, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn4part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part5Program {s with pc := UInt256.ofNat 8761, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn4part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn4part5Program, productColumn4part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn4part6Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def productColumn4part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x4 x9
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 192
  {s with pc := UInt256.ofNat 8779, memory := s.memory, stack := v2 :: x14 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn4part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part6Program {s with pc := UInt256.ofNat 8769, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn4part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part6Program, productColumn4part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def productColumn4part7Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def productColumn4part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.mulMod v2 x5 x12
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 8787, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn4part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part7Program {s with pc := UInt256.ofNat 8779, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn4part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part7Program, productColumn4part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def productColumn4part8Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def productColumn4part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.mulMod v0 x11 x9
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 8796, memory := s.memory, stack := x13 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn4part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part8Program {s with pc := UInt256.ofNat 8787, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn4part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part8Program, productColumn4part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def productColumn4part9Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def productColumn4part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2720
  let v1 : UInt256 := x3 * v0
  let v2 : UInt256 := UInt256.land x14 v1
  {s with pc := UInt256.ofNat 8806, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn4part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part9Program {s with pc := UInt256.ofNat 8796, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn4part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part9Program, productColumn4part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2720, hf2720]


def productColumn4part10Program : List Instr :=
  [.push 2 1216,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def productColumn4part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1216
  let v1 : UInt256 := UInt256.mulMod x1 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v2 x5
  {s with pc := UInt256.ofNat 8818, memory := v0, stack := x13 :: v3 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn4part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part10Program {s with pc := UInt256.ofNat 8806, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn4part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part10Program, productColumn4part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def productColumn4part11Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn4part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1984
  let v2 : UInt256 := v1 * v0
  {s with pc := UInt256.ofNat 8830, memory := s.memory, stack := v2 :: x2 :: v0 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn4part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part11Program {s with pc := UInt256.ofNat 8818, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn4part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : UInt256).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part11Program, productColumn4part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha1984, hf1984]


def productColumn4part12Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push 2 1952,
   .op .MLOAD]

def productColumn4part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := MachineState.readWord s.memory 1952
  {s with pc := UInt256.ofNat 8840, memory := s.memory, stack := v3 :: x9 :: x13 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn4part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part12Program {s with pc := UInt256.ofNat 8830, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn4part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1952 : (1952 : UInt256).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn4part12Program, productColumn4part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1952, hf1952]


def productColumn4part13Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn4part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  {s with pc := UInt256.ofNat 8844, memory := s.memory, stack := v0 :: x4 :: x1 :: x2 :: x3 :: x0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn4part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4part13Program {s with pc := UInt256.ofNat 8840, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn4part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn4part13Program, productColumn4part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn4Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1792,
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
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 224,
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
   .push 2 1216,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .push 2 1984,
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
   .op (.Dup ⟨6, by decide⟩),
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn4Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := MachineState.readWord s.memory 96
  let v5 : UInt256 := MachineState.readWord s.memory 1792
  let v6 : UInt256 := v5 * v4
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.mulMod v5 v4 word13
  let v9 : UInt256 := v8 + v3
  let v10 : UInt256 := word14 * word11
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := word12 * word8
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := MachineState.readWord s.memory 192
  let v15 : UInt256 := v14 * word18
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := MachineState.readWord s.memory 0
  let v18 : UInt256 := v17 * word6
  let v19 : UInt256 := v18 + v16
  let v20 : UInt256 := MachineState.readWord s.memory 224
  let v21 : UInt256 := v20 * word15
  let v22 : UInt256 := v21 + v19
  let v23 : UInt256 := UInt256.mulMod word14 word11 word13
  let v24 : UInt256 := v23 + v9
  let v25 : UInt256 := UInt256.mulMod word12 word8 word13
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := MachineState.readWord s.memory 192
  let v28 : UInt256 := UInt256.mulMod v27 word18 word13
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord s.memory 0
  let v31 : UInt256 := UInt256.mulMod v30 word6 word13
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 224
  let v34 : UInt256 := UInt256.mulMod v33 word15 word13
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := MachineState.readWord s.memory 2720
  let v37 : UInt256 := v22 * v36
  let v38 : UInt256 := UInt256.land word16 v37
  let v39 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v38.toNat 32) 1216
  let v40 : UInt256 := UInt256.mulMod v38 word17 word13
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v41 word13
  let v43 : UInt256 := MachineState.readWord v39 768
  let v44 : UInt256 := MachineState.readWord v39 1984
  let v45 : UInt256 := v44 * v43
  let v46 : UInt256 := v45 + v42
  let v47 : UInt256 := UInt256.mulMod v44 v43 word13
  let v48 : UInt256 := v47 + v42
  let v49 : UInt256 := MachineState.readWord v39 1952
  let v50 : UInt256 := v49 * word9
  {s with pc := UInt256.ofNat 8844, memory := v39, stack := v50 :: v46 :: word9 :: word13 :: v48 :: v49 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest}

theorem productColumn4_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn4Program {s with pc := UInt256.ofNat 8716, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} =
      some (productColumn4Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 rest) := by
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := MachineState.readWord s.memory 96
  let v5 : UInt256 := MachineState.readWord s.memory 1792
  let v6 : UInt256 := v5 * v4
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.mulMod v5 v4 word13
  let v9 : UInt256 := v8 + v3
  let v10 : UInt256 := word14 * word11
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := word12 * word8
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := MachineState.readWord s.memory 192
  let v15 : UInt256 := v14 * word18
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := MachineState.readWord s.memory 0
  let v18 : UInt256 := v17 * word6
  let v19 : UInt256 := v18 + v16
  let v20 : UInt256 := MachineState.readWord s.memory 224
  let v21 : UInt256 := v20 * word15
  let v22 : UInt256 := v21 + v19
  let v23 : UInt256 := UInt256.mulMod word14 word11 word13
  let v24 : UInt256 := v23 + v9
  let v25 : UInt256 := UInt256.mulMod word12 word8 word13
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := MachineState.readWord s.memory 192
  let v28 : UInt256 := UInt256.mulMod v27 word18 word13
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord s.memory 0
  let v31 : UInt256 := UInt256.mulMod v30 word6 word13
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 224
  let v34 : UInt256 := UInt256.mulMod v33 word15 word13
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := MachineState.readWord s.memory 2720
  let v37 : UInt256 := v22 * v36
  let v38 : UInt256 := UInt256.land word16 v37
  let v39 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v38.toNat 32) 1216
  let v40 : UInt256 := UInt256.mulMod v38 word17 word13
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v41 word13
  let v43 : UInt256 := MachineState.readWord v39 768
  let v44 : UInt256 := MachineState.readWord v39 1984
  let v45 : UInt256 := v44 * v43
  let v46 : UInt256 := v45 + v42
  let v47 : UInt256 := UInt256.mulMod v44 v43 word13
  let v48 : UInt256 := v47 + v42
  let v49 : UInt256 := MachineState.readWord v39 1952
  let v50 : UInt256 := v49 * word9
  have h0 : runInstructions productColumn4part0Program {s with pc := UInt256.ofNat 8716, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8725, memory := s.memory, stack := v4 :: word13 :: v3 :: v1 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part0Model, v0, v1, v2, v3, v4] using productColumn4part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h1 : runInstructions productColumn4part1Program {s with pc := UInt256.ofNat 8725, memory := s.memory, stack := v4 :: word13 :: v3 :: v1 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8735, memory := s.memory, stack := v5 :: v4 :: word13 :: v3 :: v7 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part1Model, v5, v6, v7] using productColumn4part1_run (s) (v4) (word13) (v3) (v1) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h2 : runInstructions productColumn4part2Program {s with pc := UInt256.ofNat 8735, memory := s.memory, stack := v5 :: v4 :: word13 :: v3 :: v7 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8743, memory := s.memory, stack := word8 :: v11 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part2Model, v8, v9, v10, v11] using productColumn4part2_run (s) (v5) (v4) (word13) (v3) (v7) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h3 : runInstructions productColumn4part3Program {s with pc := UInt256.ofNat 8743, memory := s.memory, stack := word8 :: v11 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8752, memory := s.memory, stack := v16 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part3Model, v12, v13, v14, v15, v16] using productColumn4part3_run (s) (word8) (v11) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h4 : runInstructions productColumn4part4Program {s with pc := UInt256.ofNat 8752, memory := s.memory, stack := v16 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8761, memory := s.memory, stack := v20 :: word15 :: v19 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part4Model, v17, v18, v19, v20] using productColumn4part4_run (s) (v16) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h5 : runInstructions productColumn4part5Program {s with pc := UInt256.ofNat 8761, memory := s.memory, stack := v20 :: word15 :: v19 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8769, memory := s.memory, stack := v24 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part5Model, v21, v22, v23, v24] using productColumn4part5_run (s) (v20) (word15) (v19) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h6 : runInstructions productColumn4part6Program {s with pc := UInt256.ofNat 8769, memory := s.memory, stack := v24 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8779, memory := s.memory, stack := v27 :: word18 :: word13 :: v26 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part6Model, v25, v26, v27] using productColumn4part6_run (s) (v24) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h7 : runInstructions productColumn4part7Program {s with pc := UInt256.ofNat 8779, memory := s.memory, stack := v27 :: word18 :: word13 :: v26 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8787, memory := s.memory, stack := v32 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part7Model, v28, v29, v30, v31, v32] using productColumn4part7_run (s) (v27) (word18) (word13) (v26) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h8 : runInstructions productColumn4part8Program {s with pc := UInt256.ofNat 8787, memory := s.memory, stack := v32 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8796, memory := s.memory, stack := word17 :: word13 :: v35 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part8Model, v33, v34, v35] using productColumn4part8_run (s) (v32) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h9 : runInstructions productColumn4part9Program {s with pc := UInt256.ofNat 8796, memory := s.memory, stack := word17 :: word13 :: v35 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8806, memory := s.memory, stack := v38 :: v38 :: word17 :: word13 :: v35 :: word13 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part9Model, v36, v37, v38] using productColumn4part9_run (s) (word17) (word13) (v35) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h10 : runInstructions productColumn4part10Program {s with pc := UInt256.ofNat 8806, memory := s.memory, stack := v38 :: v38 :: word17 :: word13 :: v35 :: word13 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8818, memory := v39, stack := word13 :: v42 :: v42 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part10Model, v39, v40, v41, v42] using productColumn4part10_run (s) (v38) (v38) (word17) (word13) (v35) (word13) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h11 : runInstructions productColumn4part11Program {s with pc := UInt256.ofNat 8818, memory := v39, stack := word13 :: v42 :: v42 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8830, memory := v39, stack := v45 :: v42 :: v43 :: word13 :: v42 :: v44 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part11Model, v43, v44, v45] using productColumn4part11_run ({s with memory := v39}) (word13) (v42) (v42) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h12 : runInstructions productColumn4part12Program {s with pc := UInt256.ofNat 8830, memory := v39, stack := v45 :: v42 :: v43 :: word13 :: v42 :: v44 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8840, memory := v39, stack := v49 :: word9 :: word13 :: v48 :: v46 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part12Model, v46, v47, v48, v49] using productColumn4part12_run ({s with memory := v39}) (v45) (v42) (v43) (word13) (v42) (v44) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h13 : runInstructions productColumn4part13Program {s with pc := UInt256.ofNat 8840, memory := v39, stack := v49 :: word9 :: word13 :: v48 :: v46 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 8844, memory := v39, stack := v50 :: v46 :: word9 :: word13 :: v48 :: v49 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn4part13Model, v50] using productColumn4part13_run ({s with memory := v39}) (v49) (word9) (word13) (v48) (v46) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution

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

def productColumn5part0Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 1920,
   .op .MLOAD]

def productColumn5part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := MachineState.readWord s.memory 1920
  {s with pc := UInt256.ofNat 8854, memory := s.memory, stack := v3 :: x10 :: x13 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn5part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part0Program {s with pc := UInt256.ofNat 8844, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn5part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1920 : (1920 : UInt256).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part0Program, productColumn5part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1920, hf1920]


def productColumn5part1Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn5part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x4
  let v2 : UInt256 := UInt256.mulMod x0 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 8862, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn5part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part1Program {s with pc := UInt256.ofNat 8854, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn5part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn5part1Program, productColumn5part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn5part2Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn5part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := MachineState.readWord s.memory 1888
  {s with pc := UInt256.ofNat 8873, memory := s.memory, stack := v1 :: v0 :: x1 :: v0 :: x9 :: x0 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn5part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part2Program {s with pc := UInt256.ofNat 8862, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn5part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : UInt256).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part2Program, productColumn5part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha1888, hf1888]


def productColumn5part3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD]

def productColumn5part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x6 x3 x4
  let v3 : UInt256 := v2 + x5
  let v4 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 8882, memory := s.memory, stack := v4 :: x14 :: v3 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn5part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part3Program {s with pc := UInt256.ofNat 8873, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn5part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part3Program, productColumn5part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]


def productColumn5part4Program : List Instr :=
  [.push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn5part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1856
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x3
  {s with pc := UInt256.ofNat 8892, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn5part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part4Program {s with pc := UInt256.ofNat 8882, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn5part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : UInt256).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part4Program, productColumn5part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1856, hf1856]


def productColumn5part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn5part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := MachineState.readWord s.memory 1824
  {s with pc := UInt256.ofNat 8903, memory := s.memory, stack := x4 :: v2 :: x12 :: v1 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn5part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part5Program {s with pc := UInt256.ofNat 8892, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn5part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : UInt256).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part5Program, productColumn5part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha1824, hf1824]


def productColumn5part6Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn5part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x4 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 8911, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn5part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part6Program {s with pc := UInt256.ofNat 8903, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn5part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn5part6Program, productColumn5part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn5part7Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn5part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 1792
  let v2 : UInt256 := v1 * v0
  {s with pc := UInt256.ofNat 8922, memory := s.memory, stack := v2 :: x2 :: v0 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn5part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part7Program {s with pc := UInt256.ofNat 8911, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn5part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha1792 : (1792 : UInt256).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part7Program, productColumn5part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha1792, hf1792]


def productColumn5part8Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL]

def productColumn5part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := x14 * x7
  {s with pc := UInt256.ofNat 8930, memory := s.memory, stack := v3 :: v0 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn5part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part8Program {s with pc := UInt256.ofNat 8922, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn5part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn5part8Program, productColumn5part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn5part9Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def productColumn5part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x9 * x8
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := MachineState.readWord s.memory 192
  {s with pc := UInt256.ofNat 8939, memory := s.memory, stack := v3 :: x5 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn5part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part9Program {s with pc := UInt256.ofNat 8930, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn5part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part9Program, productColumn5part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def productColumn5part10Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def productColumn5part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := v2 * x16
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 8947, memory := s.memory, stack := x4 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn5part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part10Program {s with pc := UInt256.ofNat 8939, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn5part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part10Program, productColumn5part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def productColumn5part11Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL]

def productColumn5part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 1216
  let v4 : UInt256 := v3 * x12
  {s with pc := UInt256.ofNat 8958, memory := s.memory, stack := v4 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn5part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part11Program {s with pc := UInt256.ofNat 8947, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn5part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn5part11Program, productColumn5part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224, ha1216, hf1216]


def productColumn5part12Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn5part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x11 x4 x10
  let v2 : UInt256 := v1 + x2
  {s with pc := UInt256.ofNat 8966, memory := s.memory, stack := x10 :: v2 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn5part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part12Program {s with pc := UInt256.ofNat 8958, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn5part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn5part12Program, productColumn5part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn5part13Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn5part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x9 x8 x0
  let v1 : UInt256 := v0 + x1
  {s with pc := UInt256.ofNat 8972, memory := s.memory, stack := x5 :: x10 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn5part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5part13Program {s with pc := UInt256.ofNat 8966, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn5part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn5part13Program, productColumn5part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn5Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 1920,
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
   .push 1 32,
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
   .push 1 64,
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
   .push 1 96,
   .op .MLOAD,
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
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
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
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn5Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := UInt256.mulMod word4 word1 word2
  let v2 : UInt256 := v1 + word3
  let v3 : UInt256 := MachineState.readWord s.memory 1920
  let v4 : UInt256 := v3 * word9
  let v5 : UInt256 := v4 + v0
  let v6 : UInt256 := UInt256.mulMod v3 word9 word12
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 32
  let v9 : UInt256 := MachineState.readWord s.memory 1888
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v5
  let v12 : UInt256 := UInt256.mulMod v9 v8 word12
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := MachineState.readWord s.memory 64
  let v15 : UInt256 := MachineState.readWord s.memory 1856
  let v16 : UInt256 := v15 * v14
  let v17 : UInt256 := v16 + v11
  let v18 : UInt256 := UInt256.mulMod v15 v14 word12
  let v19 : UInt256 := v18 + v13
  let v20 : UInt256 := MachineState.readWord s.memory 96
  let v21 : UInt256 := MachineState.readWord s.memory 1824
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v17
  let v24 : UInt256 := UInt256.mulMod v21 v20 word12
  let v25 : UInt256 := v24 + v19
  let v26 : UInt256 := MachineState.readWord s.memory 128
  let v27 : UInt256 := MachineState.readWord s.memory 1792
  let v28 : UInt256 := v27 * v26
  let v29 : UInt256 := v28 + v23
  let v30 : UInt256 := UInt256.mulMod v27 v26 word12
  let v31 : UInt256 := v30 + v25
  let v32 : UInt256 := word13 * word6
  let v33 : UInt256 := v32 + v29
  let v34 : UInt256 := word11 * word10
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := MachineState.readWord s.memory 192
  let v37 : UInt256 := v36 * word7
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := MachineState.readWord s.memory 0
  let v40 : UInt256 := v39 * word17
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := MachineState.readWord s.memory 224
  let v43 : UInt256 := v42 * word5
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := MachineState.readWord s.memory 1216
  let v46 : UInt256 := v45 * word14
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := UInt256.mulMod word13 word6 word12
  let v49 : UInt256 := v48 + v31
  let v50 : UInt256 := UInt256.mulMod word11 word10 word12
  let v51 : UInt256 := v50 + v49
  {s with pc := UInt256.ofNat 8972, memory := s.memory, stack := word7 :: word12 :: v51 :: v47 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest}

theorem productColumn5_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn5Program {s with pc := UInt256.ofNat 8844, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} =
      some (productColumn5Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 rest) := by
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := UInt256.mulMod word4 word1 word2
  let v2 : UInt256 := v1 + word3
  let v3 : UInt256 := MachineState.readWord s.memory 1920
  let v4 : UInt256 := v3 * word9
  let v5 : UInt256 := v4 + v0
  let v6 : UInt256 := UInt256.mulMod v3 word9 word12
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 32
  let v9 : UInt256 := MachineState.readWord s.memory 1888
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v5
  let v12 : UInt256 := UInt256.mulMod v9 v8 word12
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := MachineState.readWord s.memory 64
  let v15 : UInt256 := MachineState.readWord s.memory 1856
  let v16 : UInt256 := v15 * v14
  let v17 : UInt256 := v16 + v11
  let v18 : UInt256 := UInt256.mulMod v15 v14 word12
  let v19 : UInt256 := v18 + v13
  let v20 : UInt256 := MachineState.readWord s.memory 96
  let v21 : UInt256 := MachineState.readWord s.memory 1824
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v17
  let v24 : UInt256 := UInt256.mulMod v21 v20 word12
  let v25 : UInt256 := v24 + v19
  let v26 : UInt256 := MachineState.readWord s.memory 128
  let v27 : UInt256 := MachineState.readWord s.memory 1792
  let v28 : UInt256 := v27 * v26
  let v29 : UInt256 := v28 + v23
  let v30 : UInt256 := UInt256.mulMod v27 v26 word12
  let v31 : UInt256 := v30 + v25
  let v32 : UInt256 := word13 * word6
  let v33 : UInt256 := v32 + v29
  let v34 : UInt256 := word11 * word10
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := MachineState.readWord s.memory 192
  let v37 : UInt256 := v36 * word7
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := MachineState.readWord s.memory 0
  let v40 : UInt256 := v39 * word17
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := MachineState.readWord s.memory 224
  let v43 : UInt256 := v42 * word5
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := MachineState.readWord s.memory 1216
  let v46 : UInt256 := v45 * word14
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := UInt256.mulMod word13 word6 word12
  let v49 : UInt256 := v48 + v31
  let v50 : UInt256 := UInt256.mulMod word11 word10 word12
  let v51 : UInt256 := v50 + v49
  have h0 : runInstructions productColumn5part0Program {s with pc := UInt256.ofNat 8844, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8854, memory := s.memory, stack := v3 :: word9 :: word12 :: v2 :: v0 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part0Model, v0, v1, v2, v3] using productColumn5part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h1 : runInstructions productColumn5part1Program {s with pc := UInt256.ofNat 8854, memory := s.memory, stack := v3 :: word9 :: word12 :: v2 :: v0 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8862, memory := s.memory, stack := v7 :: v5 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part1Model, v4, v5, v6, v7] using productColumn5part1_run (s) (v3) (word9) (word12) (v2) (v0) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h2 : runInstructions productColumn5part2Program {s with pc := UInt256.ofNat 8862, memory := s.memory, stack := v7 :: v5 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8873, memory := s.memory, stack := v9 :: v8 :: v5 :: v8 :: word12 :: v7 :: v9 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part2Model, v8, v9] using productColumn5part2_run (s) (v7) (v5) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h3 : runInstructions productColumn5part3Program {s with pc := UInt256.ofNat 8873, memory := s.memory, stack := v9 :: v8 :: v5 :: v8 :: word12 :: v7 :: v9 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8882, memory := s.memory, stack := v14 :: word12 :: v13 :: v11 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part3Model, v10, v11, v12, v13, v14] using productColumn5part3_run (s) (v9) (v8) (v5) (v8) (word12) (v7) (v9) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h4 : runInstructions productColumn5part4Program {s with pc := UInt256.ofNat 8882, memory := s.memory, stack := v14 :: word12 :: v13 :: v11 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8892, memory := s.memory, stack := v15 :: v14 :: word12 :: v13 :: v17 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part4Model, v15, v16, v17] using productColumn5part4_run (s) (v14) (word12) (v13) (v11) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h5 : runInstructions productColumn5part5Program {s with pc := UInt256.ofNat 8892, memory := s.memory, stack := v15 :: v14 :: word12 :: v13 :: v17 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8903, memory := s.memory, stack := v17 :: v20 :: word12 :: v19 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part5Model, v18, v19, v20, v21] using productColumn5part5_run (s) (v15) (v14) (word12) (v13) (v17) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h6 : runInstructions productColumn5part6Program {s with pc := UInt256.ofNat 8903, memory := s.memory, stack := v17 :: v20 :: word12 :: v19 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8911, memory := s.memory, stack := word12 :: v25 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part6Model, v22, v23, v24, v25] using productColumn5part6_run (s) (v17) (v20) (word12) (v19) (v21) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h7 : runInstructions productColumn5part7Program {s with pc := UInt256.ofNat 8911, memory := s.memory, stack := word12 :: v25 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8922, memory := s.memory, stack := v28 :: v23 :: v26 :: word12 :: v25 :: v27 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part7Model, v26, v27, v28] using productColumn5part7_run (s) (word12) (v25) (v23) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h8 : runInstructions productColumn5part8Program {s with pc := UInt256.ofNat 8922, memory := s.memory, stack := v28 :: v23 :: v26 :: word12 :: v25 :: v27 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8930, memory := s.memory, stack := v32 :: v29 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part8Model, v29, v30, v31, v32] using productColumn5part8_run (s) (v28) (v23) (v26) (word12) (v25) (v27) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h9 : runInstructions productColumn5part9Program {s with pc := UInt256.ofNat 8930, memory := s.memory, stack := v32 :: v29 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8939, memory := s.memory, stack := v36 :: word7 :: v35 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part9Model, v33, v34, v35, v36] using productColumn5part9_run (s) (v32) (v29) (v31) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h10 : runInstructions productColumn5part10Program {s with pc := UInt256.ofNat 8939, memory := s.memory, stack := v36 :: word7 :: v35 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8947, memory := s.memory, stack := word5 :: v41 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part10Model, v37, v38, v39, v40, v41] using productColumn5part10_run (s) (v36) (word7) (v35) (v31) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h11 : runInstructions productColumn5part11Program {s with pc := UInt256.ofNat 8947, memory := s.memory, stack := word5 :: v41 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8958, memory := s.memory, stack := v46 :: v44 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part11Model, v42, v43, v44, v45, v46] using productColumn5part11_run (s) (word5) (v41) (v31) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h12 : runInstructions productColumn5part12Program {s with pc := UInt256.ofNat 8958, memory := s.memory, stack := v46 :: v44 :: v31 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8966, memory := s.memory, stack := word12 :: v49 :: v47 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part12Model, v47, v48, v49] using productColumn5part12_run (s) (v46) (v44) (v31) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h13 : runInstructions productColumn5part13Program {s with pc := UInt256.ofNat 8966, memory := s.memory, stack := word12 :: v49 :: v47 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8972, memory := s.memory, stack := word7 :: word12 :: v51 :: v47 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn5part13Model, v50, v51] using productColumn5part13_run (s) (word12) (v49) (v47) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution

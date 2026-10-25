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

def productColumn9part0Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def productColumn9part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x5 x2 x3
  let v3 : UInt256 := v2 + x4
  let v4 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 8908, memory := s.memory, stack := v4 :: x13 :: v3 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn9part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part0Program {s with pc := UInt256.ofNat 8898, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn9part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part0Program, productColumn9part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def productColumn9part1Program : List Instr :=
  [.push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn9part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1856
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x3
  {s with pc := UInt256.ofNat 8918, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn9part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part1Program {s with pc := UInt256.ofNat 8908, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn9part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : UInt256).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part1Program, productColumn9part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1856, hf1856]


def productColumn9part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn9part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := MachineState.readWord s.memory 1824
  {s with pc := UInt256.ofNat 8929, memory := s.memory, stack := x4 :: v2 :: x12 :: v1 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn9part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part2Program {s with pc := UInt256.ofNat 8918, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn9part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : UInt256).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part2Program, productColumn9part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160, ha1824, hf1824]


def productColumn9part3Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn9part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x4 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 8937, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn9part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part3Program {s with pc := UInt256.ofNat 8929, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn9part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn9part3Program, productColumn9part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn9part4Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn9part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1792
  let v1 : UInt256 := v0 * x3
  let v2 : UInt256 := v1 + x2
  {s with pc := UInt256.ofNat 8947, memory := s.memory, stack := v2 :: x3 :: x0 :: x1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn9part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part4Program {s with pc := UInt256.ofNat 8937, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn9part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : UInt256).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part4Program, productColumn9part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1792, hf1792]


def productColumn9part5Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def productColumn9part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 1600
  {s with pc := UInt256.ofNat 8957, memory := s.memory, stack := v2 :: x13 :: x0 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: v2 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn9part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part5Program {s with pc := UInt256.ofNat 8947, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn9part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1600 : (1600 : UInt256).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part5Program, productColumn9part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1600, hf1600]


def productColumn9part6Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL]

def productColumn9part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x11
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := x0 * x1
  {s with pc := UInt256.ofNat 8965, memory := s.memory, stack := v2 :: x2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn9part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part6Program {s with pc := UInt256.ofNat 8957, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn9part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn9part6Program, productColumn9part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn9part7Program : List Instr :=
  [.op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD]

def productColumn9part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1088
  let v2 : UInt256 := x9 * v1
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := MachineState.readWord s.memory 192
  {s with pc := UInt256.ofNat 8976, memory := s.memory, stack := v4 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn9part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part7Program {s with pc := UInt256.ofNat 8965, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn9part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part7Program, productColumn9part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192, ha1088, hf1088]


def productColumn9part8Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn9part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := x8 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 8984, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn9part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part8Program {s with pc := UInt256.ofNat 8976, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn9part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part8Program, productColumn9part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def productColumn9part9Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨15, by decide⟩)]

def productColumn9part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := x4 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 8995, memory := s.memory, stack := x14 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn9part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part9Program {s with pc := UInt256.ofNat 8984, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn9part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part9Program, productColumn9part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224, ha1216, hf1216]


def productColumn9part10Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 1280,
   .op .MLOAD]

def productColumn9part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1248
  let v3 : UInt256 := v2 * x17
  let v4 : UInt256 := v3 + v1
  let v5 : UInt256 := MachineState.readWord s.memory 1280
  {s with pc := UInt256.ofNat 9008, memory := s.memory, stack := v5 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn9part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part10Program {s with pc := UInt256.ofNat 8995, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn9part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part10Program, productColumn9part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248, ha1280, hf1280]


def productColumn9part11Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

def productColumn9part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x12 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  {s with pc := UInt256.ofNat 9018, memory := s.memory, stack := x9 :: v2 :: x10 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn9part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part11Program {s with pc := UInt256.ofNat 9008, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn9part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part11Program, productColumn9part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def productColumn9part12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD]

def productColumn9part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 192
  let v3 : UInt256 := UInt256.mulMod x6 v2 x12
  {s with pc := UInt256.ofNat 9026, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn9part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9part12Program {s with pc := UInt256.ofNat 9018, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn9part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn9part12Program, productColumn9part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def productColumn9Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
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
   .push 1 160,
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
   .op (.Dup ⟨3, by decide⟩),
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
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD]

def productColumn9Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := word4 * carry
  let v1 : UInt256 := v0 + word0
  let v2 : UInt256 := UInt256.mulMod word4 word1 word2
  let v3 : UInt256 := v2 + word3
  let v4 : UInt256 := MachineState.readWord s.memory 128
  let v5 : UInt256 := MachineState.readWord s.memory 1856
  let v6 : UInt256 := v5 * v4
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.mulMod v5 v4 word12
  let v9 : UInt256 := v8 + v3
  let v10 : UInt256 := MachineState.readWord s.memory 160
  let v11 : UInt256 := MachineState.readWord s.memory 1824
  let v12 : UInt256 := v11 * v10
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := UInt256.mulMod v11 v10 word12
  let v15 : UInt256 := v14 + v9
  let v16 : UInt256 := MachineState.readWord s.memory 1792
  let v17 : UInt256 := v16 * word5
  let v18 : UInt256 := v17 + v13
  let v19 : UInt256 := UInt256.mulMod v16 word5 word12
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := MachineState.readWord s.memory 1600
  let v22 : UInt256 := UInt256.mulMod v21 word13 word12
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := v21 * word13
  let v25 : UInt256 := v24 + v18
  let v26 : UInt256 := MachineState.readWord s.memory 1088
  let v27 : UInt256 := word11 * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 192
  let v30 : UInt256 := word6 * v29
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := MachineState.readWord s.memory 0
  let v33 : UInt256 := word10 * v32
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 224
  let v36 : UInt256 := word7 * v35
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := MachineState.readWord s.memory 1216
  let v39 : UInt256 := word17 * v38
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := MachineState.readWord s.memory 1248
  let v42 : UInt256 := v41 * word18
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := MachineState.readWord s.memory 1280
  let v45 : UInt256 := word14 * v44
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := MachineState.readWord s.memory 1088
  let v48 : UInt256 := UInt256.mulMod word11 v47 word12
  let v49 : UInt256 := v48 + v23
  let v50 : UInt256 := MachineState.readWord s.memory 192
  let v51 : UInt256 := UInt256.mulMod word6 v50 word12
  {s with pc := UInt256.ofNat 9026, memory := s.memory, stack := v51 :: v49 :: v46 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest}

theorem productColumn9_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9Program {s with pc := UInt256.ofNat 8898, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} =
      some (productColumn9Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 rest) := by
  let v0 : UInt256 := word4 * carry
  let v1 : UInt256 := v0 + word0
  let v2 : UInt256 := UInt256.mulMod word4 word1 word2
  let v3 : UInt256 := v2 + word3
  let v4 : UInt256 := MachineState.readWord s.memory 128
  let v5 : UInt256 := MachineState.readWord s.memory 1856
  let v6 : UInt256 := v5 * v4
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.mulMod v5 v4 word12
  let v9 : UInt256 := v8 + v3
  let v10 : UInt256 := MachineState.readWord s.memory 160
  let v11 : UInt256 := MachineState.readWord s.memory 1824
  let v12 : UInt256 := v11 * v10
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := UInt256.mulMod v11 v10 word12
  let v15 : UInt256 := v14 + v9
  let v16 : UInt256 := MachineState.readWord s.memory 1792
  let v17 : UInt256 := v16 * word5
  let v18 : UInt256 := v17 + v13
  let v19 : UInt256 := UInt256.mulMod v16 word5 word12
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := MachineState.readWord s.memory 1600
  let v22 : UInt256 := UInt256.mulMod v21 word13 word12
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := v21 * word13
  let v25 : UInt256 := v24 + v18
  let v26 : UInt256 := MachineState.readWord s.memory 1088
  let v27 : UInt256 := word11 * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 192
  let v30 : UInt256 := word6 * v29
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := MachineState.readWord s.memory 0
  let v33 : UInt256 := word10 * v32
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 224
  let v36 : UInt256 := word7 * v35
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := MachineState.readWord s.memory 1216
  let v39 : UInt256 := word17 * v38
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := MachineState.readWord s.memory 1248
  let v42 : UInt256 := v41 * word18
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := MachineState.readWord s.memory 1280
  let v45 : UInt256 := word14 * v44
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := MachineState.readWord s.memory 1088
  let v48 : UInt256 := UInt256.mulMod word11 v47 word12
  let v49 : UInt256 := v48 + v23
  let v50 : UInt256 := MachineState.readWord s.memory 192
  let v51 : UInt256 := UInt256.mulMod word6 v50 word12
  have h0 : runInstructions productColumn9part0Program {s with pc := UInt256.ofNat 8898, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8908, memory := s.memory, stack := v4 :: word12 :: v3 :: v1 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part0Model, v0, v1, v2, v3, v4] using productColumn9part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h1 : runInstructions productColumn9part1Program {s with pc := UInt256.ofNat 8908, memory := s.memory, stack := v4 :: word12 :: v3 :: v1 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8918, memory := s.memory, stack := v5 :: v4 :: word12 :: v3 :: v7 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part1Model, v5, v6, v7] using productColumn9part1_run (s) (v4) (word12) (v3) (v1) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h2 : runInstructions productColumn9part2Program {s with pc := UInt256.ofNat 8918, memory := s.memory, stack := v5 :: v4 :: word12 :: v3 :: v7 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8929, memory := s.memory, stack := v7 :: v10 :: word12 :: v9 :: v11 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part2Model, v8, v9, v10, v11] using productColumn9part2_run (s) (v5) (v4) (word12) (v3) (v7) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h3 : runInstructions productColumn9part3Program {s with pc := UInt256.ofNat 8929, memory := s.memory, stack := v7 :: v10 :: word12 :: v9 :: v11 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8937, memory := s.memory, stack := word12 :: v15 :: v13 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part3Model, v12, v13, v14, v15] using productColumn9part3_run (s) (v7) (v10) (word12) (v9) (v11) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h4 : runInstructions productColumn9part4Program {s with pc := UInt256.ofNat 8937, memory := s.memory, stack := word12 :: v15 :: v13 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8947, memory := s.memory, stack := v18 :: word5 :: word12 :: v15 :: v16 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part4Model, v16, v17, v18] using productColumn9part4_run (s) (word12) (v15) (v13) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h5 : runInstructions productColumn9part5Program {s with pc := UInt256.ofNat 8947, memory := s.memory, stack := v18 :: word5 :: word12 :: v15 :: v16 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8957, memory := s.memory, stack := v21 :: word13 :: v18 :: v20 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part5Model, v19, v20, v21] using productColumn9part5_run (s) (v18) (word5) (word12) (v15) (v16) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h6 : runInstructions productColumn9part6Program {s with pc := UInt256.ofNat 8957, memory := s.memory, stack := v21 :: word13 :: v18 :: v20 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8965, memory := s.memory, stack := v24 :: v18 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part6Model, v22, v23, v24] using productColumn9part6_run (s) (v21) (word13) (v18) (v20) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v21) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h7 : runInstructions productColumn9part7Program {s with pc := UInt256.ofNat 8965, memory := s.memory, stack := v24 :: v18 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8976, memory := s.memory, stack := v29 :: v28 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part7Model, v25, v26, v27, v28, v29] using productColumn9part7_run (s) (v24) (v18) (v23) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v21) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h8 : runInstructions productColumn9part8Program {s with pc := UInt256.ofNat 8976, memory := s.memory, stack := v29 :: v28 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8984, memory := s.memory, stack := v34 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part8Model, v30, v31, v32, v33, v34] using productColumn9part8_run (s) (v29) (v28) (v23) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v21) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h9 : runInstructions productColumn9part9Program {s with pc := UInt256.ofNat 8984, memory := s.memory, stack := v34 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 8995, memory := s.memory, stack := word17 :: v38 :: v37 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part9Model, v35, v36, v37, v38] using productColumn9part9_run (s) (v34) (v23) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v21) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h10 : runInstructions productColumn9part10Program {s with pc := UInt256.ofNat 8995, memory := s.memory, stack := word17 :: v38 :: v37 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9008, memory := s.memory, stack := v44 :: v43 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part10Model, v39, v40, v41, v42, v43, v44] using productColumn9part10_run (s) (word17) (v38) (v37) (v23) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v21) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h11 : runInstructions productColumn9part11Program {s with pc := UInt256.ofNat 9008, memory := s.memory, stack := v44 :: v43 :: v23 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9018, memory := s.memory, stack := word11 :: v47 :: word12 :: v23 :: v46 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part11Model, v45, v46, v47] using productColumn9part11_run (s) (v44) (v43) (v23) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v21) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h12 : runInstructions productColumn9part12Program {s with pc := UInt256.ofNat 9018, memory := s.memory, stack := word11 :: v47 :: word12 :: v23 :: v46 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9026, memory := s.memory, stack := v51 :: v49 :: v46 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v21 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn9part12Model, v48, v49, v50, v51] using productColumn9part12_run (s) (word11) (v47) (word12) (v23) (v46) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v21) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution

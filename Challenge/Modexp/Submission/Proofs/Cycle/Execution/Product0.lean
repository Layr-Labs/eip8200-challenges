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

def productColumn0part0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .push 2 1792,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def productColumn0part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1792
  let v2 : UInt256 := v0 * v1
  {s with pc := UInt256.ofNat 7756, memory := s.memory, stack := v2 :: v1 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem productColumn0part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part0Program {s with pc := UInt256.ofNat 7744, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (productColumn0part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1792 : (1792 : UInt256).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn0part0Program, productColumn0part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha1792, hf1792]


def productColumn0part1Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨14, by decide⟩),
   .op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩)]

def productColumn0part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2720
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := UInt256.land x14 v1
  {s with pc := UInt256.ofNat 7766, memory := s.memory, stack := x11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v2 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn0part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part1Program {s with pc := UInt256.ofNat 7756, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn0part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn0part1Program, productColumn0part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2720, hf2720]


def productColumn0part2Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]

def productColumn0part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x1 x2
  let v1 : UInt256 := UInt256.mulMod x15 x12 x0
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7776, memory := s.memory, stack := (UInt256.ofNat 2048) :: v2 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn0part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part2Program {s with pc := UInt256.ofNat 7766, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn0part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn0part2Program, productColumn0part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn0part3Program : List Instr :=
  [.op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn0part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := MachineState.readWord s.memory 1824
  {s with pc := UInt256.ofNat 7788, memory := s.memory, stack := v0 :: v1 :: x10 :: v0 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn0part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part3Program {s with pc := UInt256.ofNat 7776, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn0part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : UInt256).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn0part3Program, productColumn0part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha1824, hf1824]


def productColumn0part4Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn0part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x4 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 7796, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn0part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part4Program {s with pc := UInt256.ofNat 7788, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn0part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn0part4Program, productColumn0part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn0part5Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn0part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1792
  let v1 : UInt256 := v0 * x6
  let v2 : UInt256 := v1 + x2
  {s with pc := UInt256.ofNat 7806, memory := s.memory, stack := v2 :: x6 :: x0 :: x1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn0part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part5Program {s with pc := UInt256.ofNat 7796, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn0part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : UInt256).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn0part5Program, productColumn0part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1792, hf1792]


def productColumn0part6Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn0part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := x13 * x14
  let v3 : UInt256 := v2 + x0
  {s with pc := UInt256.ofNat 7814, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn0part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part6Program {s with pc := UInt256.ofNat 7806, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn0part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn0part6Program, productColumn0part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn0part7Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def productColumn0part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x11 x9
  let v1 : UInt256 := v0 + x1
  {s with pc := UInt256.ofNat 7822, memory := s.memory, stack := x13 :: x9 :: v1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn0part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part7Program {s with pc := UInt256.ofNat 7814, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn0part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn0part7Program, productColumn0part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn0part8Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def productColumn0part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2720
  let v1 : UInt256 := x3 * v0
  let v2 : UInt256 := UInt256.land x14 v1
  {s with pc := UInt256.ofNat 7832, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn0part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part8Program {s with pc := UInt256.ofNat 7822, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn0part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn0part8Program, productColumn0part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2720, hf2720]


def productColumn0part9Program : List Instr :=
  [.op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def productColumn0part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x1 x2 x3
  let v1 : UInt256 := v0 + x4
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x5
  {s with pc := UInt256.ofNat 7842, memory := s.memory, stack := x13 :: v2 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x0 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn0part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part9Program {s with pc := UInt256.ofNat 7832, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn0part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn0part9Program, productColumn0part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn0part10Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn0part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1856
  let v2 : UInt256 := v1 * v0
  {s with pc := UInt256.ofNat 7854, memory := s.memory, stack := v2 :: x2 :: v0 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn0part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part10Program {s with pc := UInt256.ofNat 7842, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn0part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1856 : (1856 : UInt256).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn0part10Program, productColumn0part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha1856, hf1856]


def productColumn0part11Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push 2 1824,
   .op .MLOAD]

def productColumn0part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := MachineState.readWord s.memory 1824
  {s with pc := UInt256.ofNat 7864, memory := s.memory, stack := v3 :: x9 :: x13 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn0part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part11Program {s with pc := UInt256.ofNat 7854, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn0part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1824 : (1824 : UInt256).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn0part11Program, productColumn0part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1824, hf1824]


def productColumn0part12Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn0part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x4
  let v2 : UInt256 := UInt256.mulMod x0 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 7872, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn0part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0part12Program {s with pc := UInt256.ofNat 7864, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn0part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn0part12Program, productColumn0part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .push 2 1792,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨14, by decide⟩),
   .op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
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
   .op (.Dup ⟨6, by decide⟩),
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
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
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
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
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
   .op (.Dup ⟨6, by decide⟩),
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn0Model (s : State) (word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1792
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := UInt256.land word10 v4
  let v6 : UInt256 := UInt256.mulMod v0 v1 word7
  let v7 : UInt256 := UInt256.mulMod word11 v5 word7
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v8 word7
  let v10 : UInt256 := MachineState.readWord s.memory 768
  let v11 : UInt256 := MachineState.readWord s.memory 1824
  let v12 : UInt256 := v11 * v10
  let v13 : UInt256 := v12 + v9
  let v14 : UInt256 := UInt256.mulMod v11 v10 word7
  let v15 : UInt256 := v14 + v9
  let v16 : UInt256 := MachineState.readWord s.memory 1792
  let v17 : UInt256 := v16 * word3
  let v18 : UInt256 := v17 + v13
  let v19 : UInt256 := UInt256.mulMod v16 word3 word7
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := v5 * word9
  let v22 : UInt256 := v21 + v18
  let v23 : UInt256 := UInt256.mulMod v5 word9 word7
  let v24 : UInt256 := v23 + v20
  let v25 : UInt256 := MachineState.readWord s.memory 2720
  let v26 : UInt256 := v22 * v25
  let v27 : UInt256 := UInt256.land word10 v26
  let v28 : UInt256 := UInt256.mulMod v27 word11 word7
  let v29 : UInt256 := v28 + v24
  let v30 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v29 word7
  let v31 : UInt256 := MachineState.readWord s.memory 768
  let v32 : UInt256 := MachineState.readWord s.memory 1856
  let v33 : UInt256 := v32 * v31
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := UInt256.mulMod v32 v31 word7
  let v36 : UInt256 := v35 + v30
  let v37 : UInt256 := MachineState.readWord s.memory 1824
  let v38 : UInt256 := v37 * word3
  let v39 : UInt256 := v38 + v34
  let v40 : UInt256 := UInt256.mulMod v37 word3 word7
  let v41 : UInt256 := v40 + v36
  {s with pc := UInt256.ofNat 7872, memory := s.memory, stack := v41 :: v39 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest}

theorem productColumn0_run (s : State) (word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0Program {s with pc := UInt256.ofNat 7744, stack := word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} =
      some (productColumn0Model s word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := MachineState.readWord s.memory 1792
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := UInt256.land word10 v4
  let v6 : UInt256 := UInt256.mulMod v0 v1 word7
  let v7 : UInt256 := UInt256.mulMod word11 v5 word7
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v8 word7
  let v10 : UInt256 := MachineState.readWord s.memory 768
  let v11 : UInt256 := MachineState.readWord s.memory 1824
  let v12 : UInt256 := v11 * v10
  let v13 : UInt256 := v12 + v9
  let v14 : UInt256 := UInt256.mulMod v11 v10 word7
  let v15 : UInt256 := v14 + v9
  let v16 : UInt256 := MachineState.readWord s.memory 1792
  let v17 : UInt256 := v16 * word3
  let v18 : UInt256 := v17 + v13
  let v19 : UInt256 := UInt256.mulMod v16 word3 word7
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := v5 * word9
  let v22 : UInt256 := v21 + v18
  let v23 : UInt256 := UInt256.mulMod v5 word9 word7
  let v24 : UInt256 := v23 + v20
  let v25 : UInt256 := MachineState.readWord s.memory 2720
  let v26 : UInt256 := v22 * v25
  let v27 : UInt256 := UInt256.land word10 v26
  let v28 : UInt256 := UInt256.mulMod v27 word11 word7
  let v29 : UInt256 := v28 + v24
  let v30 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v29 word7
  let v31 : UInt256 := MachineState.readWord s.memory 768
  let v32 : UInt256 := MachineState.readWord s.memory 1856
  let v33 : UInt256 := v32 * v31
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := UInt256.mulMod v32 v31 word7
  let v36 : UInt256 := v35 + v30
  let v37 : UInt256 := MachineState.readWord s.memory 1824
  let v38 : UInt256 := v37 * word3
  let v39 : UInt256 := v38 + v34
  let v40 : UInt256 := UInt256.mulMod v37 word3 word7
  let v41 : UInt256 := v40 + v36
  have h0 : runInstructions productColumn0part0Program {s with pc := UInt256.ofNat 7744, memory := s.memory, stack := word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7756, memory := s.memory, stack := v2 :: v1 :: word7 :: v0 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part0Model, v0, v1, v2] using productColumn0part0_run (s) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h1 : runInstructions productColumn0part1Program {s with pc := UInt256.ofNat 7756, memory := s.memory, stack := v2 :: v1 :: word7 :: v0 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7766, memory := s.memory, stack := word7 :: v1 :: word7 :: v0 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part1Model, v3, v4, v5] using productColumn0part1_run (s) (v2) (v1) (word7) (v0) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h2 : runInstructions productColumn0part2Program {s with pc := UInt256.ofNat 7766, memory := s.memory, stack := word7 :: v1 :: word7 :: v0 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7776, memory := s.memory, stack := (UInt256.ofNat 2048) :: v8 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part2Model, v6, v7, v8] using productColumn0part2_run (s) (word7) (v1) (word7) (v0) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h3 : runInstructions productColumn0part3Program {s with pc := UInt256.ofNat 7776, memory := s.memory, stack := (UInt256.ofNat 2048) :: v8 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7788, memory := s.memory, stack := v9 :: v10 :: word7 :: v9 :: v11 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part3Model, v9, v10, v11] using productColumn0part3_run (s) ((UInt256.ofNat 2048)) (v8) (word7) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h4 : runInstructions productColumn0part4Program {s with pc := UInt256.ofNat 7788, memory := s.memory, stack := v9 :: v10 :: word7 :: v9 :: v11 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7796, memory := s.memory, stack := word7 :: v15 :: v13 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part4Model, v12, v13, v14, v15] using productColumn0part4_run (s) (v9) (v10) (word7) (v9) (v11) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h5 : runInstructions productColumn0part5Program {s with pc := UInt256.ofNat 7796, memory := s.memory, stack := word7 :: v15 :: v13 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7806, memory := s.memory, stack := v18 :: word3 :: word7 :: v15 :: v16 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part5Model, v16, v17, v18] using productColumn0part5_run (s) (word7) (v15) (v13) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h6 : runInstructions productColumn0part6Program {s with pc := UInt256.ofNat 7806, memory := s.memory, stack := v18 :: word3 :: word7 :: v15 :: v16 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7814, memory := s.memory, stack := v22 :: v20 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part6Model, v19, v20, v21, v22] using productColumn0part6_run (s) (v18) (word3) (word7) (v15) (v16) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h7 : runInstructions productColumn0part7Program {s with pc := UInt256.ofNat 7814, memory := s.memory, stack := v22 :: v20 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7822, memory := s.memory, stack := word11 :: word7 :: v24 :: v22 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part7Model, v23, v24] using productColumn0part7_run (s) (v22) (v20) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h8 : runInstructions productColumn0part8Program {s with pc := UInt256.ofNat 7822, memory := s.memory, stack := word11 :: word7 :: v24 :: v22 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7832, memory := s.memory, stack := v27 :: v27 :: word11 :: word7 :: v24 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part8Model, v25, v26, v27] using productColumn0part8_run (s) (word11) (word7) (v24) (v22) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h9 : runInstructions productColumn0part9Program {s with pc := UInt256.ofNat 7832, memory := s.memory, stack := v27 :: v27 :: word11 :: word7 :: v24 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7842, memory := s.memory, stack := word7 :: v30 :: v30 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part9Model, v28, v29, v30] using productColumn0part9_run (s) (v27) (v27) (word11) (word7) (v24) (word7) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h10 : runInstructions productColumn0part10Program {s with pc := UInt256.ofNat 7842, memory := s.memory, stack := word7 :: v30 :: v30 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7854, memory := s.memory, stack := v33 :: v30 :: v31 :: word7 :: v30 :: v32 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part10Model, v31, v32, v33] using productColumn0part10_run (s) (word7) (v30) (v30) (word0) (word1) (word2) (word3) (word4) (word5) (v27) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h11 : runInstructions productColumn0part11Program {s with pc := UInt256.ofNat 7854, memory := s.memory, stack := v33 :: v30 :: v31 :: word7 :: v30 :: v32 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7864, memory := s.memory, stack := v37 :: word3 :: word7 :: v36 :: v34 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part11Model, v34, v35, v36, v37] using productColumn0part11_run (s) (v33) (v30) (v31) (word7) (v30) (v32) (word0) (word1) (word2) (word3) (word4) (word5) (v27) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h12 : runInstructions productColumn0part12Program {s with pc := UInt256.ofNat 7864, memory := s.memory, stack := v37 :: word3 :: word7 :: v36 :: v34 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7872, memory := s.memory, stack := v41 :: v39 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v27 :: word7 :: v5 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [productColumn0part12Model, v38, v39, v40, v41] using productColumn0part12_run (s) (v37) (word3) (word7) (v36) (v34) (word0) (word1) (word2) (word3) (word4) (word5) (v27) (word7) (v5) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution

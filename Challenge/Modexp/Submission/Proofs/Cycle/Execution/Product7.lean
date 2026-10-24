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

def productColumn7part0Program : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD]

def productColumn7part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := MachineState.readWord s.memory 1856
  {s with pc := UInt256.ofNat 9111, memory := s.memory, stack := v3 :: v2 :: x13 :: v1 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn7part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part0Program {s with pc := UInt256.ofNat 9100, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn7part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1856 : (1856 : UInt256).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part0Program, productColumn7part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha1856, hf1856]


def productColumn7part1Program : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn7part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x5
  let v2 : UInt256 := UInt256.mulMod x0 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 9119, memory := s.memory, stack := v3 :: x4 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn7part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part1Program {s with pc := UInt256.ofNat 9111, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn7part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn7part1Program, productColumn7part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn7part2Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩)]

def productColumn7part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 1824
  {s with pc := UInt256.ofNat 9130, memory := s.memory, stack := v1 :: v0 :: x2 :: v0 :: x10 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn7part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part2Program {s with pc := UInt256.ofNat 9119, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn7part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : UInt256).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part2Program, productColumn7part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha1824, hf1824]


def productColumn7part3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def productColumn7part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x7 x3 x4
  let v3 : UInt256 := v2 + x5
  let v4 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 9139, memory := s.memory, stack := v4 :: x15 :: v3 :: x6 :: v1 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest}

theorem productColumn7part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part3Program {s with pc := UInt256.ofNat 9130, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest} =
      some (productColumn7part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part3Program, productColumn7part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def productColumn7part4Program : List Instr :=
  [.push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩)]

def productColumn7part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1792
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x4
  {s with pc := UInt256.ofNat 9149, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn7part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part4Program {s with pc := UInt256.ofNat 9139, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn7part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : UInt256).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part4Program, productColumn7part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1792, hf1792]


def productColumn7part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩)]

def productColumn7part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := x12 * x14
  let v3 : UInt256 := v2 + x5
  {s with pc := UInt256.ofNat 9157, memory := s.memory, stack := x7 :: v3 :: x4 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn7part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part5Program {s with pc := UInt256.ofNat 9149, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn7part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn7part5Program, productColumn7part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn7part6Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def productColumn7part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 192
  let v3 : UInt256 := v2 * x9
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 9166, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn7part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part6Program {s with pc := UInt256.ofNat 9157, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn7part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part6Program, productColumn7part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def productColumn7part7Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def productColumn7part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := v0 * x5
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 9175, memory := s.memory, stack := v3 :: x15 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn7part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part7Program {s with pc := UInt256.ofNat 9166, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn7part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part7Program, productColumn7part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha224, hf224]


def productColumn7part8Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩)]

def productColumn7part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  let v3 : UInt256 := v2 * x5
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 9185, memory := s.memory, stack := x14 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn7part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part8Program {s with pc := UInt256.ofNat 9175, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn7part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part8Program, productColumn7part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def productColumn7part9Program : List Instr :=
  [.push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def productColumn7part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1248
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 9195, memory := s.memory, stack := x10 :: x12 :: x11 :: x3 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn7part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part9Program {s with pc := UInt256.ofNat 9185, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn7part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part9Program, productColumn7part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248]


def productColumn7part10Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def productColumn7part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod x4 x7 x13
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 9203, memory := s.memory, stack := x4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn7part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part10Program {s with pc := UInt256.ofNat 9195, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn7part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn7part10Program, productColumn7part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn7part11Program : List Instr :=
  [.push 2 1088,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def productColumn7part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1088
  let v1 : UInt256 := MachineState.readWord v0 192
  let v2 : UInt256 := UInt256.mulMod v1 x8 x10
  let v3 : UInt256 := v2 + x1
  {s with pc := UInt256.ofNat 9214, memory := v0, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn7part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part11Program {s with pc := UInt256.ofNat 9203, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn7part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part11Program, productColumn7part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192, ha1088, hf1088]


def productColumn7part12Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def productColumn7part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := UInt256.mulMod v0 x4 x9
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 9222, memory := s.memory, stack := x14 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn7part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part12Program {s with pc := UInt256.ofNat 9214, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn7part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part12Program, productColumn7part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def productColumn7part13Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn7part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  {s with pc := UInt256.ofNat 9228, memory := s.memory, stack := x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn7part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7part13Program {s with pc := UInt256.ofNat 9222, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn7part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn7part13Program, productColumn7part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def productColumn7Program : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1856,
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
   .push 1 128,
   .op .MLOAD,
   .push 2 1824,
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
   .push 1 160,
   .op .MLOAD,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1088,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn7Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod word4 word0 word1
  let v1 : UInt256 := v0 + word2
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := MachineState.readWord s.memory 1856
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := v4 + carry
  let v6 : UInt256 := UInt256.mulMod v3 v2 word12
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := MachineState.readWord s.memory 128
  let v9 : UInt256 := MachineState.readWord s.memory 1824
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v5
  let v12 : UInt256 := UInt256.mulMod v9 v8 word12
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := MachineState.readWord s.memory 160
  let v15 : UInt256 := MachineState.readWord s.memory 1792
  let v16 : UInt256 := v15 * v14
  let v17 : UInt256 := v16 + v11
  let v18 : UInt256 := UInt256.mulMod v15 v14 word12
  let v19 : UInt256 := v18 + v13
  let v20 : UInt256 := word11 * word13
  let v21 : UInt256 := v20 + v17
  let v22 : UInt256 := word3 * word6
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := MachineState.readWord s.memory 192
  let v25 : UInt256 := v24 * word10
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := MachineState.readWord s.memory 0
  let v28 : UInt256 := v27 * word7
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord s.memory 224
  let v31 : UInt256 := v30 * word17
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 1216
  let v34 : UInt256 := v33 * word5
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := MachineState.readWord s.memory 1248
  let v37 : UInt256 := v36 * word14
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := UInt256.mulMod word11 word13 word12
  let v40 : UInt256 := v39 + v19
  let v41 : UInt256 := UInt256.mulMod word3 word6 word12
  let v42 : UInt256 := v41 + v40
  let v43 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded word3.toNat 32) 1088
  let v44 : UInt256 := MachineState.readWord v43 192
  let v45 : UInt256 := UInt256.mulMod v44 word10 word12
  let v46 : UInt256 := v45 + v42
  let v47 : UInt256 := MachineState.readWord v43 0
  let v48 : UInt256 := UInt256.mulMod v47 word7 word12
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := MachineState.readWord v43 224
  let v51 : UInt256 := UInt256.mulMod v50 word17 word12
  let v52 : UInt256 := v51 + v49
  {s with pc := UInt256.ofNat 9228, memory := v43, stack := word12 :: v52 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest}

theorem productColumn7_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7Program {s with pc := UInt256.ofNat 9100, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} =
      some (productColumn7Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 rest) := by
  let v0 : UInt256 := UInt256.mulMod word4 word0 word1
  let v1 : UInt256 := v0 + word2
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := MachineState.readWord s.memory 1856
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := v4 + carry
  let v6 : UInt256 := UInt256.mulMod v3 v2 word12
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := MachineState.readWord s.memory 128
  let v9 : UInt256 := MachineState.readWord s.memory 1824
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v5
  let v12 : UInt256 := UInt256.mulMod v9 v8 word12
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := MachineState.readWord s.memory 160
  let v15 : UInt256 := MachineState.readWord s.memory 1792
  let v16 : UInt256 := v15 * v14
  let v17 : UInt256 := v16 + v11
  let v18 : UInt256 := UInt256.mulMod v15 v14 word12
  let v19 : UInt256 := v18 + v13
  let v20 : UInt256 := word11 * word13
  let v21 : UInt256 := v20 + v17
  let v22 : UInt256 := word3 * word6
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := MachineState.readWord s.memory 192
  let v25 : UInt256 := v24 * word10
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := MachineState.readWord s.memory 0
  let v28 : UInt256 := v27 * word7
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord s.memory 224
  let v31 : UInt256 := v30 * word17
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 1216
  let v34 : UInt256 := v33 * word5
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := MachineState.readWord s.memory 1248
  let v37 : UInt256 := v36 * word14
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := UInt256.mulMod word11 word13 word12
  let v40 : UInt256 := v39 + v19
  let v41 : UInt256 := UInt256.mulMod word3 word6 word12
  let v42 : UInt256 := v41 + v40
  let v43 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded word3.toNat 32) 1088
  let v44 : UInt256 := MachineState.readWord v43 192
  let v45 : UInt256 := UInt256.mulMod v44 word10 word12
  let v46 : UInt256 := v45 + v42
  let v47 : UInt256 := MachineState.readWord v43 0
  let v48 : UInt256 := UInt256.mulMod v47 word7 word12
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := MachineState.readWord v43 224
  let v51 : UInt256 := UInt256.mulMod v50 word17 word12
  let v52 : UInt256 := v51 + v49
  have h0 : runInstructions productColumn7part0Program {s with pc := UInt256.ofNat 9100, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9111, memory := s.memory, stack := v3 :: v2 :: word12 :: v1 :: word3 :: carry :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part0Model, v0, v1, v2, v3] using productColumn7part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h1 : runInstructions productColumn7part1Program {s with pc := UInt256.ofNat 9111, memory := s.memory, stack := v3 :: v2 :: word12 :: v1 :: word3 :: carry :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9119, memory := s.memory, stack := v7 :: word3 :: v5 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part1Model, v4, v5, v6, v7] using productColumn7part1_run (s) (v3) (v2) (word12) (v1) (word3) (carry) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h2 : runInstructions productColumn7part2Program {s with pc := UInt256.ofNat 9119, memory := s.memory, stack := v7 :: word3 :: v5 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9130, memory := s.memory, stack := v9 :: v8 :: v5 :: v8 :: word12 :: v7 :: word3 :: v9 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part2Model, v8, v9] using productColumn7part2_run (s) (v7) (word3) (v5) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h3 : runInstructions productColumn7part3Program {s with pc := UInt256.ofNat 9130, memory := s.memory, stack := v9 :: v8 :: v5 :: v8 :: word12 :: v7 :: word3 :: v9 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9139, memory := s.memory, stack := v14 :: word12 :: v13 :: word3 :: v11 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part3Model, v10, v11, v12, v13, v14] using productColumn7part3_run (s) (v9) (v8) (v5) (v8) (word12) (v7) (word3) (v9) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h4 : runInstructions productColumn7part4Program {s with pc := UInt256.ofNat 9139, memory := s.memory, stack := v14 :: word12 :: v13 :: word3 :: v11 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9149, memory := s.memory, stack := v15 :: v14 :: word12 :: v13 :: word3 :: v17 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part4Model, v15, v16, v17] using productColumn7part4_run (s) (v14) (word12) (v13) (word3) (v11) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h5 : runInstructions productColumn7part5Program {s with pc := UInt256.ofNat 9149, memory := s.memory, stack := v15 :: v14 :: word12 :: v13 :: word3 :: v17 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9157, memory := s.memory, stack := word6 :: v21 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part5Model, v18, v19, v20, v21] using productColumn7part5_run (s) (v15) (v14) (word12) (v13) (word3) (v17) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h6 : runInstructions productColumn7part6Program {s with pc := UInt256.ofNat 9157, memory := s.memory, stack := word6 :: v21 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9166, memory := s.memory, stack := v26 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part6Model, v22, v23, v24, v25, v26] using productColumn7part6_run (s) (word6) (v21) (word3) (v19) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h7 : runInstructions productColumn7part7Program {s with pc := UInt256.ofNat 9166, memory := s.memory, stack := v26 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9175, memory := s.memory, stack := v30 :: word17 :: v29 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part7Model, v27, v28, v29, v30] using productColumn7part7_run (s) (v26) (word3) (v19) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h8 : runInstructions productColumn7part8Program {s with pc := UInt256.ofNat 9175, memory := s.memory, stack := v30 :: word17 :: v29 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9185, memory := s.memory, stack := word14 :: v35 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part8Model, v31, v32, v33, v34, v35] using productColumn7part8_run (s) (v30) (word17) (v29) (word3) (v19) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h9 : runInstructions productColumn7part9Program {s with pc := UInt256.ofNat 9185, memory := s.memory, stack := word14 :: v35 :: word3 :: v19 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9195, memory := s.memory, stack := word11 :: word13 :: word12 :: v19 :: word3 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part9Model, v36, v37, v38] using productColumn7part9_run (s) (word14) (v35) (word3) (v19) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h10 : runInstructions productColumn7part10Program {s with pc := UInt256.ofNat 9195, memory := s.memory, stack := word11 :: word13 :: word12 :: v19 :: word3 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9203, memory := s.memory, stack := word3 :: v42 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part10Model, v39, v40, v41, v42] using productColumn7part10_run (s) (word11) (word13) (word12) (v19) (word3) (v38) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h11 : runInstructions productColumn7part11Program {s with pc := UInt256.ofNat 9203, memory := s.memory, stack := word3 :: v42 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9214, memory := v43, stack := v46 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part11Model, v43, v44, v45, v46] using productColumn7part11_run (s) (word3) (v42) (v38) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h12 : runInstructions productColumn7part12Program {s with pc := UInt256.ofNat 9214, memory := v43, stack := v46 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9222, memory := v43, stack := word17 :: word12 :: v49 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part12Model, v47, v48, v49] using productColumn7part12_run ({s with memory := v43}) (v46) (v38) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h13 : runInstructions productColumn7part13Program {s with pc := UInt256.ofNat 9222, memory := v43, stack := word17 :: word12 :: v49 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 9228, memory := v43, stack := word12 :: v52 :: v38 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [productColumn7part13Model, v50, v51, v52] using productColumn7part13_run ({s with memory := v43}) (word17) (word12) (v49) (v38) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution

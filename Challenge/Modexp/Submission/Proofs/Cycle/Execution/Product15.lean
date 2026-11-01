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

def productColumn15part0Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def productColumn15part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x15 * x14
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 9676, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn15part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part0Program {s with pc := UInt256.ofNat 9668, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn15part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn15part0Program, productColumn15part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn15part0_run

def productColumn15part1Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def productColumn15part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := UInt256.mulMod x10 v0 x9
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 9686, memory := s.memory, stack := v3 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn15part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part1Program {s with pc := UInt256.ofNat 9676, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn15part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn15part1Program, productColumn15part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha224, hf224]

#print axioms productColumn15part1_run

def productColumn15part2Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn15part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x5 x8 x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 9694, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn15part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part2Program {s with pc := UInt256.ofNat 9686, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn15part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn15part2Program, productColumn15part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn15part2_run

def productColumn15part3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨6, by decide⟩)]

def productColumn15part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x7 x5 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 9702, memory := s.memory, stack := x4 :: x11 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn15part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part3Program {s with pc := UInt256.ofNat 9694, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn15part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn15part3Program, productColumn15part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn15part3_run

def productColumn15part4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def productColumn15part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod x16 x17 x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 9710, memory := s.memory, stack := x4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn15part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part4Program {s with pc := UInt256.ofNat 9702, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn15part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn15part4Program, productColumn15part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn15part4_run

def productColumn15part5Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .push 6 2048]

def productColumn15part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x12 x0
  let v1 : UInt256 := x1 - v0
  let v2 : UInt256 := x9 + v1
  {s with pc := UInt256.ofNat 9724, memory := s.memory, stack := (UInt256.ofNat 2048) :: v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn15part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part5Program {s with pc := UInt256.ofNat 9710, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn15part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn15part5Program, productColumn15part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn15part5_run

def productColumn15part6Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 2048,
   .op .MLOAD]

def productColumn15part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x1 x0 x10
  let v1 : UInt256 := MachineState.readWord s.memory 64
  let v2 : UInt256 := MachineState.readWord s.memory 2048
  {s with pc := UInt256.ofNat 9736, memory := s.memory, stack := v2 :: v0 :: v1 :: x10 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn15part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part6Program {s with pc := UInt256.ofNat 9724, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn15part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : UInt256).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn15part6Program, productColumn15part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha2048, hf2048]

#print axioms productColumn15part6_run

def productColumn15part7Program : List Instr :=
  [.op (.Swap ⟨4, by decide⟩),
   .push 2 832,
   .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn15part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x5.toNat 32) 832
  let v1 : UInt256 := x0 * x2
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 9746, memory := v0, stack := x0 :: x2 :: x3 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn15part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part7Program {s with pc := UInt256.ofNat 9736, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn15part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn15part7Program, productColumn15part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha832, hf832]

#print axioms productColumn15part7_run

def productColumn15part8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn15part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := MachineState.readWord s.memory 2016
  {s with pc := UInt256.ofNat 9757, memory := s.memory, stack := x4 :: v2 :: x12 :: v1 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn15part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part8Program {s with pc := UInt256.ofNat 9746, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn15part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : UInt256).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn15part8Program, productColumn15part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha2016, hf2016]

#print axioms productColumn15part8_run

def productColumn15part9Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn15part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x4 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 9765, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn15part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part9Program {s with pc := UInt256.ofNat 9757, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn15part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn15part9Program, productColumn15part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn15part9_run

def productColumn15part10Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn15part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 1984
  let v2 : UInt256 := v1 * v0
  {s with pc := UInt256.ofNat 9776, memory := s.memory, stack := v2 :: x2 :: v0 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn15part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part10Program {s with pc := UInt256.ofNat 9765, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn15part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : UInt256).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn15part10Program, productColumn15part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha1984, hf1984]

#print axioms productColumn15part10_run

def productColumn15part11Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD]

def productColumn15part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := MachineState.readWord s.memory 160
  let v4 : UInt256 := MachineState.readWord s.memory 1952
  {s with pc := UInt256.ofNat 9788, memory := s.memory, stack := v4 :: v3 :: x13 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn15part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part11Program {s with pc := UInt256.ofNat 9776, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn15part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : UInt256).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn15part11Program, productColumn15part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160, ha1952, hf1952]

#print axioms productColumn15part11_run

def productColumn15part12Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn15part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x4
  let v2 : UInt256 := UInt256.mulMod x0 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 9796, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn15part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15part12Program {s with pc := UInt256.ofNat 9788, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn15part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn15part12Program, productColumn15part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn15part12_run

def productColumn15Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .push 6 2048,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .push 2 832,
   .op .MSTORE,
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
   .push 2 2016,
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
   .push 1 160,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn15Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := word4 * carry
  let v1 : UInt256 := v0 + word0
  let v2 : UInt256 := word14 * word13
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := MachineState.readWord s.memory 0
  let v5 : UInt256 := UInt256.mulMod word10 v4 word9
  let v6 : UInt256 := v5 + word1
  let v7 : UInt256 := MachineState.readWord s.memory 224
  let v8 : UInt256 := UInt256.mulMod word8 v7 word9
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := UInt256.mulMod word3 word6 word9
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.mulMod word7 word5 word9
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word4 word11 word9
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.mulMod word13 word14 word9
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.land word12 v3
  let v19 : UInt256 := v17 - v18
  let v20 : UInt256 := word9 + v19
  let v21 : UInt256 := UInt256.mulMod v20 (UInt256.ofNat 2048) word9
  let v22 : UInt256 := MachineState.readWord s.memory 64
  let v23 : UInt256 := MachineState.readWord s.memory 2048
  let v24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 832
  let v25 : UInt256 := v23 * v22
  let v26 : UInt256 := v25 + v21
  let v27 : UInt256 := UInt256.mulMod v23 v22 word9
  let v28 : UInt256 := v27 + v21
  let v29 : UInt256 := MachineState.readWord v24 96
  let v30 : UInt256 := MachineState.readWord v24 2016
  let v31 : UInt256 := v30 * v29
  let v32 : UInt256 := v31 + v26
  let v33 : UInt256 := UInt256.mulMod v30 v29 word9
  let v34 : UInt256 := v33 + v28
  let v35 : UInt256 := MachineState.readWord v24 128
  let v36 : UInt256 := MachineState.readWord v24 1984
  let v37 : UInt256 := v36 * v35
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := UInt256.mulMod v36 v35 word9
  let v40 : UInt256 := v39 + v34
  let v41 : UInt256 := MachineState.readWord v24 160
  let v42 : UInt256 := MachineState.readWord v24 1952
  let v43 : UInt256 := v42 * v41
  let v44 : UInt256 := v43 + v38
  let v45 : UInt256 := UInt256.mulMod v42 v41 word9
  let v46 : UInt256 := v45 + v40
  {s with pc := UInt256.ofNat 9796, memory := v24, stack := v46 :: v44 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest}

theorem productColumn15_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15Program {s with pc := UInt256.ofNat 9668, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} =
      some (productColumn15Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 rest) := by
  let v0 : UInt256 := word4 * carry
  let v1 : UInt256 := v0 + word0
  let v2 : UInt256 := word14 * word13
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := MachineState.readWord s.memory 0
  let v5 : UInt256 := UInt256.mulMod word10 v4 word9
  let v6 : UInt256 := v5 + word1
  let v7 : UInt256 := MachineState.readWord s.memory 224
  let v8 : UInt256 := UInt256.mulMod word8 v7 word9
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := UInt256.mulMod word3 word6 word9
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.mulMod word7 word5 word9
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word4 word11 word9
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.mulMod word13 word14 word9
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.land word12 v3
  let v19 : UInt256 := v17 - v18
  let v20 : UInt256 := word9 + v19
  let v21 : UInt256 := UInt256.mulMod v20 (UInt256.ofNat 2048) word9
  let v22 : UInt256 := MachineState.readWord s.memory 64
  let v23 : UInt256 := MachineState.readWord s.memory 2048
  let v24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 832
  let v25 : UInt256 := v23 * v22
  let v26 : UInt256 := v25 + v21
  let v27 : UInt256 := UInt256.mulMod v23 v22 word9
  let v28 : UInt256 := v27 + v21
  let v29 : UInt256 := MachineState.readWord v24 96
  let v30 : UInt256 := MachineState.readWord v24 2016
  let v31 : UInt256 := v30 * v29
  let v32 : UInt256 := v31 + v26
  let v33 : UInt256 := UInt256.mulMod v30 v29 word9
  let v34 : UInt256 := v33 + v28
  let v35 : UInt256 := MachineState.readWord v24 128
  let v36 : UInt256 := MachineState.readWord v24 1984
  let v37 : UInt256 := v36 * v35
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := UInt256.mulMod v36 v35 word9
  let v40 : UInt256 := v39 + v34
  let v41 : UInt256 := MachineState.readWord v24 160
  let v42 : UInt256 := MachineState.readWord v24 1952
  let v43 : UInt256 := v42 * v41
  let v44 : UInt256 := v43 + v38
  let v45 : UInt256 := UInt256.mulMod v42 v41 word9
  let v46 : UInt256 := v45 + v40
  have h0 : runInstructions productColumn15part0Program {s with pc := UInt256.ofNat 9668, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9676, memory := s.memory, stack := word1 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part0Model, v0, v1, v2, v3] using productColumn15part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h1 : runInstructions productColumn15part1Program {s with pc := UInt256.ofNat 9676, memory := s.memory, stack := word1 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9686, memory := s.memory, stack := v7 :: word9 :: v6 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part1Model, v4, v5, v6, v7] using productColumn15part1_run (s) (word1) (v3) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h2 : runInstructions productColumn15part2Program {s with pc := UInt256.ofNat 9686, memory := s.memory, stack := v7 :: word9 :: v6 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9694, memory := s.memory, stack := v11 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part2Model, v8, v9, v10, v11] using productColumn15part2_run (s) (v7) (word9) (v6) (v3) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h3 : runInstructions productColumn15part3Program {s with pc := UInt256.ofNat 9694, memory := s.memory, stack := v11 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9702, memory := s.memory, stack := word4 :: word11 :: word9 :: v13 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part3Model, v12, v13] using productColumn15part3_run (s) (v11) (v3) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h4 : runInstructions productColumn15part4Program {s with pc := UInt256.ofNat 9702, memory := s.memory, stack := word4 :: word11 :: word9 :: v13 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9710, memory := s.memory, stack := v3 :: v17 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part4Model, v14, v15, v16, v17] using productColumn15part4_run (s) (word4) (word11) (word9) (v13) (v3) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h5 : runInstructions productColumn15part5Program {s with pc := UInt256.ofNat 9710, memory := s.memory, stack := v3 :: v17 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9724, memory := s.memory, stack := (UInt256.ofNat 2048) :: v20 :: v18 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part5Model, v18, v19, v20] using productColumn15part5_run (s) (v3) (v17) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h6 : runInstructions productColumn15part6Program {s with pc := UInt256.ofNat 9724, memory := s.memory, stack := (UInt256.ofNat 2048) :: v20 :: v18 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9736, memory := s.memory, stack := v23 :: v21 :: v22 :: word9 :: v21 :: v18 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part6Model, v21, v22, v23] using productColumn15part6_run (s) ((UInt256.ofNat 2048)) (v20) (v18) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h7 : runInstructions productColumn15part7Program {s with pc := UInt256.ofNat 9736, memory := s.memory, stack := v23 :: v21 :: v22 :: word9 :: v21 :: v18 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9746, memory := v24, stack := v23 :: v22 :: word9 :: v21 :: v26 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part7Model, v24, v25, v26] using productColumn15part7_run (s) (v23) (v21) (v22) (word9) (v21) (v18) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h8 : runInstructions productColumn15part8Program {s with pc := UInt256.ofNat 9746, memory := v24, stack := v23 :: v22 :: word9 :: v21 :: v26 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9757, memory := v24, stack := v26 :: v29 :: word9 :: v28 :: v30 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part8Model, v27, v28, v29, v30] using productColumn15part8_run ({s with memory := v24}) (v23) (v22) (word9) (v21) (v26) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h9 : runInstructions productColumn15part9Program {s with pc := UInt256.ofNat 9757, memory := v24, stack := v26 :: v29 :: word9 :: v28 :: v30 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9765, memory := v24, stack := word9 :: v34 :: v32 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part9Model, v31, v32, v33, v34] using productColumn15part9_run ({s with memory := v24}) (v26) (v29) (word9) (v28) (v30) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h10 : runInstructions productColumn15part10Program {s with pc := UInt256.ofNat 9765, memory := v24, stack := word9 :: v34 :: v32 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9776, memory := v24, stack := v37 :: v32 :: v35 :: word9 :: v34 :: v36 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part10Model, v35, v36, v37] using productColumn15part10_run ({s with memory := v24}) (word9) (v34) (v32) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h11 : runInstructions productColumn15part11Program {s with pc := UInt256.ofNat 9776, memory := v24, stack := v37 :: v32 :: v35 :: word9 :: v34 :: v36 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9788, memory := v24, stack := v42 :: v41 :: word9 :: v40 :: v38 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part11Model, v38, v39, v40, v41, v42] using productColumn15part11_run ({s with memory := v24}) (v37) (v32) (v35) (word9) (v34) (v36) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h12 : runInstructions productColumn15part12Program {s with pc := UInt256.ofNat 9788, memory := v24, stack := v42 :: v41 :: word9 :: v40 :: v38 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9796, memory := v24, stack := v46 :: v44 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn15part12Model, v43, v44, v45, v46] using productColumn15part12_run ({s with memory := v24}) (v42) (v41) (word9) (v40) (v38) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms productColumn15_run

end CycleSubmission.Execution

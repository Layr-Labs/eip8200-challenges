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

def productColumn18part0Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def productColumn18part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x6 x3 x4
  let v3 : UInt256 := v2 + x5
  {s with pc := UInt256.ofNat 10060, memory := s.memory, stack := x15 :: x10 :: v1 :: v3 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn18part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part0Program {s with pc := UInt256.ofNat 10052, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn18part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part0Program, productColumn18part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part0_run

def productColumn18part1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def productColumn18part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x10 * x13
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 10068, memory := s.memory, stack := x5 :: x15 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn18part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part1Program {s with pc := UInt256.ofNat 10060, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn18part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part1Program, productColumn18part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part1_run

def productColumn18part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn18part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x12 x7 x11
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 10076, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn18part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part2Program {s with pc := UInt256.ofNat 10068, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn18part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part2Program, productColumn18part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part2_run

def productColumn18part3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn18part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x11 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 10084, memory := s.memory, stack := x3 :: x13 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part3Program {s with pc := UInt256.ofNat 10076, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part3Program, productColumn18part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part3_run

def productColumn18part4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MSTORE]

def productColumn18part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  {s with pc := UInt256.ofNat 10093, memory := v3, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn18part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part4Program {s with pc := UInt256.ofNat 10084, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn18part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part4Program, productColumn18part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]

#print axioms productColumn18part4_run

def productColumn18part5Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 6 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD]

def productColumn18part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 - x0
  let v1 : UInt256 := x9 + v0
  let v2 : UInt256 := UInt256.mulMod v1 (UInt256.ofNat 2048) x9
  {s with pc := UInt256.ofNat 10107, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part5Program {s with pc := UInt256.ofNat 10093, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part5Program, productColumn18part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part5_run

def productColumn18part6Program : List Instr :=
  [.push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 800,
   .op .MLOAD]

def productColumn18part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2048
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := MachineState.readWord s.memory 800
  {s with pc := UInt256.ofNat 10121, memory := s.memory, stack := v2 :: x0 :: v1 :: x8 :: x0 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem productColumn18part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part6Program {s with pc := UInt256.ofNat 10107, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (productColumn18part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : UInt256).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part6Program, productColumn18part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160, ha800, hf800, ha2048, hf2048]

#print axioms productColumn18part6_run

def productColumn18part7Program : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD]

def productColumn18part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x2
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x5 x2 x3
  {s with pc := UInt256.ofNat 10129, memory := s.memory, stack := v2 :: x4 :: v1 :: x6 :: x7 :: x8 :: x0 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn18part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part7Program {s with pc := UInt256.ofNat 10121, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn18part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part7Program, productColumn18part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part7_run

def productColumn18part8Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn18part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 2016
  {s with pc := UInt256.ofNat 10139, memory := s.memory, stack := v1 :: x3 :: x2 :: x3 :: x10 :: v0 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn18part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part8Program {s with pc := UInt256.ofNat 10129, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn18part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha2016 : (2016 : UInt256).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part8Program, productColumn18part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2016, hf2016]

#print axioms productColumn18part8_run

def productColumn18part9Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def productColumn18part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x6 x3 x4
  let v3 : UInt256 := v2 + x5
  {s with pc := UInt256.ofNat 10147, memory := s.memory, stack := x15 :: x16 :: v1 :: v3 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn18part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part9Program {s with pc := UInt256.ofNat 10139, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn18part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part9Program, productColumn18part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part9_run

def productColumn18part10Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def productColumn18part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x10 * x15
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 10155, memory := s.memory, stack := x11 :: x3 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn18part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part10Program {s with pc := UInt256.ofNat 10147, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn18part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part10Program, productColumn18part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part10_run

def productColumn18part11Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def productColumn18part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x12 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x9 x14 x10
  {s with pc := UInt256.ofNat 10163, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn18part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part11Program {s with pc := UInt256.ofNat 10155, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn18part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part11Program, productColumn18part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part11_run

def productColumn18part12Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩)]

def productColumn18part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.land x13 x2
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 128
  {s with pc := UInt256.ofNat 10172, memory := v2, stack := v0 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn18part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part12Program {s with pc := UInt256.ofNat 10163, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn18part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part12Program, productColumn18part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]

#print axioms productColumn18part12_run

def productColumn18part13Program : List Instr :=
  [.op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 6 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD]

def productColumn18part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := x9 + v0
  let v2 : UInt256 := UInt256.mulMod v1 (UInt256.ofNat 2048) x9
  let v3 : UInt256 := MachineState.readWord s.memory 2048
  {s with pc := UInt256.ofNat 10189, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part13Program {s with pc := UInt256.ofNat 10172, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : UInt256).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part13Program, productColumn18part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2048, hf2048]

#print axioms productColumn18part13_run

def productColumn18part14Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩)]

def productColumn18part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10190, memory := s.memory, stack := x1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part14Program {s with pc := UInt256.ofNat 10189, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part14Program, productColumn18part14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn18part14_run

def productColumn18Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 6 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
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
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
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
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 6 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨0, by decide⟩)]

def productColumn18Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := word14 * word9
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := word12 * word15
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := word7 * word17
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := UInt256.mulMod word14 word9 word13
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := UInt256.mulMod word12 word15 word13
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word7 word17 word13
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.land word16 v9
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 96
  let v18 : UInt256 := v15 - v16
  let v19 : UInt256 := word13 + v18
  let v20 : UInt256 := UInt256.mulMod v19 (UInt256.ofNat 2048) word13
  let v21 : UInt256 := MachineState.readWord v17 2048
  let v22 : UInt256 := MachineState.readWord v17 160
  let v23 : UInt256 := MachineState.readWord v17 800
  let v24 : UInt256 := v21 * v22
  let v25 : UInt256 := v24 + v20
  let v26 : UInt256 := UInt256.mulMod v21 v22 word13
  let v27 : UInt256 := v26 + v20
  let v28 : UInt256 := MachineState.readWord v17 2016
  let v29 : UInt256 := v28 * word6
  let v30 : UInt256 := v29 + v25
  let v31 : UInt256 := UInt256.mulMod v28 word6 word13
  let v32 : UInt256 := v31 + v27
  let v33 : UInt256 := word14 * word15
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := word12 * word17
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := UInt256.mulMod word14 word15 word13
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := UInt256.mulMod word12 word17 word13
  let v40 : UInt256 := v39 + v38
  let v41 : UInt256 := UInt256.land word16 v36
  let v42 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v41.toNat 32) 128
  let v43 : UInt256 := v40 - v41
  let v44 : UInt256 := word13 + v43
  let v45 : UInt256 := UInt256.mulMod v44 (UInt256.ofNat 2048) word13
  let v46 : UInt256 := MachineState.readWord v42 2048
  {s with pc := UInt256.ofNat 10190, memory := v42, stack := v45 :: v46 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest}

theorem productColumn18_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18Program {s with pc := UInt256.ofNat 10052, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} =
      some (productColumn18Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 rest) := by
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := word14 * word9
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := word12 * word15
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := word7 * word17
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := UInt256.mulMod word14 word9 word13
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := UInt256.mulMod word12 word15 word13
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word7 word17 word13
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.land word16 v9
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 96
  let v18 : UInt256 := v15 - v16
  let v19 : UInt256 := word13 + v18
  let v20 : UInt256 := UInt256.mulMod v19 (UInt256.ofNat 2048) word13
  let v21 : UInt256 := MachineState.readWord v17 2048
  let v22 : UInt256 := MachineState.readWord v17 160
  let v23 : UInt256 := MachineState.readWord v17 800
  let v24 : UInt256 := v21 * v22
  let v25 : UInt256 := v24 + v20
  let v26 : UInt256 := UInt256.mulMod v21 v22 word13
  let v27 : UInt256 := v26 + v20
  let v28 : UInt256 := MachineState.readWord v17 2016
  let v29 : UInt256 := v28 * word6
  let v30 : UInt256 := v29 + v25
  let v31 : UInt256 := UInt256.mulMod v28 word6 word13
  let v32 : UInt256 := v31 + v27
  let v33 : UInt256 := word14 * word15
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := word12 * word17
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := UInt256.mulMod word14 word15 word13
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := UInt256.mulMod word12 word17 word13
  let v40 : UInt256 := v39 + v38
  let v41 : UInt256 := UInt256.land word16 v36
  let v42 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v41.toNat 32) 128
  let v43 : UInt256 := v40 - v41
  let v44 : UInt256 := word13 + v43
  let v45 : UInt256 := UInt256.mulMod v44 (UInt256.ofNat 2048) word13
  let v46 : UInt256 := MachineState.readWord v42 2048
  have h0 : runInstructions productColumn18part0Program {s with pc := UInt256.ofNat 10052, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10060, memory := s.memory, stack := word14 :: word9 :: v1 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part0Model, v0, v1, v2, v3] using productColumn18part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h1 : runInstructions productColumn18part1Program {s with pc := UInt256.ofNat 10060, memory := s.memory, stack := word14 :: word9 :: v1 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10068, memory := s.memory, stack := word7 :: word17 :: v7 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part1Model, v4, v5, v6, v7] using productColumn18part1_run (s) (word14) (word9) (v1) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h2 : runInstructions productColumn18part2Program {s with pc := UInt256.ofNat 10068, memory := s.memory, stack := word7 :: word17 :: v7 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10076, memory := s.memory, stack := v11 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part2Model, v8, v9, v10, v11] using productColumn18part2_run (s) (word7) (word17) (v7) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h3 : runInstructions productColumn18part3Program {s with pc := UInt256.ofNat 10076, memory := s.memory, stack := v11 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10084, memory := s.memory, stack := word7 :: word17 :: word13 :: v13 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part3Model, v12, v13] using productColumn18part3_run (s) (v11) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h4 : runInstructions productColumn18part4Program {s with pc := UInt256.ofNat 10084, memory := s.memory, stack := word7 :: word17 :: word13 :: v13 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10093, memory := v17, stack := v16 :: v15 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part4Model, v14, v15, v16, v17] using productColumn18part4_run (s) (word7) (word17) (word13) (v13) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h5 : runInstructions productColumn18part5Program {s with pc := UInt256.ofNat 10093, memory := v17, stack := v16 :: v15 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10107, memory := v17, stack := v20 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part5Model, v18, v19, v20] using productColumn18part5_run ({s with memory := v17}) (v16) (v15) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h6 : runInstructions productColumn18part6Program {s with pc := UInt256.ofNat 10107, memory := v17, stack := v20 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10121, memory := v17, stack := v23 :: v20 :: v22 :: word13 :: v20 :: v21 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part6Model, v21, v22, v23] using productColumn18part6_run ({s with memory := v17}) (v20) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h7 : runInstructions productColumn18part7Program {s with pc := UInt256.ofNat 10121, memory := v17, stack := v23 :: v20 :: v22 :: word13 :: v20 :: v21 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10129, memory := v17, stack := v26 :: v20 :: v25 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part7Model, v24, v25, v26] using productColumn18part7_run ({s with memory := v17}) (v23) (v20) (v22) (word13) (v20) (v21) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h8 : runInstructions productColumn18part8Program {s with pc := UInt256.ofNat 10129, memory := v17, stack := v26 :: v20 :: v25 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10139, memory := v17, stack := v28 :: word6 :: v25 :: word6 :: word13 :: v27 :: v28 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part8Model, v27, v28] using productColumn18part8_run ({s with memory := v17}) (v26) (v20) (v25) (word6) (word7) (word8) (v23) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h9 : runInstructions productColumn18part9Program {s with pc := UInt256.ofNat 10139, memory := v17, stack := v28 :: word6 :: v25 :: word6 :: word13 :: v27 :: v28 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10147, memory := v17, stack := word14 :: word15 :: v30 :: v32 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part9Model, v29, v30, v31, v32] using productColumn18part9_run ({s with memory := v17}) (v28) (word6) (v25) (word6) (word13) (v27) (v28) (word6) (word7) (word8) (v23) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h10 : runInstructions productColumn18part10Program {s with pc := UInt256.ofNat 10147, memory := v17, stack := word14 :: word15 :: v30 :: v32 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10155, memory := v17, stack := word13 :: v32 :: v36 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part10Model, v33, v34, v35, v36] using productColumn18part10_run ({s with memory := v17}) (word14) (word15) (v30) (v32) (word6) (word7) (word8) (v23) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h11 : runInstructions productColumn18part11Program {s with pc := UInt256.ofNat 10155, memory := v17, stack := word13 :: v32 :: v36 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10163, memory := v17, stack := v39 :: v38 :: v36 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part11Model, v37, v38, v39] using productColumn18part11_run ({s with memory := v17}) (word13) (v32) (v36) (word6) (word7) (word8) (v23) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h12 : runInstructions productColumn18part12Program {s with pc := UInt256.ofNat 10163, memory := v17, stack := v39 :: v38 :: v36 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10172, memory := v42, stack := v40 :: v41 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part12Model, v40, v41, v42] using productColumn18part12_run ({s with memory := v17}) (v39) (v38) (v36) (word6) (word7) (word8) (v23) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h13 : runInstructions productColumn18part13Program {s with pc := UInt256.ofNat 10172, memory := v42, stack := v40 :: v41 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10189, memory := v42, stack := v46 :: v45 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part13Model, v43, v44, v45, v46] using productColumn18part13_run ({s with memory := v42}) (v40) (v41) (word6) (word7) (word8) (v23) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h14 : runInstructions productColumn18part14Program {s with pc := UInt256.ofNat 10189, memory := v42, stack := v46 :: v45 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10190, memory := v42, stack := v45 :: v46 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part14Model] using productColumn18part14_run ({s with memory := v42}) (v46) (v45) (word6) (word7) (word8) (v23) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))

#print axioms productColumn18_run

end CycleSubmission.Execution

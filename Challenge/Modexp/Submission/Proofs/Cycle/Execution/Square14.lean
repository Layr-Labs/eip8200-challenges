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

def squareColumn14part0Program : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def squareColumn14part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 800
  let v1 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 7509, memory := s.memory, stack := v1 :: x8 :: x14 :: x0 :: x1 :: x2 :: x3 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem squareColumn14part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part0Program {s with pc := UInt256.ofNat 7498, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (squareColumn14part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part0Program, squareColumn14part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160, ha800, hf800]

#print axioms squareColumn14part0_run

def squareColumn14part1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn14part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x0
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := UInt256.mulMod x2 x0 x1
  {s with pc := UInt256.ofNat 7517, memory := s.memory, stack := v2 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn14part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part1Program {s with pc := UInt256.ofNat 7509, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn14part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part1Program, squareColumn14part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part1_run

def squareColumn14part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL]

def squareColumn14part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x3 + v0
  let v2 : UInt256 := x3 + x2
  let v3 : UInt256 := x12 * x13
  {s with pc := UInt256.ofNat 7525, memory := s.memory, stack := v3 :: v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn14part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part2Program {s with pc := UInt256.ofNat 7517, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn14part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part2Program, squareColumn14part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part2_run

def squareColumn14part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn14part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x9 * x14
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7533, memory := s.memory, stack := x12 :: x10 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part3Program {s with pc := UInt256.ofNat 7525, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part3Program, squareColumn14part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part3_run

def squareColumn14part4Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def squareColumn14part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x12 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x10 x15 x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7541, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn14part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part4Program {s with pc := UInt256.ofNat 7533, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn14part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part4Program, squareColumn14part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part4_run

def squareColumn14part5Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB]

def squareColumn14part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x12 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 128
  let v2 : UInt256 := x0 - v0
  {s with pc := UInt256.ofNat 7550, memory := v1, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn14part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part5Program {s with pc := UInt256.ofNat 7541, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn14part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part5Program, squareColumn14part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]

#print axioms squareColumn14part5_run

def squareColumn14part6Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 1376,
   .op .MLOAD]

def squareColumn14part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x8 + x0
  let v1 : UInt256 := UInt256.mulMod v0 (UInt256.ofNat 2048) x8
  let v2 : UInt256 := MachineState.readWord s.memory 1376
  {s with pc := UInt256.ofNat 7567, memory := s.memory, stack := v2 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem squareColumn14part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part6Program {s with pc := UInt256.ofNat 7550, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (squareColumn14part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part6Program, squareColumn14part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1376, hf1376]

#print axioms squareColumn14part6_run

def squareColumn14part7Program : List Instr :=
  [.op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn14part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x15 x15 x9
  {s with pc := UInt256.ofNat 7575, memory := s.memory, stack := x15 :: x15 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn14part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part7Program {s with pc := UInt256.ofNat 7567, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn14part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part7Program, squareColumn14part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part7_run

def squareColumn14part8Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩)]

def squareColumn14part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := x3 + v0
  let v2 : UInt256 := x15 * x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7583, memory := s.memory, stack := x3 :: x2 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn14part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part8Program {s with pc := UInt256.ofNat 7575, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn14part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part8Program, squareColumn14part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part8_run

def squareColumn14part9Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn14part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x11 x14 x10
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7591, memory := s.memory, stack := x13 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part9Program {s with pc := UInt256.ofNat 7583, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part9Program, squareColumn14part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part9_run

def squareColumn14part10Program : List Instr :=
  [.op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 160,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD]

def squareColumn14part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 160
  let v2 : UInt256 := x2 - v0
  let v3 : UInt256 := x10 + v2
  {s with pc := UInt256.ofNat 7600, memory := v1, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part10Program {s with pc := UInt256.ofNat 7591, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part10Program, squareColumn14part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]

#print axioms squareColumn14part10_run

def squareColumn14part11Program : List Instr :=
  [.push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1344,
   .op .MLOAD]

def squareColumn14part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 (UInt256.ofNat 2048) x8
  let v1 : UInt256 := MachineState.readWord s.memory 1344
  {s with pc := UInt256.ofNat 7617, memory := s.memory, stack := v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: v0 :: rest}

theorem squareColumn14part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part11Program {s with pc := UInt256.ofNat 7600, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (squareColumn14part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part11Program, squareColumn14part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1344, hf1344]

#print axioms squareColumn14part11_run

def squareColumn14part12Program : List Instr :=
  [.op (.Swap ⟨11, by decide⟩),
   .op .POP]

def squareColumn14part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 7619, memory := s.memory, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x0 :: x13 :: x14 :: rest}

theorem squareColumn14part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part12Program {s with pc := UInt256.ofNat 7617, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (squareColumn14part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part12Program, squareColumn14part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn14part12_run

def squareColumn14Program : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
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
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 1376,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 160,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP]

def squareColumn14Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 800
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := word13 * v1
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := UInt256.mulMod word13 v1 word7
  let v5 : UInt256 := v4 + v4
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v3
  let v8 : UInt256 := word8 * word9
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := word6 * word11
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.mulMod word8 word9 word7
  let v13 : UInt256 := v12 + v6
  let v14 : UInt256 := UInt256.mulMod word6 word11 word7
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.land word10 v11
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 128
  let v18 : UInt256 := v15 - v16
  let v19 : UInt256 := word7 + v18
  let v20 : UInt256 := UInt256.mulMod v19 (UInt256.ofNat 2048) word7
  let v21 : UInt256 := MachineState.readWord v17 1376
  let v22 : UInt256 := UInt256.mulMod word13 word13 word7
  let v23 : UInt256 := word13 * word13
  let v24 : UInt256 := v20 + v23
  let v25 : UInt256 := word11 * word8
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := v20 + v22
  let v28 : UInt256 := UInt256.mulMod word8 word11 word7
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := UInt256.land word10 v26
  let v31 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v30.toNat 32) 160
  let v32 : UInt256 := v29 - v30
  let v33 : UInt256 := word7 + v32
  let v34 : UInt256 := UInt256.mulMod v33 (UInt256.ofNat 2048) word7
  let v35 : UInt256 := MachineState.readWord v31 1344
  {s with pc := UInt256.ofNat 7619, memory := v31, stack := word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: v35 :: word12 :: v34 :: rest}

theorem squareColumn14_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14Program {s with pc := UInt256.ofNat 7498, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} =
      some (squareColumn14Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 800
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := word13 * v1
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := UInt256.mulMod word13 v1 word7
  let v5 : UInt256 := v4 + v4
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v3
  let v8 : UInt256 := word8 * word9
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := word6 * word11
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.mulMod word8 word9 word7
  let v13 : UInt256 := v12 + v6
  let v14 : UInt256 := UInt256.mulMod word6 word11 word7
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.land word10 v11
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 128
  let v18 : UInt256 := v15 - v16
  let v19 : UInt256 := word7 + v18
  let v20 : UInt256 := UInt256.mulMod v19 (UInt256.ofNat 2048) word7
  let v21 : UInt256 := MachineState.readWord v17 1376
  let v22 : UInt256 := UInt256.mulMod word13 word13 word7
  let v23 : UInt256 := word13 * word13
  let v24 : UInt256 := v20 + v23
  let v25 : UInt256 := word11 * word8
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := v20 + v22
  let v28 : UInt256 := UInt256.mulMod word8 word11 word7
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := UInt256.land word10 v26
  let v31 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v30.toNat 32) 160
  let v32 : UInt256 := v29 - v30
  let v33 : UInt256 := word7 + v32
  let v34 : UInt256 := UInt256.mulMod v33 (UInt256.ofNat 2048) word7
  let v35 : UInt256 := MachineState.readWord v31 1344
  have h0 : runInstructions squareColumn14part0Program {s with pc := UInt256.ofNat 7498, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7509, memory := s.memory, stack := v1 :: word7 :: word13 :: carry :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part0Model, v0, v1] using squareColumn14part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h1 : runInstructions squareColumn14part1Program {s with pc := UInt256.ofNat 7509, memory := s.memory, stack := v1 :: word7 :: word13 :: carry :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7517, memory := s.memory, stack := v4 :: v4 :: v3 :: carry :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part1Model, v2, v3, v4] using squareColumn14part1_run (s) (v1) (word7) (word13) (carry) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h2 : runInstructions squareColumn14part2Program {s with pc := UInt256.ofNat 7517, memory := s.memory, stack := v4 :: v4 :: v3 :: carry :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7525, memory := s.memory, stack := v8 :: v7 :: v6 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part2Model, v5, v6, v7, v8] using squareColumn14part2_run (s) (v4) (v4) (v3) (carry) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h3 : runInstructions squareColumn14part3Program {s with pc := UInt256.ofNat 7525, memory := s.memory, stack := v8 :: v7 :: v6 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7533, memory := s.memory, stack := word9 :: word7 :: v6 :: v11 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part3Model, v9, v10, v11] using squareColumn14part3_run (s) (v8) (v7) (v6) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h4 : runInstructions squareColumn14part4Program {s with pc := UInt256.ofNat 7533, memory := s.memory, stack := word9 :: word7 :: v6 :: v11 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7541, memory := s.memory, stack := v15 :: v11 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part4Model, v12, v13, v14, v15] using squareColumn14part4_run (s) (word9) (word7) (v6) (v11) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h5 : runInstructions squareColumn14part5Program {s with pc := UInt256.ofNat 7541, memory := s.memory, stack := v15 :: v11 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7550, memory := v17, stack := v18 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part5Model, v16, v17, v18] using squareColumn14part5_run (s) (v15) (v11) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h6 : runInstructions squareColumn14part6Program {s with pc := UInt256.ofNat 7550, memory := v17, stack := v18 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7567, memory := v17, stack := v21 :: v20 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part6Model, v19, v20, v21] using squareColumn14part6_run ({s with memory := v17}) (v18) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h7 : runInstructions squareColumn14part7Program {s with pc := UInt256.ofNat 7567, memory := v17, stack := v21 :: v20 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7575, memory := v17, stack := word13 :: word13 :: v22 :: v20 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part7Model, v22] using squareColumn14part7_run ({s with memory := v17}) (v21) (v20) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h8 : runInstructions squareColumn14part8Program {s with pc := UInt256.ofNat 7575, memory := v17, stack := word13 :: word13 :: v22 :: v20 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7583, memory := v17, stack := v20 :: v22 :: v26 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part8Model, v23, v24, v25, v26] using squareColumn14part8_run ({s with memory := v17}) (word13) (word13) (v22) (v20) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (v21) (word10) (word11) (word12) (word13) rest hcap hact
  have h9 : runInstructions squareColumn14part9Program {s with pc := UInt256.ofNat 7583, memory := v17, stack := v20 :: v22 :: v26 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7591, memory := v17, stack := word10 :: v26 :: v29 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part9Model, v27, v28, v29] using squareColumn14part9_run ({s with memory := v17}) (v20) (v22) (v26) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (v21) (word10) (word11) (word12) (word13) rest hcap hact
  have h10 : runInstructions squareColumn14part10Program {s with pc := UInt256.ofNat 7591, memory := v17, stack := word10 :: v26 :: v29 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7600, memory := v31, stack := v33 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn14part10Model, v30, v31, v32, v33] using squareColumn14part10_run ({s with memory := v17}) (word10) (v26) (v29) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (v21) (word10) (word11) (word12) (word13) rest hcap hact
  have h11 : runInstructions squareColumn14part11Program {s with pc := UInt256.ofNat 7600, memory := v31, stack := v33 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 7617, memory := v31, stack := v35 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: v34 :: rest} := by
    simpa only [squareColumn14part11Model, v34, v35] using squareColumn14part11_run ({s with memory := v31}) (v33) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (v21) (word10) (word11) (word12) (word13) rest hcap hact
  have h12 : runInstructions squareColumn14part12Program {s with pc := UInt256.ofNat 7617, memory := v31, stack := v35 :: word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: word11 :: word12 :: v34 :: rest} = some {s with pc := UInt256.ofNat 7619, memory := v31, stack := word0 :: word1 :: word2 :: v0 :: word4 :: word5 :: word6 :: word7 :: word8 :: v21 :: word10 :: v35 :: word12 :: v34 :: rest} := by
    simpa only [squareColumn14part12Model] using squareColumn14part12_run ({s with memory := v31}) (v35) (word0) (word1) (word2) (v0) (word4) (word5) (word6) (word7) (word8) (v21) (word10) (word11) (word12) (v34) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms squareColumn14_run

end CycleSubmission.Execution

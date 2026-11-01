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

def squareColumn13part0Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def squareColumn13part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x14 * x8
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7371, memory := s.memory, stack := x7 :: x10 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn13part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part0Program {s with pc := UInt256.ofNat 7363, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn13part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part0Program, squareColumn13part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part0_run

def squareColumn13part1Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def squareColumn13part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x12 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x10 x7 x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7379, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn13part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part1Program {s with pc := UInt256.ofNat 7371, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn13part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part1Program, squareColumn13part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part1_run

def squareColumn13part2Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def squareColumn13part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x3 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 7387, memory := s.memory, stack := x13 :: x7 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn13part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part2Program {s with pc := UInt256.ofNat 7379, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn13part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part2Program, squareColumn13part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part2_run

def squareColumn13part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MSTORE]

def squareColumn13part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 64
  {s with pc := UInt256.ofNat 7396, memory := v3, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn13part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part3Program {s with pc := UInt256.ofNat 7387, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn13part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn13part3Program, squareColumn13part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]

#print axioms squareColumn13part3_run

def squareColumn13part4Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD]

def squareColumn13part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 - x0
  let v1 : UInt256 := x9 + v0
  let v2 : UInt256 := UInt256.mulMod v1 (UInt256.ofNat 2048) x9
  {s with pc := UInt256.ofNat 7411, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn13part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part4Program {s with pc := UInt256.ofNat 7396, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn13part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part4Program, squareColumn13part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part4_run

def squareColumn13part5Program : List Instr :=
  [.push 2 832,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def squareColumn13part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 832
  let v1 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 7422, memory := s.memory, stack := v1 :: x8 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem squareColumn13part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part5Program {s with pc := UInt256.ofNat 7411, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (squareColumn13part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn13part5Program, squareColumn13part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha832, hf832]

#print axioms squareColumn13part5_run

def squareColumn13part6Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn13part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x0
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := UInt256.mulMod x2 x0 x1
  {s with pc := UInt256.ofNat 7430, memory := s.memory, stack := v2 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn13part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part6Program {s with pc := UInt256.ofNat 7422, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn13part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part6Program, squareColumn13part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part6_run

def squareColumn13part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn13part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x3 + v0
  let v2 : UInt256 := x3 + x2
  let v3 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 7439, memory := s.memory, stack := v3 :: v3 :: v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn13part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part7Program {s with pc := UInt256.ofNat 7430, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn13part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn13part7Program, squareColumn13part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]

#print axioms squareColumn13part7_run

def squareColumn13part8Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn13part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x12 * x7
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7447, memory := s.memory, stack := x10 :: x13 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn13part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part8Program {s with pc := UInt256.ofNat 7439, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn13part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part8Program, squareColumn13part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part8_run

def squareColumn13part9Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn13part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x15 * x5
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7455, memory := s.memory, stack := x11 :: x3 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn13part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part9Program {s with pc := UInt256.ofNat 7447, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn13part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part9Program, squareColumn13part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part9_run

def squareColumn13part10Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn13part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.mulMod v0 v0 x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 7464, memory := s.memory, stack := x11 :: x6 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn13part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part10Program {s with pc := UInt256.ofNat 7455, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn13part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn13part10Program, squareColumn13part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]

#print axioms squareColumn13part10_run

def squareColumn13part11Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn13part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod x11 x14 x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7472, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn13part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part11Program {s with pc := UInt256.ofNat 7464, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn13part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part11Program, squareColumn13part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part11_run

def squareColumn13part12Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn13part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x14 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.land x13 x2
  {s with pc := UInt256.ofNat 7480, memory := s.memory, stack := v2 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn13part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part12Program {s with pc := UInt256.ofNat 7472, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn13part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part12Program, squareColumn13part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part12_run

def squareColumn13part13Program : List Instr :=
  [.push 1 96,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn13part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 96
  let v1 : UInt256 := x2 - x1
  let v2 : UInt256 := x10 + v1
  {s with pc := UInt256.ofNat 7496, memory := v0, stack := x10 :: (UInt256.ofNat 2048) :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn13part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part13Program {s with pc := UInt256.ofNat 7480, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn13part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn13part13Program, squareColumn13part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]

#print axioms squareColumn13part13_run

def squareColumn13part14Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .MULMOD]

def squareColumn13part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x2 x1 x0
  {s with pc := UInt256.ofNat 7498, memory := s.memory, stack := v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn13part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13part14Program {s with pc := UInt256.ofNat 7496, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn13part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn13part14Program, squareColumn13part14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms squareColumn13part14_run

def squareColumn13Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 832,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
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
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
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
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD]

def squareColumn13Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := word13 * word7
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := UInt256.mulMod word10 word6 word9
  let v4 : UInt256 := v3 + word1
  let v5 : UInt256 := UInt256.mulMod word8 word5 word9
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod word11 word3 word9
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod word13 word7 word9
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.land word12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : UInt256 := v10 - v11
  let v14 : UInt256 := word9 + v13
  let v15 : UInt256 := UInt256.mulMod v14 (UInt256.ofNat 2048) word9
  let v16 : UInt256 := MachineState.readWord v12 832
  let v17 : UInt256 := MachineState.readWord v12 128
  let v18 : UInt256 := word15 * v17
  let v19 : UInt256 := v18 + v18
  let v20 : UInt256 := UInt256.mulMod word15 v17 word9
  let v21 : UInt256 := v20 + v20
  let v22 : UInt256 := v15 + v21
  let v23 : UInt256 := v15 + v19
  let v24 : UInt256 := MachineState.readWord v12 160
  let v25 : UInt256 := v24 * v24
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := word10 * word5
  let v28 : UInt256 := v27 + v26
  let v29 : UInt256 := word8 * word11
  let v30 : UInt256 := v29 + v28
  let v31 : UInt256 := word13 * word3
  let v32 : UInt256 := v31 + v30
  let v33 : UInt256 := MachineState.readWord v12 160
  let v34 : UInt256 := UInt256.mulMod v33 v33 word9
  let v35 : UInt256 := v34 + v22
  let v36 : UInt256 := UInt256.mulMod word10 word5 word9
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := UInt256.mulMod word8 word11 word9
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := UInt256.mulMod word3 word13 word9
  let v41 : UInt256 := v40 + v39
  let v42 : UInt256 := UInt256.land word12 v32
  let v43 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v42.toNat 32) 96
  let v44 : UInt256 := v41 - v42
  let v45 : UInt256 := word9 + v44
  let v46 : UInt256 := UInt256.mulMod v45 (UInt256.ofNat 2048) word9
  {s with pc := UInt256.ofNat 7498, memory := v43, stack := v46 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest}

theorem squareColumn13_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13Program {s with pc := UInt256.ofNat 7363, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} =
      some (squareColumn13Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 rest) := by
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := word13 * word7
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := UInt256.mulMod word10 word6 word9
  let v4 : UInt256 := v3 + word1
  let v5 : UInt256 := UInt256.mulMod word8 word5 word9
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod word11 word3 word9
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod word13 word7 word9
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.land word12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : UInt256 := v10 - v11
  let v14 : UInt256 := word9 + v13
  let v15 : UInt256 := UInt256.mulMod v14 (UInt256.ofNat 2048) word9
  let v16 : UInt256 := MachineState.readWord v12 832
  let v17 : UInt256 := MachineState.readWord v12 128
  let v18 : UInt256 := word15 * v17
  let v19 : UInt256 := v18 + v18
  let v20 : UInt256 := UInt256.mulMod word15 v17 word9
  let v21 : UInt256 := v20 + v20
  let v22 : UInt256 := v15 + v21
  let v23 : UInt256 := v15 + v19
  let v24 : UInt256 := MachineState.readWord v12 160
  let v25 : UInt256 := v24 * v24
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := word10 * word5
  let v28 : UInt256 := v27 + v26
  let v29 : UInt256 := word8 * word11
  let v30 : UInt256 := v29 + v28
  let v31 : UInt256 := word13 * word3
  let v32 : UInt256 := v31 + v30
  let v33 : UInt256 := MachineState.readWord v12 160
  let v34 : UInt256 := UInt256.mulMod v33 v33 word9
  let v35 : UInt256 := v34 + v22
  let v36 : UInt256 := UInt256.mulMod word10 word5 word9
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := UInt256.mulMod word8 word11 word9
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := UInt256.mulMod word3 word13 word9
  let v41 : UInt256 := v40 + v39
  let v42 : UInt256 := UInt256.land word12 v32
  let v43 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v42.toNat 32) 96
  let v44 : UInt256 := v41 - v42
  let v45 : UInt256 := word9 + v44
  let v46 : UInt256 := UInt256.mulMod v45 (UInt256.ofNat 2048) word9
  have h0 : runInstructions squareColumn13part0Program {s with pc := UInt256.ofNat 7363, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7371, memory := s.memory, stack := word6 :: word9 :: word1 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part0Model, v0, v1, v2] using squareColumn13part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h1 : runInstructions squareColumn13part1Program {s with pc := UInt256.ofNat 7371, memory := s.memory, stack := word6 :: word9 :: word1 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7379, memory := s.memory, stack := v6 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part1Model, v3, v4, v5, v6] using squareColumn13part1_run (s) (word6) (word9) (word1) (v2) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h2 : runInstructions squareColumn13part2Program {s with pc := UInt256.ofNat 7379, memory := s.memory, stack := v6 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7387, memory := s.memory, stack := word13 :: word7 :: word9 :: v8 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part2Model, v7, v8] using squareColumn13part2_run (s) (v6) (v2) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h3 : runInstructions squareColumn13part3Program {s with pc := UInt256.ofNat 7387, memory := s.memory, stack := word13 :: word7 :: word9 :: v8 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7396, memory := v12, stack := v11 :: v10 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part3Model, v9, v10, v11, v12] using squareColumn13part3_run (s) (word13) (word7) (word9) (v8) (v2) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h4 : runInstructions squareColumn13part4Program {s with pc := UInt256.ofNat 7396, memory := v12, stack := v11 :: v10 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7411, memory := v12, stack := v15 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part4Model, v13, v14, v15] using squareColumn13part4_run ({s with memory := v12}) (v11) (v10) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h5 : runInstructions squareColumn13part5Program {s with pc := UInt256.ofNat 7411, memory := v12, stack := v15 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7422, memory := v12, stack := v17 :: word9 :: word15 :: v15 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part5Model, v16, v17] using squareColumn13part5_run ({s with memory := v12}) (v15) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h6 : runInstructions squareColumn13part6Program {s with pc := UInt256.ofNat 7422, memory := v12, stack := v17 :: word9 :: word15 :: v15 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7430, memory := v12, stack := v20 :: v20 :: v19 :: v15 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part6Model, v18, v19, v20] using squareColumn13part6_run ({s with memory := v12}) (v17) (word9) (word15) (v15) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h7 : runInstructions squareColumn13part7Program {s with pc := UInt256.ofNat 7430, memory := v12, stack := v20 :: v20 :: v19 :: v15 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7439, memory := v12, stack := v24 :: v24 :: v23 :: v22 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part7Model, v21, v22, v23, v24] using squareColumn13part7_run ({s with memory := v12}) (v20) (v20) (v19) (v15) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h8 : runInstructions squareColumn13part8Program {s with pc := UInt256.ofNat 7439, memory := v12, stack := v24 :: v24 :: v23 :: v22 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7447, memory := v12, stack := word8 :: word11 :: v28 :: v22 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part8Model, v25, v26, v27, v28] using squareColumn13part8_run ({s with memory := v12}) (v24) (v24) (v23) (v22) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h9 : runInstructions squareColumn13part9Program {s with pc := UInt256.ofNat 7447, memory := v12, stack := word8 :: word11 :: v28 :: v22 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7455, memory := v12, stack := word9 :: v22 :: v32 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part9Model, v29, v30, v31, v32] using squareColumn13part9_run ({s with memory := v12}) (word8) (word11) (v28) (v22) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h10 : runInstructions squareColumn13part10Program {s with pc := UInt256.ofNat 7455, memory := v12, stack := word9 :: v22 :: v32 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7464, memory := v12, stack := word10 :: word5 :: word9 :: v35 :: v32 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part10Model, v33, v34, v35] using squareColumn13part10_run ({s with memory := v12}) (word9) (v22) (v32) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h11 : runInstructions squareColumn13part11Program {s with pc := UInt256.ofNat 7464, memory := v12, stack := word10 :: word5 :: word9 :: v35 :: v32 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7472, memory := v12, stack := word9 :: v39 :: v32 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part11Model, v36, v37, v38, v39] using squareColumn13part11_run ({s with memory := v12}) (word10) (word5) (word9) (v35) (v32) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h12 : runInstructions squareColumn13part12Program {s with pc := UInt256.ofNat 7472, memory := v12, stack := word9 :: v39 :: v32 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7480, memory := v12, stack := v42 :: v42 :: v41 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part12Model, v40, v41, v42] using squareColumn13part12_run ({s with memory := v12}) (word9) (v39) (v32) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h13 : runInstructions squareColumn13part13Program {s with pc := UInt256.ofNat 7480, memory := v12, stack := v42 :: v42 :: v41 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7496, memory := v43, stack := word9 :: (UInt256.ofNat 2048) :: v45 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part13Model, v43, v44, v45] using squareColumn13part13_run ({s with memory := v12}) (v42) (v42) (v41) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h14 : runInstructions squareColumn13part14Program {s with pc := UInt256.ofNat 7496, memory := v43, stack := word9 :: (UInt256.ofNat 2048) :: v45 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7498, memory := v43, stack := v46 :: word2 :: word3 :: word4 :: word5 :: v16 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn13part14Model, v46] using squareColumn13part14_run ({s with memory := v43}) (word9) ((UInt256.ofNat 2048)) (v45) (word2) (word3) (word4) (word5) (v16) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))

#print axioms squareColumn13_run

end CycleSubmission.Execution

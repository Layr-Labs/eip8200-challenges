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

def productColumn12part0Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn12part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  let v3 : UInt256 := UInt256.mulMod x7 v2 x12
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 9294, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn12part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part0Program {s with pc := UInt256.ofNat 9284, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn12part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part0Program, productColumn12part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]

#print axioms productColumn12part0_run

def productColumn12part1Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def productColumn12part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x14 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 9302, memory := s.memory, stack := x15 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn12part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part1Program {s with pc := UInt256.ofNat 9294, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn12part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn12part1Program, productColumn12part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn12part1_run

def productColumn12part2Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD]

def productColumn12part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1280
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  let v3 : UInt256 := UInt256.mulMod x13 x15 x11
  {s with pc := UInt256.ofNat 9312, memory := s.memory, stack := v3 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn12part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part2Program {s with pc := UInt256.ofNat 9302, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn12part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part2Program, productColumn12part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]

#print axioms productColumn12part2_run

def productColumn12part3Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 768,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩)]

def productColumn12part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.land x13 x2
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  {s with pc := UInt256.ofNat 9322, memory := v2, stack := v0 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn12part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part3Program {s with pc := UInt256.ofNat 9312, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn12part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part3Program, productColumn12part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768]

#print axioms productColumn12part3_run

def productColumn12part4Program : List Instr :=
  [.op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 1280,
   .op .MLOAD]

def productColumn12part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := x9 + v0
  let v2 : UInt256 := UInt256.mulMod v1 (UInt256.ofNat 2048) x9
  let v3 : UInt256 := MachineState.readWord s.memory 1280
  {s with pc := UInt256.ofNat 9340, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn12part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part4Program {s with pc := UInt256.ofNat 9322, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn12part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part4Program, productColumn12part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]

#print axioms productColumn12part4_run

def productColumn12part5Program : List Instr :=
  [.op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def productColumn12part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2048
  {s with pc := UInt256.ofNat 9350, memory := s.memory, stack := x6 :: v0 :: x9 :: x1 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn12part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part5Program {s with pc := UInt256.ofNat 9340, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn12part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : UInt256).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part5Program, productColumn12part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2048, hf2048]

#print axioms productColumn12part5_run

def productColumn12part6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩)]

def productColumn12part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := x10 * x4
  let v3 : UInt256 := v2 + x5
  let v4 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 9360, memory := s.memory, stack := v1 :: v3 :: x6 :: x7 :: x8 :: x9 :: v4 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn12part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part6Program {s with pc := UInt256.ofNat 9350, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn12part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part6Program, productColumn12part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]

#print axioms productColumn12part6_run

def productColumn12part7Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn12part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := MachineState.readWord s.memory 2016
  {s with pc := UInt256.ofNat 9371, memory := s.memory, stack := v1 :: v0 :: x1 :: v0 :: x9 :: x0 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn12part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part7Program {s with pc := UInt256.ofNat 9360, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn12part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : UInt256).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part7Program, productColumn12part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha2016, hf2016]

#print axioms productColumn12part7_run

def productColumn12part8Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD]

def productColumn12part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x6 x3 x4
  let v3 : UInt256 := v2 + x5
  let v4 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 9380, memory := s.memory, stack := v4 :: x14 :: v3 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn12part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part8Program {s with pc := UInt256.ofNat 9371, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn12part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part8Program, productColumn12part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]

#print axioms productColumn12part8_run

def productColumn12part9Program : List Instr :=
  [.push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn12part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1984
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x3
  {s with pc := UInt256.ofNat 9390, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn12part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part9Program {s with pc := UInt256.ofNat 9380, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn12part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1984 : (1984 : UInt256).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part9Program, productColumn12part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1984, hf1984]

#print axioms productColumn12part9_run

def productColumn12part10Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn12part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := MachineState.readWord s.memory 1952
  {s with pc := UInt256.ofNat 9401, memory := s.memory, stack := x4 :: v2 :: x12 :: v1 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn12part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part10Program {s with pc := UInt256.ofNat 9390, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn12part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : UInt256).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part10Program, productColumn12part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha1952, hf1952]

#print axioms productColumn12part10_run

def productColumn12part11Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn12part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x4 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 9409, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn12part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part11Program {s with pc := UInt256.ofNat 9401, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn12part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn12part11Program, productColumn12part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn12part11_run

def productColumn12part12Program : List Instr :=
  [.push 1 128,
   .op .MLOAD]

def productColumn12part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 9412, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn12part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12part12Program {s with pc := UInt256.ofNat 9409, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn12part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn12part12Program, productColumn12part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]

#print axioms productColumn12part12_run

def productColumn12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 768,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
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
   .push 1 64,
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
   .push 1 96,
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
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def productColumn12Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod carry word0 word1
  let v1 : UInt256 := v0 + word2
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  let v3 : UInt256 := UInt256.mulMod word6 v2 word11
  let v4 : UInt256 := v3 + v1
  let v5 : UInt256 := UInt256.mulMod word7 word16 word11
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := MachineState.readWord s.memory 1280
  let v8 : UInt256 := UInt256.mulMod v7 word17 word11
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := UInt256.mulMod word13 word15 word11
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.land word14 word3
  let v13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v12.toNat 32) 768
  let v14 : UInt256 := v11 - v12
  let v15 : UInt256 := word11 + v14
  let v16 : UInt256 := UInt256.mulMod v15 (UInt256.ofNat 2048) word11
  let v17 : UInt256 := MachineState.readWord v13 1280
  let v18 : UInt256 := MachineState.readWord v13 2048
  let v19 : UInt256 := UInt256.mulMod word8 v18 word11
  let v20 : UInt256 := v19 + v16
  let v21 : UInt256 := word8 * v18
  let v22 : UInt256 := v21 + v16
  let v23 : UInt256 := MachineState.readWord v13 1216
  let v24 : UInt256 := MachineState.readWord v13 32
  let v25 : UInt256 := MachineState.readWord v13 2016
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v22
  let v28 : UInt256 := UInt256.mulMod v25 v24 word11
  let v29 : UInt256 := v28 + v20
  let v30 : UInt256 := MachineState.readWord v13 64
  let v31 : UInt256 := MachineState.readWord v13 1984
  let v32 : UInt256 := v31 * v30
  let v33 : UInt256 := v32 + v27
  let v34 : UInt256 := UInt256.mulMod v31 v30 word11
  let v35 : UInt256 := v34 + v29
  let v36 : UInt256 := MachineState.readWord v13 96
  let v37 : UInt256 := MachineState.readWord v13 1952
  let v38 : UInt256 := v37 * v36
  let v39 : UInt256 := v38 + v33
  let v40 : UInt256 := UInt256.mulMod v37 v36 word11
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := MachineState.readWord v13 128
  {s with pc := UInt256.ofNat 9412, memory := v13, stack := v42 :: word11 :: v41 :: v39 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest}

theorem productColumn12_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12Program {s with pc := UInt256.ofNat 9284, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} =
      some (productColumn12Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 rest) := by
  let v0 : UInt256 := UInt256.mulMod carry word0 word1
  let v1 : UInt256 := v0 + word2
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  let v3 : UInt256 := UInt256.mulMod word6 v2 word11
  let v4 : UInt256 := v3 + v1
  let v5 : UInt256 := UInt256.mulMod word7 word16 word11
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := MachineState.readWord s.memory 1280
  let v8 : UInt256 := UInt256.mulMod v7 word17 word11
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := UInt256.mulMod word13 word15 word11
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.land word14 word3
  let v13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v12.toNat 32) 768
  let v14 : UInt256 := v11 - v12
  let v15 : UInt256 := word11 + v14
  let v16 : UInt256 := UInt256.mulMod v15 (UInt256.ofNat 2048) word11
  let v17 : UInt256 := MachineState.readWord v13 1280
  let v18 : UInt256 := MachineState.readWord v13 2048
  let v19 : UInt256 := UInt256.mulMod word8 v18 word11
  let v20 : UInt256 := v19 + v16
  let v21 : UInt256 := word8 * v18
  let v22 : UInt256 := v21 + v16
  let v23 : UInt256 := MachineState.readWord v13 1216
  let v24 : UInt256 := MachineState.readWord v13 32
  let v25 : UInt256 := MachineState.readWord v13 2016
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v22
  let v28 : UInt256 := UInt256.mulMod v25 v24 word11
  let v29 : UInt256 := v28 + v20
  let v30 : UInt256 := MachineState.readWord v13 64
  let v31 : UInt256 := MachineState.readWord v13 1984
  let v32 : UInt256 := v31 * v30
  let v33 : UInt256 := v32 + v27
  let v34 : UInt256 := UInt256.mulMod v31 v30 word11
  let v35 : UInt256 := v34 + v29
  let v36 : UInt256 := MachineState.readWord v13 96
  let v37 : UInt256 := MachineState.readWord v13 1952
  let v38 : UInt256 := v37 * v36
  let v39 : UInt256 := v38 + v33
  let v40 : UInt256 := UInt256.mulMod v37 v36 word11
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := MachineState.readWord v13 128
  have h0 : runInstructions productColumn12part0Program {s with pc := UInt256.ofNat 9284, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9294, memory := s.memory, stack := v4 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part0Model, v0, v1, v2, v3, v4] using productColumn12part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h1 : runInstructions productColumn12part1Program {s with pc := UInt256.ofNat 9294, memory := s.memory, stack := v4 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9302, memory := s.memory, stack := word17 :: word11 :: v6 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part1Model, v5, v6] using productColumn12part1_run (s) (v4) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h2 : runInstructions productColumn12part2Program {s with pc := UInt256.ofNat 9302, memory := s.memory, stack := word17 :: word11 :: v6 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9312, memory := s.memory, stack := v10 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part2Model, v7, v8, v9, v10] using productColumn12part2_run (s) (word17) (word11) (v6) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h3 : runInstructions productColumn12part3Program {s with pc := UInt256.ofNat 9312, memory := s.memory, stack := v10 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9322, memory := v13, stack := v11 :: v12 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part3Model, v11, v12, v13] using productColumn12part3_run (s) (v10) (v9) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h4 : runInstructions productColumn12part4Program {s with pc := UInt256.ofNat 9322, memory := v13, stack := v11 :: v12 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9340, memory := v13, stack := v17 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part4Model, v14, v15, v16, v17] using productColumn12part4_run ({s with memory := v13}) (v11) (v12) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h5 : runInstructions productColumn12part5Program {s with pc := UInt256.ofNat 9340, memory := v13, stack := v17 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9350, memory := v13, stack := word8 :: v18 :: word11 :: v16 :: v18 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part5Model, v18] using productColumn12part5_run ({s with memory := v13}) (v17) (v16) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h6 : runInstructions productColumn12part6Program {s with pc := UInt256.ofNat 9350, memory := v13, stack := word8 :: v18 :: word11 :: v16 :: v18 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9360, memory := v13, stack := v20 :: v22 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part6Model, v19, v20, v21, v22, v23] using productColumn12part6_run ({s with memory := v13}) (word8) (v18) (word11) (v16) (v18) (v16) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v17) (word14) (word15) (word16) (word17) rest hcap hact
  have h7 : runInstructions productColumn12part7Program {s with pc := UInt256.ofNat 9360, memory := v13, stack := v20 :: v22 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9371, memory := v13, stack := v25 :: v24 :: v22 :: v24 :: word11 :: v20 :: v25 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part7Model, v24, v25] using productColumn12part7_run ({s with memory := v13}) (v20) (v22) (word4) (word5) (word6) (word7) (v23) (word9) (word10) (word11) (word12) (v17) (word14) (word15) (word16) (word17) rest hcap hact
  have h8 : runInstructions productColumn12part8Program {s with pc := UInt256.ofNat 9371, memory := v13, stack := v25 :: v24 :: v22 :: v24 :: word11 :: v20 :: v25 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9380, memory := v13, stack := v30 :: word11 :: v29 :: v27 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part8Model, v26, v27, v28, v29, v30] using productColumn12part8_run ({s with memory := v13}) (v25) (v24) (v22) (v24) (word11) (v20) (v25) (word4) (word5) (word6) (word7) (v23) (word9) (word10) (word11) (word12) (v17) (word14) (word15) (word16) (word17) rest hcap hact
  have h9 : runInstructions productColumn12part9Program {s with pc := UInt256.ofNat 9380, memory := v13, stack := v30 :: word11 :: v29 :: v27 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9390, memory := v13, stack := v31 :: v30 :: word11 :: v29 :: v33 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part9Model, v31, v32, v33] using productColumn12part9_run ({s with memory := v13}) (v30) (word11) (v29) (v27) (word4) (word5) (word6) (word7) (v23) (word9) (word10) (word11) (word12) (v17) (word14) (word15) (word16) (word17) rest hcap hact
  have h10 : runInstructions productColumn12part10Program {s with pc := UInt256.ofNat 9390, memory := v13, stack := v31 :: v30 :: word11 :: v29 :: v33 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9401, memory := v13, stack := v33 :: v36 :: word11 :: v35 :: v37 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part10Model, v34, v35, v36, v37] using productColumn12part10_run ({s with memory := v13}) (v31) (v30) (word11) (v29) (v33) (word4) (word5) (word6) (word7) (v23) (word9) (word10) (word11) (word12) (v17) (word14) (word15) (word16) (word17) rest hcap hact
  have h11 : runInstructions productColumn12part11Program {s with pc := UInt256.ofNat 9401, memory := v13, stack := v33 :: v36 :: word11 :: v35 :: v37 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9409, memory := v13, stack := word11 :: v41 :: v39 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part11Model, v38, v39, v40, v41] using productColumn12part11_run ({s with memory := v13}) (v33) (v36) (word11) (v35) (v37) (word4) (word5) (word6) (word7) (v23) (word9) (word10) (word11) (word12) (v17) (word14) (word15) (word16) (word17) rest hcap hact
  have h12 : runInstructions productColumn12part12Program {s with pc := UInt256.ofNat 9409, memory := v13, stack := word11 :: v41 :: v39 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 9412, memory := v13, stack := v42 :: word11 :: v41 :: v39 :: word4 :: word5 :: word6 :: word7 :: v23 :: word9 :: word10 :: word11 :: word12 :: v17 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [productColumn12part12Model, v42] using productColumn12part12_run ({s with memory := v13}) (word11) (v41) (v39) (word4) (word5) (word6) (word7) (v23) (word9) (word10) (word11) (word12) (v17) (word14) (word15) (word16) (word17) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms productColumn12_run

end CycleSubmission.Execution

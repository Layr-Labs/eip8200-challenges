import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.ExecPrologue
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word (succ_ofNat_mod ofNat_add_mod ofNat_sub_ofNat literal_eq_ofNat)
open Challenge.EvmProof.Stepper (runInstr)
open Challenge.Modexp.Submission.Proofs.Fast.Exp (activeWords_fix)

private theorem hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
private theorem hzn : ({val := 0} : UInt256).toNat = 0 := rfl

/-! ## pro: pc 5334..5344, 8 instructions -/

def propart0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 16,
   .op .SHL,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 192,
   .op .MSTORE]

def propart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x11 (UInt256.ofNat 16)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  {s with pc := UInt256.ofNat 5344, memory := v1, stack := v0 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem propart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions propart0Program {s with pc := UInt256.ofNat 5334, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (propart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, propart0Program, propart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha192, hf192]

def proProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 16,
   .op .SHL,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 192,
   .op .MSTORE]

def proModel (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft f11 (UInt256.ofNat 16)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  {s with pc := UInt256.ofNat 5344, memory := v1, stack := v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest}

theorem pro_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions proProgram {s with pc := UInt256.ofNat 5334, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} =
      some (proModel s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
  let v0 : UInt256 := UInt256.shiftLeft f11 (UInt256.ofNat 16)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  have h0 : runInstructions propart0Program {s with pc := UInt256.ofNat 5334, memory := s.memory, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5344, memory := v1, stack := v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [propart0Model, v0, v1] using propart0_run (s) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  exact h0

def pro_o0 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  (UInt256.shiftLeft f11 (UInt256.ofNat 16))

def pro_mem (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.shiftLeft f11 (UInt256.ofNat 16)).toNat 32) 192)

theorem pro_eq (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) :
    proModel s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest =
      {s with pc := UInt256.ofNat 5344, memory := pro_mem s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15, stack := (pro_o0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
  simp only [proModel, pro_mem, pro_o0]

/-! ## blk5344: pc 5344..5352, 6 instructions -/

def blk5344part0Program : List Instr :=
  [.push 0 0,
   .op .NOT,
   .push 1 16,
   .op .SHR,
   .push 1 224,
   .op .MSTORE]

def blk5344part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 224
  {s with pc := UInt256.ofNat 5352, memory := v2, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem blk5344part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5344part0Program {s with pc := UInt256.ofNat 5344, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (blk5344part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5344part0Program, blk5344part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def blk5344Program : List Instr :=
  [.push 0 0,
   .op .NOT,
   .push 1 16,
   .op .SHR,
   .push 1 224,
   .op .MSTORE]

def blk5344Model (s : State) (p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 224
  {s with pc := UInt256.ofNat 5352, memory := v2, stack := p1_0 :: p1_1 :: p1_2 :: p1_3 :: p1_4 :: p1_5 :: p1_6 :: p1_7 :: p1_8 :: p1_9 :: p1_10 :: p1_11 :: p1_12 :: p1_13 :: p1_14 :: p1_15 :: p1_16 :: p1_17 :: rest}

theorem blk5344_run (s : State) (p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5344Program {s with pc := UInt256.ofNat 5344, stack := p1_0 :: p1_1 :: p1_2 :: p1_3 :: p1_4 :: p1_5 :: p1_6 :: p1_7 :: p1_8 :: p1_9 :: p1_10 :: p1_11 :: p1_12 :: p1_13 :: p1_14 :: p1_15 :: p1_16 :: p1_17 :: rest} =
      some (blk5344Model s p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 rest) := by
  let v0 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 224
  have h0 : runInstructions blk5344part0Program {s with pc := UInt256.ofNat 5344, memory := s.memory, stack := p1_0 :: p1_1 :: p1_2 :: p1_3 :: p1_4 :: p1_5 :: p1_6 :: p1_7 :: p1_8 :: p1_9 :: p1_10 :: p1_11 :: p1_12 :: p1_13 :: p1_14 :: p1_15 :: p1_16 :: p1_17 :: rest} = some {s with pc := UInt256.ofNat 5352, memory := v2, stack := p1_0 :: p1_1 :: p1_2 :: p1_3 :: p1_4 :: p1_5 :: p1_6 :: p1_7 :: p1_8 :: p1_9 :: p1_10 :: p1_11 :: p1_12 :: p1_13 :: p1_14 :: p1_15 :: p1_16 :: p1_17 :: rest} := by
    simpa only [blk5344part0Model, v0, v1, v2] using blk5344part0_run (s) p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 rest hcap hact
  exact h0

def blk5344_mem (mem : ByteArray) (p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.shiftRight (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 16)).toNat 32) 224)

theorem blk5344_eq (s : State) (p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 : UInt256) (rest : List UInt256) :
    blk5344Model s p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 rest =
      {s with pc := UInt256.ofNat 5352, memory := blk5344_mem s.memory p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17, stack := p1_0 :: p1_1 :: p1_2 :: p1_3 :: p1_4 :: p1_5 :: p1_6 :: p1_7 :: p1_8 :: p1_9 :: p1_10 :: p1_11 :: p1_12 :: p1_13 :: p1_14 :: p1_15 :: p1_16 :: p1_17 :: rest} := by
  simp only [blk5344Model, blk5344_mem]

/-! ## blk5352: pc 5352..5393, 30 instructions -/

def blk5352part0Program : List Instr :=
  [.push 0 0,
   .op .NOT,
   .push 1 5,
   .op .SHR,
   .push 0 0,
   .op .MLOAD,
   .push 1 192,
   .op .SHR]

def blk5352part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 192)
  {s with pc := UInt256.ofNat 5362, memory := s.memory, stack := v3 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem blk5352part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5352part0Program {s with pc := UInt256.ofNat 5352, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (blk5352part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5352part0Program, blk5352part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def blk5352part1Program : List Instr :=
  [.push 1 6,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 36,
   .op .MLOAD]

def blk5352part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 6
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : UInt256 := MachineState.readWord s.memory 36
  {s with pc := UInt256.ofNat 5372, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem blk5352part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5352part1Program {s with pc := UInt256.ofNat 5362, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (blk5352part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 35) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha6 : (6 : UInt256).toNat = 6 := rfl
  have hf6 := activeWords_fix s 6 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha36 : (36 : UInt256).toNat = 36 := rfl
  have hf36 := activeWords_fix s 36 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5352part1Program, blk5352part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha6, hf6, ha224, hf224, ha36, hf36]

def blk5352part2Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 66,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND]

def blk5352part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.land v0 x0
  let v2 : UInt256 := MachineState.readWord s.memory 66
  let v3 : UInt256 := MachineState.readWord s.memory 224
  let v4 : UInt256 := UInt256.land v3 v2
  {s with pc := UInt256.ofNat 5383, memory := s.memory, stack := v4 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest}

theorem blk5352part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5352part2Program {s with pc := UInt256.ofNat 5372, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest} =
      some (blk5352part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 rest) := by
  have hc (j : Nat) (hj : j ≤ 37) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha66 : (66 : UInt256).toNat = 66 := rfl
  have hf66 := activeWords_fix s 66 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5352part2Program, blk5352part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224, ha66, hf66]

def blk5352part3Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 160,
   .op .MSTORE]

def blk5352part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 160
  {s with pc := UInt256.ofNat 5393, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem blk5352part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5352part3Program {s with pc := UInt256.ofNat 5383, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (blk5352part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hc (j : Nat) (hj : j ≤ 38) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5352part3Program, blk5352part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96, ha224, hf224, ha160, hf160]

def blk5352Program : List Instr :=
  [.push 0 0,
   .op .NOT,
   .push 1 5,
   .op .SHR,
   .push 0 0,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 6,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 36,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 66,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 96,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 160,
   .op .MSTORE]

def blk5352Model (s : State) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 192)
  let v4 : UInt256 := MachineState.readWord s.memory 6
  let v5 : UInt256 := MachineState.readWord s.memory 224
  let v6 : UInt256 := UInt256.land v5 v4
  let v7 : UInt256 := MachineState.readWord s.memory 36
  let v8 : UInt256 := MachineState.readWord s.memory 224
  let v9 : UInt256 := UInt256.land v8 v7
  let v10 : UInt256 := MachineState.readWord s.memory 66
  let v11 : UInt256 := MachineState.readWord s.memory 224
  let v12 : UInt256 := UInt256.land v11 v10
  let v13 : UInt256 := MachineState.readWord s.memory 96
  let v14 : UInt256 := MachineState.readWord s.memory 224
  let v15 : UInt256 := UInt256.land v14 v13
  let v16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v15.toNat 32) 160
  {s with pc := UInt256.ofNat 5393, memory := v16, stack := v12 :: v9 :: v6 :: v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest}

theorem blk5352_run (s : State) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5352Program {s with pc := UInt256.ofNat 5352, stack := p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} =
      some (blk5352Model s p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 rest) := by
  let v0 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 192)
  let v4 : UInt256 := MachineState.readWord s.memory 6
  let v5 : UInt256 := MachineState.readWord s.memory 224
  let v6 : UInt256 := UInt256.land v5 v4
  let v7 : UInt256 := MachineState.readWord s.memory 36
  let v8 : UInt256 := MachineState.readWord s.memory 224
  let v9 : UInt256 := UInt256.land v8 v7
  let v10 : UInt256 := MachineState.readWord s.memory 66
  let v11 : UInt256 := MachineState.readWord s.memory 224
  let v12 : UInt256 := UInt256.land v11 v10
  let v13 : UInt256 := MachineState.readWord s.memory 96
  let v14 : UInt256 := MachineState.readWord s.memory 224
  let v15 : UInt256 := UInt256.land v14 v13
  let v16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v15.toNat 32) 160
  have h0 : runInstructions blk5352part0Program {s with pc := UInt256.ofNat 5352, memory := s.memory, stack := p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} = some {s with pc := UInt256.ofNat 5362, memory := s.memory, stack := v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} := by
    simpa only [blk5352part0Model, v0, v1, v2, v3] using blk5352part0_run (s) p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 rest hcap hact
  have h1 : runInstructions blk5352part1Program {s with pc := UInt256.ofNat 5362, memory := s.memory, stack := v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} = some {s with pc := UInt256.ofNat 5372, memory := s.memory, stack := v7 :: v6 :: v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} := by
    simpa only [blk5352part1Model, v4, v5, v6, v7] using blk5352part1_run (s) v3 v1 p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 rest hcap hact
  have h2 : runInstructions blk5352part2Program {s with pc := UInt256.ofNat 5372, memory := s.memory, stack := v7 :: v6 :: v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} = some {s with pc := UInt256.ofNat 5383, memory := s.memory, stack := v12 :: v9 :: v6 :: v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} := by
    simpa only [blk5352part2Model, v8, v9, v10, v11, v12] using blk5352part2_run (s) v7 v6 v3 v1 p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 rest hcap hact
  have h3 : runInstructions blk5352part3Program {s with pc := UInt256.ofNat 5383, memory := s.memory, stack := v12 :: v9 :: v6 :: v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} = some {s with pc := UInt256.ofNat 5393, memory := v16, stack := v12 :: v9 :: v6 :: v3 :: v1 :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} := by
    simpa only [blk5352part3Model, v13, v14, v15, v16] using blk5352part3_run (s) v12 v9 v6 v3 v1 p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 h3)))

def blk5352_o0 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) : UInt256 :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 66))

def blk5352_o1 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) : UInt256 :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 36))

def blk5352_o2 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) : UInt256 :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 6))

def blk5352_o3 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) : UInt256 :=
  (UInt256.shiftRight (MachineState.readWord mem 0) (UInt256.ofNat 192))

def blk5352_o4 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) : UInt256 :=
  (UInt256.shiftRight (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 5))

def blk5352_mem (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 96)).toNat 32) 160)

theorem blk5352_eq (s : State) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : UInt256) (rest : List UInt256) :
    blk5352Model s p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 rest =
      {s with pc := UInt256.ofNat 5393, memory := blk5352_mem s.memory p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17, stack := (blk5352_o0 s.memory p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17) :: (blk5352_o1 s.memory p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17) :: (blk5352_o2 s.memory p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17) :: (blk5352_o3 s.memory p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17) :: (blk5352_o4 s.memory p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17) :: p2_0 :: p2_1 :: p2_2 :: p2_3 :: p2_4 :: p2_5 :: p2_6 :: p2_7 :: p2_8 :: p2_9 :: p2_10 :: p2_11 :: p2_12 :: p2_13 :: p2_14 :: p2_15 :: p2_16 :: p2_17 :: rest} := by
  simp only [blk5352Model, blk5352_mem, blk5352_o0, blk5352_o1, blk5352_o2, blk5352_o3, blk5352_o4]

/-! ## blk5393: pc 5393..5403, 7 instructions -/

def blk5393part0Program : List Instr :=
  [.push 2 352,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 0 0,
   .op .MSTORE]

def blk5393part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 352
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 0
  {s with pc := UInt256.ofNat 5403, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem blk5393part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5393part0Program {s with pc := UInt256.ofNat 5393, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (blk5393part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hc (j : Nat) (hj : j ≤ 38) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha352 : (352 : UInt256).toNat = 352 := rfl
  have hf352 := activeWords_fix s 352 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5393part0Program, blk5393part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha352, hf352, ha224, hf224, ha0, hf0]

def blk5393Program : List Instr :=
  [.push 2 352,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 0 0,
   .op .MSTORE]

def blk5393Model (s : State) (p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 352
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 0
  {s with pc := UInt256.ofNat 5403, memory := v3, stack := p3_0 :: p3_1 :: p3_2 :: p3_3 :: p3_4 :: p3_5 :: p3_6 :: p3_7 :: p3_8 :: p3_9 :: p3_10 :: p3_11 :: p3_12 :: p3_13 :: p3_14 :: p3_15 :: p3_16 :: p3_17 :: p3_18 :: p3_19 :: p3_20 :: p3_21 :: p3_22 :: rest}

theorem blk5393_run (s : State) (p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5393Program {s with pc := UInt256.ofNat 5393, stack := p3_0 :: p3_1 :: p3_2 :: p3_3 :: p3_4 :: p3_5 :: p3_6 :: p3_7 :: p3_8 :: p3_9 :: p3_10 :: p3_11 :: p3_12 :: p3_13 :: p3_14 :: p3_15 :: p3_16 :: p3_17 :: p3_18 :: p3_19 :: p3_20 :: p3_21 :: p3_22 :: rest} =
      some (blk5393Model s p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 352
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 0
  have h0 : runInstructions blk5393part0Program {s with pc := UInt256.ofNat 5393, memory := s.memory, stack := p3_0 :: p3_1 :: p3_2 :: p3_3 :: p3_4 :: p3_5 :: p3_6 :: p3_7 :: p3_8 :: p3_9 :: p3_10 :: p3_11 :: p3_12 :: p3_13 :: p3_14 :: p3_15 :: p3_16 :: p3_17 :: p3_18 :: p3_19 :: p3_20 :: p3_21 :: p3_22 :: rest} = some {s with pc := UInt256.ofNat 5403, memory := v3, stack := p3_0 :: p3_1 :: p3_2 :: p3_3 :: p3_4 :: p3_5 :: p3_6 :: p3_7 :: p3_8 :: p3_9 :: p3_10 :: p3_11 :: p3_12 :: p3_13 :: p3_14 :: p3_15 :: p3_16 :: p3_17 :: p3_18 :: p3_19 :: p3_20 :: p3_21 :: p3_22 :: rest} := by
    simpa only [blk5393part0Model, v0, v1, v2, v3] using blk5393part0_run (s) p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 rest hcap hact
  exact h0

def blk5393_mem (mem : ByteArray) (p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 352)).toNat 32) 0)

theorem blk5393_eq (s : State) (p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 : UInt256) (rest : List UInt256) :
    blk5393Model s p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 rest =
      {s with pc := UInt256.ofNat 5403, memory := blk5393_mem s.memory p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22, stack := p3_0 :: p3_1 :: p3_2 :: p3_3 :: p3_4 :: p3_5 :: p3_6 :: p3_7 :: p3_8 :: p3_9 :: p3_10 :: p3_11 :: p3_12 :: p3_13 :: p3_14 :: p3_15 :: p3_16 :: p3_17 :: p3_18 :: p3_19 :: p3_20 :: p3_21 :: p3_22 :: rest} := by
  simp only [blk5393Model, blk5393_mem]

/-! ## blk5403: pc 5403..5414, 7 instructions -/

def blk5403part0Program : List Instr :=
  [.push 2 322,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 32,
   .op .MSTORE]

def blk5403part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 322
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 32
  {s with pc := UInt256.ofNat 5414, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem blk5403part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5403part0Program {s with pc := UInt256.ofNat 5403, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (blk5403part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hc (j : Nat) (hj : j ≤ 38) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha322 : (322 : UInt256).toNat = 322 := rfl
  have hf322 := activeWords_fix s 322 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5403part0Program, blk5403part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha322, hf322, ha224, hf224, ha32, hf32]

def blk5403Program : List Instr :=
  [.push 2 322,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 32,
   .op .MSTORE]

def blk5403Model (s : State) (p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 322
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 32
  {s with pc := UInt256.ofNat 5414, memory := v3, stack := p4_0 :: p4_1 :: p4_2 :: p4_3 :: p4_4 :: p4_5 :: p4_6 :: p4_7 :: p4_8 :: p4_9 :: p4_10 :: p4_11 :: p4_12 :: p4_13 :: p4_14 :: p4_15 :: p4_16 :: p4_17 :: p4_18 :: p4_19 :: p4_20 :: p4_21 :: p4_22 :: rest}

theorem blk5403_run (s : State) (p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5403Program {s with pc := UInt256.ofNat 5403, stack := p4_0 :: p4_1 :: p4_2 :: p4_3 :: p4_4 :: p4_5 :: p4_6 :: p4_7 :: p4_8 :: p4_9 :: p4_10 :: p4_11 :: p4_12 :: p4_13 :: p4_14 :: p4_15 :: p4_16 :: p4_17 :: p4_18 :: p4_19 :: p4_20 :: p4_21 :: p4_22 :: rest} =
      some (blk5403Model s p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 322
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 32
  have h0 : runInstructions blk5403part0Program {s with pc := UInt256.ofNat 5403, memory := s.memory, stack := p4_0 :: p4_1 :: p4_2 :: p4_3 :: p4_4 :: p4_5 :: p4_6 :: p4_7 :: p4_8 :: p4_9 :: p4_10 :: p4_11 :: p4_12 :: p4_13 :: p4_14 :: p4_15 :: p4_16 :: p4_17 :: p4_18 :: p4_19 :: p4_20 :: p4_21 :: p4_22 :: rest} = some {s with pc := UInt256.ofNat 5414, memory := v3, stack := p4_0 :: p4_1 :: p4_2 :: p4_3 :: p4_4 :: p4_5 :: p4_6 :: p4_7 :: p4_8 :: p4_9 :: p4_10 :: p4_11 :: p4_12 :: p4_13 :: p4_14 :: p4_15 :: p4_16 :: p4_17 :: p4_18 :: p4_19 :: p4_20 :: p4_21 :: p4_22 :: rest} := by
    simpa only [blk5403part0Model, v0, v1, v2, v3] using blk5403part0_run (s) p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 rest hcap hact
  exact h0

def blk5403_mem (mem : ByteArray) (p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 322)).toNat 32) 32)

theorem blk5403_eq (s : State) (p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 : UInt256) (rest : List UInt256) :
    blk5403Model s p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 rest =
      {s with pc := UInt256.ofNat 5414, memory := blk5403_mem s.memory p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22, stack := p4_0 :: p4_1 :: p4_2 :: p4_3 :: p4_4 :: p4_5 :: p4_6 :: p4_7 :: p4_8 :: p4_9 :: p4_10 :: p4_11 :: p4_12 :: p4_13 :: p4_14 :: p4_15 :: p4_16 :: p4_17 :: p4_18 :: p4_19 :: p4_20 :: p4_21 :: p4_22 :: rest} := by
  simp only [blk5403Model, blk5403_mem]

/-! ## blk5414: pc 5414..5425, 7 instructions -/

def blk5414part0Program : List Instr :=
  [.push 2 292,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 64,
   .op .MSTORE]

def blk5414part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 292
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 64
  {s with pc := UInt256.ofNat 5425, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem blk5414part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5414part0Program {s with pc := UInt256.ofNat 5414, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (blk5414part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hc (j : Nat) (hj : j ≤ 38) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha292 : (292 : UInt256).toNat = 292 := rfl
  have hf292 := activeWords_fix s 292 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5414part0Program, blk5414part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha292, hf292, ha224, hf224, ha64, hf64]

def blk5414Program : List Instr :=
  [.push 2 292,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 64,
   .op .MSTORE]

def blk5414Model (s : State) (p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 292
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 64
  {s with pc := UInt256.ofNat 5425, memory := v3, stack := p5_0 :: p5_1 :: p5_2 :: p5_3 :: p5_4 :: p5_5 :: p5_6 :: p5_7 :: p5_8 :: p5_9 :: p5_10 :: p5_11 :: p5_12 :: p5_13 :: p5_14 :: p5_15 :: p5_16 :: p5_17 :: p5_18 :: p5_19 :: p5_20 :: p5_21 :: p5_22 :: rest}

theorem blk5414_run (s : State) (p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5414Program {s with pc := UInt256.ofNat 5414, stack := p5_0 :: p5_1 :: p5_2 :: p5_3 :: p5_4 :: p5_5 :: p5_6 :: p5_7 :: p5_8 :: p5_9 :: p5_10 :: p5_11 :: p5_12 :: p5_13 :: p5_14 :: p5_15 :: p5_16 :: p5_17 :: p5_18 :: p5_19 :: p5_20 :: p5_21 :: p5_22 :: rest} =
      some (blk5414Model s p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 292
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 64
  have h0 : runInstructions blk5414part0Program {s with pc := UInt256.ofNat 5414, memory := s.memory, stack := p5_0 :: p5_1 :: p5_2 :: p5_3 :: p5_4 :: p5_5 :: p5_6 :: p5_7 :: p5_8 :: p5_9 :: p5_10 :: p5_11 :: p5_12 :: p5_13 :: p5_14 :: p5_15 :: p5_16 :: p5_17 :: p5_18 :: p5_19 :: p5_20 :: p5_21 :: p5_22 :: rest} = some {s with pc := UInt256.ofNat 5425, memory := v3, stack := p5_0 :: p5_1 :: p5_2 :: p5_3 :: p5_4 :: p5_5 :: p5_6 :: p5_7 :: p5_8 :: p5_9 :: p5_10 :: p5_11 :: p5_12 :: p5_13 :: p5_14 :: p5_15 :: p5_16 :: p5_17 :: p5_18 :: p5_19 :: p5_20 :: p5_21 :: p5_22 :: rest} := by
    simpa only [blk5414part0Model, v0, v1, v2, v3] using blk5414part0_run (s) p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 rest hcap hact
  exact h0

def blk5414_mem (mem : ByteArray) (p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 292)).toNat 32) 64)

theorem blk5414_eq (s : State) (p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 : UInt256) (rest : List UInt256) :
    blk5414Model s p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 rest =
      {s with pc := UInt256.ofNat 5425, memory := blk5414_mem s.memory p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22, stack := p5_0 :: p5_1 :: p5_2 :: p5_3 :: p5_4 :: p5_5 :: p5_6 :: p5_7 :: p5_8 :: p5_9 :: p5_10 :: p5_11 :: p5_12 :: p5_13 :: p5_14 :: p5_15 :: p5_16 :: p5_17 :: p5_18 :: p5_19 :: p5_20 :: p5_21 :: p5_22 :: rest} := by
  simp only [blk5414Model, blk5414_mem]

/-! ## blk5425: pc 5425..5436, 7 instructions -/

def blk5425part0Program : List Instr :=
  [.push 2 262,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 96,
   .op .MSTORE]

def blk5425part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 262
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  {s with pc := UInt256.ofNat 5436, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem blk5425part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5425part0Program {s with pc := UInt256.ofNat 5425, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (blk5425part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hc (j : Nat) (hj : j ≤ 38) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha262 : (262 : UInt256).toNat = 262 := rfl
  have hf262 := activeWords_fix s 262 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5425part0Program, blk5425part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha262, hf262, ha224, hf224, ha96, hf96]

def blk5425Program : List Instr :=
  [.push 2 262,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 1 96,
   .op .MSTORE]

def blk5425Model (s : State) (p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 262
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  {s with pc := UInt256.ofNat 5436, memory := v3, stack := p6_0 :: p6_1 :: p6_2 :: p6_3 :: p6_4 :: p6_5 :: p6_6 :: p6_7 :: p6_8 :: p6_9 :: p6_10 :: p6_11 :: p6_12 :: p6_13 :: p6_14 :: p6_15 :: p6_16 :: p6_17 :: p6_18 :: p6_19 :: p6_20 :: p6_21 :: p6_22 :: rest}

theorem blk5425_run (s : State) (p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5425Program {s with pc := UInt256.ofNat 5425, stack := p6_0 :: p6_1 :: p6_2 :: p6_3 :: p6_4 :: p6_5 :: p6_6 :: p6_7 :: p6_8 :: p6_9 :: p6_10 :: p6_11 :: p6_12 :: p6_13 :: p6_14 :: p6_15 :: p6_16 :: p6_17 :: p6_18 :: p6_19 :: p6_20 :: p6_21 :: p6_22 :: rest} =
      some (blk5425Model s p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 262
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  have h0 : runInstructions blk5425part0Program {s with pc := UInt256.ofNat 5425, memory := s.memory, stack := p6_0 :: p6_1 :: p6_2 :: p6_3 :: p6_4 :: p6_5 :: p6_6 :: p6_7 :: p6_8 :: p6_9 :: p6_10 :: p6_11 :: p6_12 :: p6_13 :: p6_14 :: p6_15 :: p6_16 :: p6_17 :: p6_18 :: p6_19 :: p6_20 :: p6_21 :: p6_22 :: rest} = some {s with pc := UInt256.ofNat 5436, memory := v3, stack := p6_0 :: p6_1 :: p6_2 :: p6_3 :: p6_4 :: p6_5 :: p6_6 :: p6_7 :: p6_8 :: p6_9 :: p6_10 :: p6_11 :: p6_12 :: p6_13 :: p6_14 :: p6_15 :: p6_16 :: p6_17 :: p6_18 :: p6_19 :: p6_20 :: p6_21 :: p6_22 :: rest} := by
    simpa only [blk5425part0Model, v0, v1, v2, v3] using blk5425part0_run (s) p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 rest hcap hact
  exact h0

def blk5425_mem (mem : ByteArray) (p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 262)).toNat 32) 96)

theorem blk5425_eq (s : State) (p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 : UInt256) (rest : List UInt256) :
    blk5425Model s p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 rest =
      {s with pc := UInt256.ofNat 5436, memory := blk5425_mem s.memory p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22, stack := p6_0 :: p6_1 :: p6_2 :: p6_3 :: p6_4 :: p6_5 :: p6_6 :: p6_7 :: p6_8 :: p6_9 :: p6_10 :: p6_11 :: p6_12 :: p6_13 :: p6_14 :: p6_15 :: p6_16 :: p6_17 :: p6_18 :: p6_19 :: p6_20 :: p6_21 :: p6_22 :: rest} := by
  simp only [blk5425Model, blk5425_mem]

/-! ## blk5436: pc 5436..5446, 6 instructions -/

def blk5436part0Program : List Instr :=
  [.push 2 256,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 128,
   .op .MSTORE]

def blk5436part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 256
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 192)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 128
  {s with pc := UInt256.ofNat 5446, memory := v2, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem blk5436part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5436part0Program {s with pc := UInt256.ofNat 5436, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (blk5436part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hc (j : Nat) (hj : j ≤ 38) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha256 : (256 : UInt256).toNat = 256 := rfl
  have hf256 := activeWords_fix s 256 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5436part0Program, blk5436part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha256, hf256, ha128, hf128]

def blk5436Program : List Instr :=
  [.push 2 256,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 128,
   .op .MSTORE]

def blk5436Model (s : State) (p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 256
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 192)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 128
  {s with pc := UInt256.ofNat 5446, memory := v2, stack := p7_0 :: p7_1 :: p7_2 :: p7_3 :: p7_4 :: p7_5 :: p7_6 :: p7_7 :: p7_8 :: p7_9 :: p7_10 :: p7_11 :: p7_12 :: p7_13 :: p7_14 :: p7_15 :: p7_16 :: p7_17 :: p7_18 :: p7_19 :: p7_20 :: p7_21 :: p7_22 :: rest}

theorem blk5436_run (s : State) (p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5436Program {s with pc := UInt256.ofNat 5436, stack := p7_0 :: p7_1 :: p7_2 :: p7_3 :: p7_4 :: p7_5 :: p7_6 :: p7_7 :: p7_8 :: p7_9 :: p7_10 :: p7_11 :: p7_12 :: p7_13 :: p7_14 :: p7_15 :: p7_16 :: p7_17 :: p7_18 :: p7_19 :: p7_20 :: p7_21 :: p7_22 :: rest} =
      some (blk5436Model s p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 256
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 192)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 128
  have h0 : runInstructions blk5436part0Program {s with pc := UInt256.ofNat 5436, memory := s.memory, stack := p7_0 :: p7_1 :: p7_2 :: p7_3 :: p7_4 :: p7_5 :: p7_6 :: p7_7 :: p7_8 :: p7_9 :: p7_10 :: p7_11 :: p7_12 :: p7_13 :: p7_14 :: p7_15 :: p7_16 :: p7_17 :: p7_18 :: p7_19 :: p7_20 :: p7_21 :: p7_22 :: rest} = some {s with pc := UInt256.ofNat 5446, memory := v2, stack := p7_0 :: p7_1 :: p7_2 :: p7_3 :: p7_4 :: p7_5 :: p7_6 :: p7_7 :: p7_8 :: p7_9 :: p7_10 :: p7_11 :: p7_12 :: p7_13 :: p7_14 :: p7_15 :: p7_16 :: p7_17 :: p7_18 :: p7_19 :: p7_20 :: p7_21 :: p7_22 :: rest} := by
    simpa only [blk5436part0Model, v0, v1, v2] using blk5436part0_run (s) p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 rest hcap hact
  exact h0

def blk5436_mem (mem : ByteArray) (p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 : UInt256) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.shiftRight (MachineState.readWord mem 256) (UInt256.ofNat 192)).toNat 32) 128)

theorem blk5436_eq (s : State) (p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 : UInt256) (rest : List UInt256) :
    blk5436Model s p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 rest =
      {s with pc := UInt256.ofNat 5446, memory := blk5436_mem s.memory p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22, stack := p7_0 :: p7_1 :: p7_2 :: p7_3 :: p7_4 :: p7_5 :: p7_6 :: p7_7 :: p7_8 :: p7_9 :: p7_10 :: p7_11 :: p7_12 :: p7_13 :: p7_14 :: p7_15 :: p7_16 :: p7_17 :: p7_18 :: p7_19 :: p7_20 :: p7_21 :: p7_22 :: rest} := by
  simp only [blk5436Model, blk5436_mem]

/-! ## blk5446: pc 5446..5464, 9 instructions -/

def blk5446part0Program : List Instr :=
  [.push 2 2112,
   .op .MLOAD,
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 200,
   .op .SHR]

def blk5446part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2112
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 200)
  {s with pc := UInt256.ofNat 5457, memory := s.memory, stack := v2 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem blk5446part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5446part0Program {s with pc := UInt256.ofNat 5446, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (blk5446part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hc (j : Nat) (hj : j ≤ 39) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hf2112 := activeWords_fix s 2112 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5446part0Program, blk5446part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha2112, hf2112]

def blk5446part1Program : List Instr :=
  [.push 5 1099511627775,
   .op .EQ]

def blk5446part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.eq (UInt256.ofNat 1099511627775) x0
  {s with pc := UInt256.ofNat 5464, memory := s.memory, stack := v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest}

theorem blk5446part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5446part1Program {s with pc := UInt256.ofNat 5457, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest} =
      some (blk5446part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 rest) := by
  have hc (j : Nat) (hj : j ≤ 39) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, blk5446part1Program, blk5446part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def blk5446Program : List Instr :=
  [.push 2 2112,
   .op .MLOAD,
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 200,
   .op .SHR,
   .push 5 1099511627775,
   .op .EQ]

def blk5446Model (s : State) (p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2112
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 200)
  let v3 : UInt256 := UInt256.eq (UInt256.ofNat 1099511627775) v2
  {s with pc := UInt256.ofNat 5464, memory := s.memory, stack := v3 :: v1 :: p8_0 :: p8_1 :: p8_2 :: p8_3 :: p8_4 :: p8_5 :: p8_6 :: p8_7 :: p8_8 :: p8_9 :: p8_10 :: p8_11 :: p8_12 :: p8_13 :: p8_14 :: p8_15 :: p8_16 :: p8_17 :: p8_18 :: p8_19 :: p8_20 :: p8_21 :: p8_22 :: rest}

theorem blk5446_run (s : State) (p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5446Program {s with pc := UInt256.ofNat 5446, stack := p8_0 :: p8_1 :: p8_2 :: p8_3 :: p8_4 :: p8_5 :: p8_6 :: p8_7 :: p8_8 :: p8_9 :: p8_10 :: p8_11 :: p8_12 :: p8_13 :: p8_14 :: p8_15 :: p8_16 :: p8_17 :: p8_18 :: p8_19 :: p8_20 :: p8_21 :: p8_22 :: rest} =
      some (blk5446Model s p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 2112
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 200)
  let v3 : UInt256 := UInt256.eq (UInt256.ofNat 1099511627775) v2
  have h0 : runInstructions blk5446part0Program {s with pc := UInt256.ofNat 5446, memory := s.memory, stack := p8_0 :: p8_1 :: p8_2 :: p8_3 :: p8_4 :: p8_5 :: p8_6 :: p8_7 :: p8_8 :: p8_9 :: p8_10 :: p8_11 :: p8_12 :: p8_13 :: p8_14 :: p8_15 :: p8_16 :: p8_17 :: p8_18 :: p8_19 :: p8_20 :: p8_21 :: p8_22 :: rest} = some {s with pc := UInt256.ofNat 5457, memory := s.memory, stack := v2 :: v1 :: p8_0 :: p8_1 :: p8_2 :: p8_3 :: p8_4 :: p8_5 :: p8_6 :: p8_7 :: p8_8 :: p8_9 :: p8_10 :: p8_11 :: p8_12 :: p8_13 :: p8_14 :: p8_15 :: p8_16 :: p8_17 :: p8_18 :: p8_19 :: p8_20 :: p8_21 :: p8_22 :: rest} := by
    simpa only [blk5446part0Model, v0, v1, v2] using blk5446part0_run (s) p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 rest hcap hact
  have h1 : runInstructions blk5446part1Program {s with pc := UInt256.ofNat 5457, memory := s.memory, stack := v2 :: v1 :: p8_0 :: p8_1 :: p8_2 :: p8_3 :: p8_4 :: p8_5 :: p8_6 :: p8_7 :: p8_8 :: p8_9 :: p8_10 :: p8_11 :: p8_12 :: p8_13 :: p8_14 :: p8_15 :: p8_16 :: p8_17 :: p8_18 :: p8_19 :: p8_20 :: p8_21 :: p8_22 :: rest} = some {s with pc := UInt256.ofNat 5464, memory := s.memory, stack := v3 :: v1 :: p8_0 :: p8_1 :: p8_2 :: p8_3 :: p8_4 :: p8_5 :: p8_6 :: p8_7 :: p8_8 :: p8_9 :: p8_10 :: p8_11 :: p8_12 :: p8_13 :: p8_14 :: p8_15 :: p8_16 :: p8_17 :: p8_18 :: p8_19 :: p8_20 :: p8_21 :: p8_22 :: rest} := by
    simpa only [blk5446part1Model, v3] using blk5446part1_run (s) v2 v1 p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 h1)

def blk5446_o0 (mem : ByteArray) (p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 : UInt256) : UInt256 :=
  (UInt256.eq (UInt256.ofNat 1099511627775) (UInt256.shiftRight (UInt256.shiftRight (MachineState.readWord mem 2112) (UInt256.ofNat 16)) (UInt256.ofNat 200)))

def blk5446_o1 (mem : ByteArray) (p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 : UInt256) : UInt256 :=
  (UInt256.shiftRight (MachineState.readWord mem 2112) (UInt256.ofNat 16))

theorem blk5446_eq (s : State) (p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 : UInt256) (rest : List UInt256) :
    blk5446Model s p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 rest =
      {s with pc := UInt256.ofNat 5464, stack := (blk5446_o0 s.memory p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22) :: (blk5446_o1 s.memory p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22) :: p8_0 :: p8_1 :: p8_2 :: p8_3 :: p8_4 :: p8_5 :: p8_6 :: p8_7 :: p8_8 :: p8_9 :: p8_10 :: p8_11 :: p8_12 :: p8_13 :: p8_14 :: p8_15 :: p8_16 :: p8_17 :: p8_18 :: p8_19 :: p8_20 :: p8_21 :: p8_22 :: rest} := by
  simp only [blk5446Model, blk5446_o0, blk5446_o1]

/-! ## blk5467: pc 5467..5502, 22 instructions -/

def blk5467part0Program : List Instr :=
  [.push 2 2140,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 2 2170,
   .op .MLOAD]

def blk5467part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2140
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : UInt256 := MachineState.readWord s.memory 2170
  {s with pc := UInt256.ofNat 5479, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest}

theorem blk5467part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5467part0Program {s with pc := UInt256.ofNat 5467, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest} =
      some (blk5467part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 rest) := by
  have hc (j : Nat) (hj : j ≤ 39) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha2140 : (2140 : UInt256).toNat = 2140 := rfl
  have hf2140 := activeWords_fix s 2140 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha2170 : (2170 : UInt256).toNat = 2170 := rfl
  have hf2170 := activeWords_fix s 2170 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5467part0Program, blk5467part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha2140, hf2140, ha224, hf224, ha2170, hf2170]

def blk5467part1Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 2 2200,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND]

def blk5467part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.land v0 x0
  let v2 : UInt256 := MachineState.readWord s.memory 2200
  let v3 : UInt256 := MachineState.readWord s.memory 224
  let v4 : UInt256 := UInt256.land v3 v2
  {s with pc := UInt256.ofNat 5491, memory := s.memory, stack := v4 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest}

theorem blk5467part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5467part1Program {s with pc := UInt256.ofNat 5479, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest} =
      some (blk5467part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 rest) := by
  have hc (j : Nat) (hj : j ≤ 41) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha2200 : (2200 : UInt256).toNat = 2200 := rfl
  have hf2200 := activeWords_fix s 2200 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5467part1Program, blk5467part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224, ha2200, hf2200]

def blk5467part2Program : List Instr :=
  [.push 2 2208,
   .op .MLOAD,
   .push 1 176,
   .op .SHL,
   .push 1 224,
   .op .MLOAD,
   .op .AND]

def blk5467part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2208
  let v1 : UInt256 := UInt256.shiftLeft v0 (UInt256.ofNat 176)
  let v2 : UInt256 := MachineState.readWord s.memory 224
  let v3 : UInt256 := UInt256.land v2 v1
  {s with pc := UInt256.ofNat 5502, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: rest}

theorem blk5467part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5467part2Program {s with pc := UInt256.ofNat 5491, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: rest} =
      some (blk5467part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 rest) := by
  have hc (j : Nat) (hj : j ≤ 42) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha2208 : (2208 : UInt256).toNat = 2208 := rfl
  have hf2208 := activeWords_fix s 2208 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5467part2Program, blk5467part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha2208, hf2208, ha224, hf224]

def blk5467Program : List Instr :=
  [.push 2 2140,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 2 2170,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 2 2200,
   .op .MLOAD,
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .push 2 2208,
   .op .MLOAD,
   .push 1 176,
   .op .SHL,
   .push 1 224,
   .op .MLOAD,
   .op .AND]

def blk5467Model (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2140
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : UInt256 := MachineState.readWord s.memory 2170
  let v4 : UInt256 := MachineState.readWord s.memory 224
  let v5 : UInt256 := UInt256.land v4 v3
  let v6 : UInt256 := MachineState.readWord s.memory 2200
  let v7 : UInt256 := MachineState.readWord s.memory 224
  let v8 : UInt256 := UInt256.land v7 v6
  let v9 : UInt256 := MachineState.readWord s.memory 2208
  let v10 : UInt256 := UInt256.shiftLeft v9 (UInt256.ofNat 176)
  let v11 : UInt256 := MachineState.readWord s.memory 224
  let v12 : UInt256 := UInt256.land v11 v10
  {s with pc := UInt256.ofNat 5502, memory := s.memory, stack := v12 :: v8 :: v5 :: v2 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest}

theorem blk5467_run (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5467Program {s with pc := UInt256.ofNat 5467, stack := p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} =
      some (blk5467Model s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 2140
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 v0
  let v3 : UInt256 := MachineState.readWord s.memory 2170
  let v4 : UInt256 := MachineState.readWord s.memory 224
  let v5 : UInt256 := UInt256.land v4 v3
  let v6 : UInt256 := MachineState.readWord s.memory 2200
  let v7 : UInt256 := MachineState.readWord s.memory 224
  let v8 : UInt256 := UInt256.land v7 v6
  let v9 : UInt256 := MachineState.readWord s.memory 2208
  let v10 : UInt256 := UInt256.shiftLeft v9 (UInt256.ofNat 176)
  let v11 : UInt256 := MachineState.readWord s.memory 224
  let v12 : UInt256 := UInt256.land v11 v10
  have h0 : runInstructions blk5467part0Program {s with pc := UInt256.ofNat 5467, memory := s.memory, stack := p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} = some {s with pc := UInt256.ofNat 5479, memory := s.memory, stack := v3 :: v2 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
    simpa only [blk5467part0Model, v0, v1, v2, v3] using blk5467part0_run (s) p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest hcap hact
  have h1 : runInstructions blk5467part1Program {s with pc := UInt256.ofNat 5479, memory := s.memory, stack := v3 :: v2 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} = some {s with pc := UInt256.ofNat 5491, memory := s.memory, stack := v8 :: v5 :: v2 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
    simpa only [blk5467part1Model, v4, v5, v6, v7, v8] using blk5467part1_run (s) v3 v2 p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest hcap hact
  have h2 : runInstructions blk5467part2Program {s with pc := UInt256.ofNat 5491, memory := s.memory, stack := v8 :: v5 :: v2 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} = some {s with pc := UInt256.ofNat 5502, memory := s.memory, stack := v12 :: v8 :: v5 :: v2 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
    simpa only [blk5467part2Model, v9, v10, v11, v12] using blk5467part2_run (s) v8 v5 v2 p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))

def blk5467_o0 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : UInt256) : UInt256 :=
  (UInt256.land (MachineState.readWord mem 224) (UInt256.shiftLeft (MachineState.readWord mem 2208) (UInt256.ofNat 176)))

def blk5467_o1 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : UInt256) : UInt256 :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 2200))

def blk5467_o2 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : UInt256) : UInt256 :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 2170))

def blk5467_o3 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : UInt256) : UInt256 :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 2140))

theorem blk5467_eq (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : UInt256) (rest : List UInt256) :
    blk5467Model s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest =
      {s with pc := UInt256.ofNat 5502, stack := (blk5467_o0 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: (blk5467_o1 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: (blk5467_o2 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: (blk5467_o3 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
  simp only [blk5467Model, blk5467_o0, blk5467_o1, blk5467_o2, blk5467_o3]

end CycleSubmission.R5.ExecPrologue

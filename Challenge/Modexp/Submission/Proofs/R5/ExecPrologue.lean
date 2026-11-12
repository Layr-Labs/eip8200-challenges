import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp

open CycleSubmission.SharedStackArgs

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

local notation "W" => UInt256
local notation "N" => UInt256.ofNat

private theorem hz : ({val := 0} : W) = N 0 := rfl
private theorem hzn : ({val := 0} : W).toNat = 0 := rfl

/-! ## pro: pc 5334..5344, 8 instructions -/

def pro_o0 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) : W :=
  (UInt256.shiftLeft f11 (N 16))

def pro_mem (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.shiftLeft f11 (N 16)).toNat 32) 192)

def blk5344_mem (mem : ByteArray) (p1_0 p1_1 p1_2 p1_3 p1_4 p1_5 p1_6 p1_7 p1_8 p1_9 p1_10 p1_11 p1_12 p1_13 p1_14 p1_15 p1_16 p1_17 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.shiftRight (UInt256.lnot (N 0)) (N 16)).toNat 32) 224)

def blk5352_o0 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : W) : W :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 66))

def blk5352_o1 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : W) : W :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 36))

def blk5352_o2 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : W) : W :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 6))

def blk5352_o3 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : W) : W :=
  (UInt256.shiftRight (MachineState.readWord mem 0) (N 192))

def blk5352_o4 (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : W) : W :=
  (UInt256.shiftRight (UInt256.lnot (N 0)) (N 5))

def blk5352_mem (mem : ByteArray) (p2_0 p2_1 p2_2 p2_3 p2_4 p2_5 p2_6 p2_7 p2_8 p2_9 p2_10 p2_11 p2_12 p2_13 p2_14 p2_15 p2_16 p2_17 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 96)).toNat 32) 160)

def blk5393_mem (mem : ByteArray) (p3_0 p3_1 p3_2 p3_3 p3_4 p3_5 p3_6 p3_7 p3_8 p3_9 p3_10 p3_11 p3_12 p3_13 p3_14 p3_15 p3_16 p3_17 p3_18 p3_19 p3_20 p3_21 p3_22 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 352)).toNat 32) 0)

def blk5403_mem (mem : ByteArray) (p4_0 p4_1 p4_2 p4_3 p4_4 p4_5 p4_6 p4_7 p4_8 p4_9 p4_10 p4_11 p4_12 p4_13 p4_14 p4_15 p4_16 p4_17 p4_18 p4_19 p4_20 p4_21 p4_22 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 322)).toNat 32) 32)

def blk5414_mem (mem : ByteArray) (p5_0 p5_1 p5_2 p5_3 p5_4 p5_5 p5_6 p5_7 p5_8 p5_9 p5_10 p5_11 p5_12 p5_13 p5_14 p5_15 p5_16 p5_17 p5_18 p5_19 p5_20 p5_21 p5_22 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 292)).toNat 32) 64)

def blk5425_mem (mem : ByteArray) (p6_0 p6_1 p6_2 p6_3 p6_4 p6_5 p6_6 p6_7 p6_8 p6_9 p6_10 p6_11 p6_12 p6_13 p6_14 p6_15 p6_16 p6_17 p6_18 p6_19 p6_20 p6_21 p6_22 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 262)).toNat 32) 96)

def blk5436_mem (mem : ByteArray) (p7_0 p7_1 p7_2 p7_3 p7_4 p7_5 p7_6 p7_7 p7_8 p7_9 p7_10 p7_11 p7_12 p7_13 p7_14 p7_15 p7_16 p7_17 p7_18 p7_19 p7_20 p7_21 p7_22 : W) : ByteArray :=
  (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.shiftRight (MachineState.readWord mem 256) (N 192)).toNat 32) 128)

def blk5446_o0 (mem : ByteArray) (p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 : W) : W :=
  (UInt256.eq (N 1099511627775) (UInt256.shiftRight (UInt256.shiftRight (MachineState.readWord mem 2112) (N 16)) (N 200)))

def blk5446_o1 (mem : ByteArray) (p8_0 p8_1 p8_2 p8_3 p8_4 p8_5 p8_6 p8_7 p8_8 p8_9 p8_10 p8_11 p8_12 p8_13 p8_14 p8_15 p8_16 p8_17 p8_18 p8_19 p8_20 p8_21 p8_22 : W) : W :=
  (UInt256.shiftRight (MachineState.readWord mem 2112) (N 16))

/-! ## blk5467: pc 5467..5502, 20 instructions -/

open CycleSubmission.Prepared.Arithmetic
open Challenge.Modexp.Submission.Proofs.Fast

def preparedpart0Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .push 2 2170,
   .op .MLOAD,
   .op (.Dup dA1),
   .op .AND,
   .push 2 2200,
   .op .MLOAD]

def preparedpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := MachineState.readWord s.memory 2170
  let v2 : W := UInt256.land v0 v1
  let v3 : W := MachineState.readWord s.memory 2200
  {s with pc := N 5394, memory := s.memory, stack := v3 :: v2 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest}

theorem preparedpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedpart0Program {s with pc := N 5381, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest} =
      some (preparedpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha2170 : (2170 : W).toNat = 2170 := rfl
  have hf2170 := Monpro.activeWords_fix s 2170 32 (by decide) (by norm_num) hact
  have ha2200 : (2200 : W).toNat = 2200 := rfl
  have hf2200 := Monpro.activeWords_fix s 2200 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedpart0Program, preparedpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha224, hf224, ha2170, hf2170, ha2200, hf2200]


def preparedpart1Program : List Instr :=
  [.op (.Dup dA2),
   .op .AND,
   .push 2 2208,
   .op .MLOAD,
   .push 1 176,
   .op .SHL,
   .push 2 2140,
   .op .MLOAD]

def preparedpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x2 x0
  let v1 : W := MachineState.readWord s.memory 2208
  let v2 : W := UInt256.shiftLeft v1 (N 176)
  let v3 : W := MachineState.readWord s.memory 2140
  {s with pc := N 5407, memory := s.memory, stack := v3 :: v2 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: rest}

theorem preparedpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedpart1Program {s with pc := N 5394, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: rest} =
      some (preparedpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 29) : rest.length + j < 1024 := by omega
  have ha2140 : (2140 : W).toNat = 2140 := rfl
  have hf2140 := Monpro.activeWords_fix s 2140 32 (by decide) (by norm_num) hact
  have ha2208 : (2208 : W).toNat = 2208 := rfl
  have hf2208 := Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedpart1Program, preparedpart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha2140, hf2140, ha2208, hf2208]


def preparedpart2Program : List Instr :=
  [.op (.Dup dA4),
   .op .AND,
   .op (.Swap sA3),
   .op .AND]

def preparedpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x4 x0
  let v1 : W := UInt256.land x4 x1
  {s with pc := N 5411, memory := s.memory, stack := v1 :: x2 :: x3 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: rest}

theorem preparedpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedpart2Program {s with pc := N 5407, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: rest} =
      some (preparedpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  simp [hz, hzn, preparedpart2Program, preparedpart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]


def preparedProgram : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .push 2 2170,
   .op .MLOAD,
   .op (.Dup dA1),
   .op .AND,
   .push 2 2200,
   .op .MLOAD,
   .op (.Dup dA2),
   .op .AND,
   .push 2 2208,
   .op .MLOAD,
   .push 1 176,
   .op .SHL,
   .push 2 2140,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .AND,
   .op (.Swap sA3),
   .op .AND]

def preparedModel (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := MachineState.readWord s.memory 2170
  let v2 : W := UInt256.land v0 v1
  let v3 : W := MachineState.readWord s.memory 2200
  let v4 : W := UInt256.land v0 v3
  let v5 : W := MachineState.readWord s.memory 2208
  let v6 : W := UInt256.shiftLeft v5 (N 176)
  let v7 : W := MachineState.readWord s.memory 2140
  let v8 : W := UInt256.land v0 v7
  let v9 : W := UInt256.land v0 v6
  {s with pc := N 5411, memory := s.memory, stack := v9 :: v4 :: v2 :: v8 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest}

theorem prepared_run (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProgram {s with pc := N 5381, stack := p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} =
      some (preparedModel s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest) := by
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := MachineState.readWord s.memory 2170
  let v2 : W := UInt256.land v0 v1
  let v3 : W := MachineState.readWord s.memory 2200
  let v4 : W := UInt256.land v0 v3
  let v5 : W := MachineState.readWord s.memory 2208
  let v6 : W := UInt256.shiftLeft v5 (N 176)
  let v7 : W := MachineState.readWord s.memory 2140
  let v8 : W := UInt256.land v0 v7
  let v9 : W := UInt256.land v0 v6
  have h0 : runInstructions preparedpart0Program {s with pc := N 5381, memory := s.memory, stack := p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} = some {s with pc := N 5394, memory := s.memory, stack := v3 :: v2 :: v0 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
    simpa only [preparedpart0Model, v0, v1, v2, v3] using preparedpart0_run (s) (p9_0) (p9_1) (p9_2) (p9_3) (p9_4) (p9_5) (p9_6) (p9_7) (p9_8) (p9_9) (p9_10) (p9_11) (p9_12) (p9_13) (p9_14) (p9_15) (p9_16) (p9_17) (p9_18) (p9_19) (p9_20) (p9_21) (p9_22) (p9_23) rest hcap hact
  have h1 : runInstructions preparedpart1Program {s with pc := N 5394, memory := s.memory, stack := v3 :: v2 :: v0 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} = some {s with pc := N 5407, memory := s.memory, stack := v7 :: v6 :: v4 :: v2 :: v0 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
    simpa only [preparedpart1Model, v4, v5, v6, v7] using preparedpart1_run (s) (v3) (v2) (v0) (p9_0) (p9_1) (p9_2) (p9_3) (p9_4) (p9_5) (p9_6) (p9_7) (p9_8) (p9_9) (p9_10) (p9_11) (p9_12) (p9_13) (p9_14) (p9_15) (p9_16) (p9_17) (p9_18) (p9_19) (p9_20) (p9_21) (p9_22) (p9_23) rest hcap hact
  have h2 : runInstructions preparedpart2Program {s with pc := N 5407, memory := s.memory, stack := v7 :: v6 :: v4 :: v2 :: v0 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} = some {s with pc := N 5411, memory := s.memory, stack := v9 :: v4 :: v2 :: v8 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
    simpa only [preparedpart2Model, v8, v9] using preparedpart2_run (s) (v7) (v6) (v4) (v2) (v0) (p9_0) (p9_1) (p9_2) (p9_3) (p9_4) (p9_5) (p9_6) (p9_7) (p9_8) (p9_9) (p9_10) (p9_11) (p9_12) (p9_13) (p9_14) (p9_15) (p9_16) (p9_17) (p9_18) (p9_19) (p9_20) (p9_21) (p9_22) (p9_23) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))

#print axioms prepared_run

def blk5467Model (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2140
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := UInt256.land v1 v0
  let v3 : W := MachineState.readWord s.memory 2170
  let v4 : W := MachineState.readWord s.memory 224
  let v5 : W := UInt256.land v4 v3
  let v6 : W := MachineState.readWord s.memory 2200
  let v7 : W := MachineState.readWord s.memory 224
  let v8 : W := UInt256.land v7 v6
  let v9 : W := MachineState.readWord s.memory 2208
  let v10 : W := UInt256.shiftLeft v9 (N 176)
  let v11 : W := MachineState.readWord s.memory 224
  let v12 : W := UInt256.land v11 v10
  {s with pc := N 5411, memory := s.memory, stack := v12 :: v8 :: v5 :: v2 :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest}

def blk5467Program : List Instr := preparedProgram

private theorem prepared_model_eq (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) (rest : List W) :
    preparedModel s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest = blk5467Model s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest := by
  simp (disch := decide) only [preparedModel, blk5467Model, addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint]

theorem blk5467_run (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5467Program {s with pc := N 5381, stack := p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} =
      some (blk5467Model s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest) := by
  exact (prepared_run s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest hcap hact).trans
    (congrArg some (prepared_model_eq s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest))

#print axioms blk5467_run

def blk5467_o0 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) : W :=
  (UInt256.land (MachineState.readWord mem 224) (UInt256.shiftLeft (MachineState.readWord mem 2208) (N 176)))

def blk5467_o1 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) : W :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 2200))

def blk5467_o2 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) : W :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 2170))

def blk5467_o3 (mem : ByteArray) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) : W :=
  (UInt256.land (MachineState.readWord mem 224) (MachineState.readWord mem 2140))

theorem blk5467_eq (s : State) (p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 : W) (rest : List W) :
    blk5467Model s p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23 rest =
      {s with pc := N 5411, stack := (blk5467_o0 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: (blk5467_o1 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: (blk5467_o2 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: (blk5467_o3 s.memory p9_0 p9_1 p9_2 p9_3 p9_4 p9_5 p9_6 p9_7 p9_8 p9_9 p9_10 p9_11 p9_12 p9_13 p9_14 p9_15 p9_16 p9_17 p9_18 p9_19 p9_20 p9_21 p9_22 p9_23) :: p9_0 :: p9_1 :: p9_2 :: p9_3 :: p9_4 :: p9_5 :: p9_6 :: p9_7 :: p9_8 :: p9_9 :: p9_10 :: p9_11 :: p9_12 :: p9_13 :: p9_14 :: p9_15 :: p9_16 :: p9_17 :: p9_18 :: p9_19 :: p9_20 :: p9_21 :: p9_22 :: p9_23 :: rest} := by
  simp only [blk5467Model, blk5467_o0, blk5467_o1, blk5467_o2, blk5467_o3]

end CycleSubmission.R5.ExecPrologue

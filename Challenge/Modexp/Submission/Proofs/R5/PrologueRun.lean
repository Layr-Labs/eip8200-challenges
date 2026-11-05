import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.R5.ExecPrologue

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.PrologueRun
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.R5.ExecPrologue

def proSegV0_0 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  pro_o0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM0 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  pro_mem mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM1 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  blk5344_mem ((proSegM0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegV2_0 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  blk5352_o0 ((proSegM1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegV2_1 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  blk5352_o1 ((proSegM1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegV2_2 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  blk5352_o2 ((proSegM1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegV2_3 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  blk5352_o3 ((proSegM1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegV2_4 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  blk5352_o4 ((proSegM1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM2 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  blk5352_mem ((proSegM1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM3 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  blk5393_mem ((proSegM2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM4 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  blk5403_mem ((proSegM3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM5 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  blk5414_mem ((proSegM4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM6 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  blk5425_mem ((proSegM5 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegM7 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : ByteArray :=
  blk5436_mem ((proSegM6 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegV8_0 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  blk5446_o0 ((proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

def proSegV8_1 (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) : UInt256 :=
  blk5446_o1 ((proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) ((proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15)) f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

open CycleSubmission.Prepared.Arithmetic

def preparedProloguepart0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 16,
   .op .SHL,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 192,
   .op .MSTORE]

def preparedProloguepart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x11 (UInt256.ofNat 16)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  {s with pc := UInt256.ofNat 5384, memory := v1, stack := v0 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem preparedProloguepart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart0Program {s with pc := UInt256.ofNat 5374, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (preparedProloguepart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart0Program, preparedProloguepart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha192, hf192]


private theorem directMax_eq : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 = UInt256.lnot (UInt256.ofNat 0) := by decide

def preparedProloguepart1Program : List Instr :=
  [.push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 16,
   .op .SHR,
   .push 1 224,
   .op .MSTORE,
   .push 1 5]

def preparedProloguepart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 224
  {s with pc := UInt256.ofNat 5426, memory := v2, stack := (UInt256.ofNat 5) :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem preparedProloguepart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart1Program {s with pc := UInt256.ofNat 5384, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (preparedProloguepart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [directMax_eq, hz, hzn, preparedProloguepart1Program, preparedProloguepart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha224, hf224]


def preparedProloguepart2Program : List Instr :=
  [.op .SHR,
   .push 0 0,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩)]

def preparedProloguepart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x1 x0
  let v1 : UInt256 := MachineState.readWord s.memory 0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 192)
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 5436, memory := s.memory, stack := v3 :: v3 :: v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem preparedProloguepart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x0 : x0 = UInt256.ofNat 5) :
    runInstructions preparedProloguepart2Program {s with pc := UInt256.ofNat 5426, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (preparedProloguepart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hk_x0, hz, hzn, preparedProloguepart2Program, preparedProloguepart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def preparedProloguepart3Program : List Instr :=
  [.push 1 36,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 1 66,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND]

def preparedProloguepart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 36
  let v1 : UInt256 := UInt256.land x1 v0
  let v2 : UInt256 := MachineState.readWord s.memory 66
  let v3 : UInt256 := UInt256.land x1 v2
  {s with pc := UInt256.ofNat 5446, memory := s.memory, stack := v3 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest}

theorem preparedProloguepart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart3Program {s with pc := UInt256.ofNat 5436, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest} =
      some (preparedProloguepart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 25) : rest.length + j < 1024 := by omega
  have ha36 : (36 : UInt256).toNat = 36 := rfl
  have hf36 := Monpro.activeWords_fix s 36 32 (by decide) (by norm_num) hact
  have ha66 : (66 : UInt256).toNat = 66 := rfl
  have hf66 := Monpro.activeWords_fix s 66 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart3Program, preparedProloguepart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha36, hf36, ha66, hf66]


def preparedProloguepart4Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .push 1 6,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .AND]

def preparedProloguepart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := MachineState.readWord s.memory 6
  let v2 : UInt256 := UInt256.land x3 v1
  let v3 : UInt256 := UInt256.land x3 v0
  {s with pc := UInt256.ofNat 5456, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest}

theorem preparedProloguepart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart4Program {s with pc := UInt256.ofNat 5446, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest} =
      some (preparedProloguepart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have ha6 : (6 : UInt256).toNat = 6 := rfl
  have hf6 := Monpro.activeWords_fix s 6 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart4Program, preparedProloguepart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha6, hf6, ha96, hf96]


def preparedProloguepart5Program : List Instr :=
  [.push 1 160,
   .op .MSTORE,
   .push 2 352,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 0 0,
   .op .MSTORE]

def preparedProloguepart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 160
  let v1 : UInt256 := MachineState.readWord v0 352
  let v2 : UInt256 := UInt256.land x3 v1
  let v3 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v2.toNat 32) 0
  {s with pc := UInt256.ofNat 5467, memory := v3, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest}

theorem preparedProloguepart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart5Program {s with pc := UInt256.ofNat 5456, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest} =
      some (preparedProloguepart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha352 : (352 : UInt256).toNat = 352 := rfl
  have hf352 := Monpro.activeWords_fix s 352 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart5Program, preparedProloguepart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha0, hf0, ha160, hf160, ha352, hf352]


def preparedProloguepart6Program : List Instr :=
  [.push 2 322,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 1 32,
   .op .MSTORE,
   .push 2 292,
   .op .MLOAD]

def preparedProloguepart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 322
  let v1 : UInt256 := UInt256.land x2 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 32
  let v3 : UInt256 := MachineState.readWord v2 292
  {s with pc := UInt256.ofNat 5480, memory := v2, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest}

theorem preparedProloguepart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart6Program {s with pc := UInt256.ofNat 5467, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest} =
      some (preparedProloguepart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha292 : (292 : UInt256).toNat = 292 := rfl
  have hf292 := Monpro.activeWords_fix s 292 32 (by decide) (by norm_num) hact
  have ha322 : (322 : UInt256).toNat = 322 := rfl
  have hf322 := Monpro.activeWords_fix s 322 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart6Program, preparedProloguepart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha32, hf32, ha292, hf292, ha322, hf322]


def preparedProloguepart7Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 1 64,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .push 3 262,
   .op .MLOAD]

def preparedProloguepart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x3 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 64
  let v2 : UInt256 := MachineState.readWord v1 262
  {s with pc := UInt256.ofNat 5492, memory := v1, stack := v2 :: x3 :: x1 :: x2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest}

theorem preparedProloguepart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart7Program {s with pc := UInt256.ofNat 5480, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest} =
      some (preparedProloguepart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha262 : (262 : UInt256).toNat = 262 := rfl
  have hf262 := Monpro.activeWords_fix s 262 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart7Program, preparedProloguepart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha64, hf64, ha262, hf262]


def preparedProloguepart8Program : List Instr :=
  [.op .AND,
   .push 1 96,
   .op .MSTORE,
   .push 2 256,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 128,
   .op .MSTORE]

def preparedProloguepart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 96
  let v2 : UInt256 := MachineState.readWord v1 256
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 192)
  let v4 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v3.toNat 32) 128
  {s with pc := UInt256.ofNat 5506, memory := v4, stack := x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest}

theorem preparedProloguepart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart8Program {s with pc := UInt256.ofNat 5492, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: rest} =
      some (preparedProloguepart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 25) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha256 : (256 : UInt256).toNat = 256 := rfl
  have hf256 := Monpro.activeWords_fix s 256 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart8Program, preparedProloguepart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha96, hf96, ha128, hf128, ha256, hf256]


def preparedProloguepart9Program : List Instr :=
  [.push 2 2112,
   .op .MLOAD,
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 200,
   .op .SHR,
   .push 5 1099511627775]

def preparedProloguepart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2112
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 200)
  {s with pc := UInt256.ofNat 5523, memory := s.memory, stack := (UInt256.ofNat 1099511627775) :: v2 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem preparedProloguepart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedProloguepart9Program {s with pc := UInt256.ofNat 5506, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (preparedProloguepart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  have ha2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hf2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact
  simp [hz, hzn, preparedProloguepart9Program, preparedProloguepart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha2112, hf2112]


def preparedProloguepart10Program : List Instr :=
  [.op .EQ]

def preparedProloguepart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.eq x0 x1
  {s with pc := UInt256.ofNat 5524, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest}

theorem preparedProloguepart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x0 : x0 = UInt256.ofNat 1099511627775) :
    runInstructions preparedProloguepart10Program {s with pc := UInt256.ofNat 5523, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest} =
      some (preparedProloguepart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  simp [hk_x0, hz, hzn, preparedProloguepart10Program, preparedProloguepart10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]


def preparedPrologueProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 16,
   .op .SHL,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 192,
   .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 16,
   .op .SHR,
   .push 1 224,
   .op .MSTORE,
   .push 1 5,
   .op .SHR,
   .push 0 0,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 36,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 1 66,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 1 96,
   .op .MLOAD,
   .push 1 6,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .AND,
   .push 1 160,
   .op .MSTORE,
   .push 2 352,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 0 0,
   .op .MSTORE,
   .push 2 322,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 1 32,
   .op .MSTORE,
   .push 2 292,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 1 64,
   .op .MSTORE,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .push 3 262,
   .op .MLOAD,
   .op .AND,
   .push 1 96,
   .op .MSTORE,
   .push 2 256,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .push 1 128,
   .op .MSTORE,
   .push 2 2112,
   .op .MLOAD,
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 200,
   .op .SHR,
   .push 5 1099511627775,
   .op .EQ]

def preparedPrologueModel (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft f11 (UInt256.ofNat 16)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  let v2 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  let v4 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v3.toNat 32) 224
  let v5 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 5)
  let v6 : UInt256 := MachineState.readWord v4 0
  let v7 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 192)
  let v8 : UInt256 := MachineState.readWord v4 224
  let v9 : UInt256 := MachineState.readWord v4 36
  let v10 : UInt256 := UInt256.land v8 v9
  let v11 : UInt256 := MachineState.readWord v4 66
  let v12 : UInt256 := UInt256.land v8 v11
  let v13 : UInt256 := MachineState.readWord v4 96
  let v14 : UInt256 := MachineState.readWord v4 6
  let v15 : UInt256 := UInt256.land v8 v14
  let v16 : UInt256 := UInt256.land v8 v13
  let v17 : ByteArray := MachineState.writeBytes v4 (Data.Bytes.natToBytesPadded v16.toNat 32) 160
  let v18 : UInt256 := MachineState.readWord v17 352
  let v19 : UInt256 := UInt256.land v8 v18
  let v20 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v19.toNat 32) 0
  let v21 : UInt256 := MachineState.readWord v20 322
  let v22 : UInt256 := UInt256.land v8 v21
  let v23 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v22.toNat 32) 32
  let v24 : UInt256 := MachineState.readWord v23 292
  let v25 : UInt256 := UInt256.land v8 v24
  let v26 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v25.toNat 32) 64
  let v27 : UInt256 := MachineState.readWord v26 262
  let v28 : UInt256 := UInt256.land v27 v8
  let v29 : ByteArray := MachineState.writeBytes v26 (Data.Bytes.natToBytesPadded v28.toNat 32) 96
  let v30 : UInt256 := MachineState.readWord v29 256
  let v31 : UInt256 := UInt256.shiftRight v30 (UInt256.ofNat 192)
  let v32 : ByteArray := MachineState.writeBytes v29 (Data.Bytes.natToBytesPadded v31.toNat 32) 128
  let v33 : UInt256 := MachineState.readWord v32 2112
  let v34 : UInt256 := UInt256.shiftRight v33 (UInt256.ofNat 16)
  let v35 : UInt256 := UInt256.shiftRight v34 (UInt256.ofNat 200)
  let v36 : UInt256 := UInt256.eq (UInt256.ofNat 1099511627775) v35
  {s with pc := UInt256.ofNat 5524, memory := v32, stack := v36 :: v34 :: v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest}

theorem preparedPrologue_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedPrologueProgram {s with pc := UInt256.ofNat 5374, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} =
      some (preparedPrologueModel s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
  let v0 : UInt256 := UInt256.shiftLeft f11 (UInt256.ofNat 16)
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  let v2 : UInt256 := UInt256.lnot (UInt256.ofNat 0)
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  let v4 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v3.toNat 32) 224
  let v5 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 5)
  let v6 : UInt256 := MachineState.readWord v4 0
  let v7 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 192)
  let v8 : UInt256 := MachineState.readWord v4 224
  let v9 : UInt256 := MachineState.readWord v4 36
  let v10 : UInt256 := UInt256.land v8 v9
  let v11 : UInt256 := MachineState.readWord v4 66
  let v12 : UInt256 := UInt256.land v8 v11
  let v13 : UInt256 := MachineState.readWord v4 96
  let v14 : UInt256 := MachineState.readWord v4 6
  let v15 : UInt256 := UInt256.land v8 v14
  let v16 : UInt256 := UInt256.land v8 v13
  let v17 : ByteArray := MachineState.writeBytes v4 (Data.Bytes.natToBytesPadded v16.toNat 32) 160
  let v18 : UInt256 := MachineState.readWord v17 352
  let v19 : UInt256 := UInt256.land v8 v18
  let v20 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v19.toNat 32) 0
  let v21 : UInt256 := MachineState.readWord v20 322
  let v22 : UInt256 := UInt256.land v8 v21
  let v23 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v22.toNat 32) 32
  let v24 : UInt256 := MachineState.readWord v23 292
  let v25 : UInt256 := UInt256.land v8 v24
  let v26 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v25.toNat 32) 64
  let v27 : UInt256 := MachineState.readWord v26 262
  let v28 : UInt256 := UInt256.land v27 v8
  let v29 : ByteArray := MachineState.writeBytes v26 (Data.Bytes.natToBytesPadded v28.toNat 32) 96
  let v30 : UInt256 := MachineState.readWord v29 256
  let v31 : UInt256 := UInt256.shiftRight v30 (UInt256.ofNat 192)
  let v32 : ByteArray := MachineState.writeBytes v29 (Data.Bytes.natToBytesPadded v31.toNat 32) 128
  let v33 : UInt256 := MachineState.readWord v32 2112
  let v34 : UInt256 := UInt256.shiftRight v33 (UInt256.ofNat 16)
  let v35 : UInt256 := UInt256.shiftRight v34 (UInt256.ofNat 200)
  let v36 : UInt256 := UInt256.eq (UInt256.ofNat 1099511627775) v35
  have h0 : runInstructions preparedProloguepart0Program {s with pc := UInt256.ofNat 5374, memory := s.memory, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5384, memory := v1, stack := v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart0Model, v0, v1] using preparedProloguepart0_run (s) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h1 : runInstructions preparedProloguepart1Program {s with pc := UInt256.ofNat 5384, memory := v1, stack := v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5426, memory := v4, stack := (UInt256.ofNat 5) :: v2 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart1Model, v2, v3, v4] using preparedProloguepart1_run ({s with memory := v1}) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h2 : runInstructions preparedProloguepart2Program {s with pc := UInt256.ofNat 5426, memory := v4, stack := (UInt256.ofNat 5) :: v2 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5436, memory := v4, stack := v8 :: v8 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart2Model, v5, v6, v7, v8] using preparedProloguepart2_run ({s with memory := v4}) ((UInt256.ofNat 5)) (v2) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact (by rfl)
  have h3 : runInstructions preparedProloguepart3Program {s with pc := UInt256.ofNat 5436, memory := v4, stack := v8 :: v8 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5446, memory := v4, stack := v12 :: v10 :: v8 :: v8 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart3Model, v9, v10, v11, v12] using preparedProloguepart3_run ({s with memory := v4}) (v8) (v8) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h4 : runInstructions preparedProloguepart4Program {s with pc := UInt256.ofNat 5446, memory := v4, stack := v12 :: v10 :: v8 :: v8 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5456, memory := v4, stack := v16 :: v12 :: v10 :: v8 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart4Model, v13, v14, v15, v16] using preparedProloguepart4_run ({s with memory := v4}) (v12) (v10) (v8) (v8) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h5 : runInstructions preparedProloguepart5Program {s with pc := UInt256.ofNat 5456, memory := v4, stack := v16 :: v12 :: v10 :: v8 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5467, memory := v20, stack := v12 :: v10 :: v8 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart5Model, v17, v18, v19, v20] using preparedProloguepart5_run ({s with memory := v4}) (v16) (v12) (v10) (v8) (v15) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h6 : runInstructions preparedProloguepart6Program {s with pc := UInt256.ofNat 5467, memory := v20, stack := v12 :: v10 :: v8 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5480, memory := v23, stack := v24 :: v12 :: v10 :: v8 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart6Model, v21, v22, v23, v24] using preparedProloguepart6_run ({s with memory := v20}) (v12) (v10) (v8) (v15) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h7 : runInstructions preparedProloguepart7Program {s with pc := UInt256.ofNat 5480, memory := v23, stack := v24 :: v12 :: v10 :: v8 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5492, memory := v26, stack := v27 :: v8 :: v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart7Model, v25, v26, v27] using preparedProloguepart7_run ({s with memory := v23}) (v24) (v12) (v10) (v8) (v15) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h8 : runInstructions preparedProloguepart8Program {s with pc := UInt256.ofNat 5492, memory := v26, stack := v27 :: v8 :: v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5506, memory := v32, stack := v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart8Model, v28, v29, v30, v31, v32] using preparedProloguepart8_run ({s with memory := v26}) (v27) (v8) (v12) (v10) (v15) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h9 : runInstructions preparedProloguepart9Program {s with pc := UInt256.ofNat 5506, memory := v32, stack := v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5523, memory := v32, stack := (UInt256.ofNat 1099511627775) :: v35 :: v34 :: v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart9Model, v33, v34, v35] using preparedProloguepart9_run ({s with memory := v32}) (v12) (v10) (v15) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact
  have h10 : runInstructions preparedProloguepart10Program {s with pc := UInt256.ofNat 5523, memory := v32, stack := (UInt256.ofNat 1099511627775) :: v35 :: v34 :: v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} = some {s with pc := UInt256.ofNat 5524, memory := v32, stack := v36 :: v34 :: v12 :: v10 :: v15 :: v7 :: v5 :: v0 :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
    simpa only [preparedProloguepart10Model, v36] using preparedProloguepart10_run ({s with memory := v32}) ((UInt256.ofNat 1099511627775)) (v35) (v34) (v12) (v10) (v15) (v7) (v5) (v0) (f14) (f0) (f1) (f2) (f3) (f4) (f5) (f6) (f7) (f8) (f9) (f10) (f11) (f12) (f13) (f14) (f15) rest hcap hact (by rfl)
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 h10))))))))))

#print axioms preparedPrologue_run

def proSegProgram : List Instr := preparedPrologueProgram

private theorem prepared_model_eq (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) :
    preparedPrologueModel s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest = {s with pc := UInt256.ofNat 5524, memory := (proSegM7 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15), stack := (proSegV8_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV8_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_2 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_3 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_4 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV0_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
  simp (disch := decide) only [preparedPrologueModel, pro_o0, pro_mem, blk5344_mem, blk5352_o0, blk5352_o1, blk5352_o2, blk5352_o3, blk5352_o4, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem, blk5446_o0, blk5446_o1, proSegV0_0, proSegM0, proSegM1, proSegV2_0, proSegV2_1, proSegV2_2, proSegV2_3, proSegV2_4, proSegM2, proSegM3, proSegM4, proSegM5, proSegM6, proSegM7, proSegV8_0, proSegV8_1, addC, addA, addL, mulC, mmC, andC, read_disjoint]

theorem proSeg_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions proSegProgram {s with pc := UInt256.ofNat 5374, stack := f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} =
      some {s with pc := UInt256.ofNat 5524, memory := (proSegM7 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15), stack := (proSegV8_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV8_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_2 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_3 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV2_4 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: (proSegV0_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) :: f14 :: f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: f8 :: f9 :: f10 :: f11 :: f12 :: f13 :: f14 :: f15 :: rest} := by
  exact (preparedPrologue_run s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact).trans
    (congrArg some (prepared_model_eq s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest))

#print axioms proSeg_run
end CycleSubmission.R5.PrologueRun

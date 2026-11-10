import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace R9InvCompactExec
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open CycleSubmission.Prepared.Arithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

def stage0Part0Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Swap sA10),
   .op .POP,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA8),
   .op (.Dup dA1)]
def stage0Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := MachineState.readWord (s.memory) 768
  {s with pc := N 5580, memory := s.memory, stack := (v1) :: (w7) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest}
theorem stage0Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part0Program {s with pc := N 5568, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some (stage0Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage0Part0Program, stage0Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720, ha768, hf768]

def stage0Part1Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA0),
   .op .MUL,
   .op (.Dup dA14),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap sA11)]
def stage0Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w0)
  let v1 : W := (w13) * (v0)
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v1)
  {s with pc := N 5618, memory := s.memory, stack := (w11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (v2) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage0Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part1Program {s with pc := N 5580, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage0Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage0Part1Program, stage0Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage0Part2Program : List Instr :=
  [.op .POP,
   .op (.Dup dA10),
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA1),
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MULMOD]
def stage0Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w3) (w1) (w2)
  let v1 : W := UInt256.mulMod (w15) (w12) (w11)
  {s with pc := N 5626, memory := s.memory, stack := (v1) :: (v0) :: (w11) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage0Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part2Program {s with pc := N 5618, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage0Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage0Part2Program, stage0Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage0Part3Program : List Instr :=
  [.op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage0Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (N 2048) (v0) (w2)
  {s with pc := N 5631, memory := s.memory, stack := (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage0Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part3Program {s with pc := N 5626, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage0Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage0Part3Program, stage0Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage0Program : List Instr := (stage0Part0Program ++ (stage0Part1Program ++ (stage0Part2Program ++ (stage0Part3Program))))
def stage0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v1) * (v1)
  let v3 : W := (v0) * (v2)
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v3)
  let v5 : W := UInt256.mulMod (v1) (v1) (w7)
  let v6 : W := UInt256.mulMod (w11) (v4) (w7)
  let v7 : W := (v6) + (v5)
  let v8 : W := UInt256.mulMod (N 2048) (v7) (w7)
  {s with pc := N 5631, memory := s.memory, stack := (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest}
theorem stage0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Program {s with pc := N 5568, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some (stage0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v1) * (v1)
  let v3 : W := (v0) * (v2)
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v3)
  let v5 : W := UInt256.mulMod (v1) (v1) (w7)
  let v6 : W := UInt256.mulMod (w11) (v4) (w7)
  let v7 : W := (v6) + (v5)
  let v8 : W := UInt256.mulMod (N 2048) (v7) (w7)
  have h0 : runInstructions stage0Part0Program {s with pc := N 5568, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 5580, memory := s.memory, stack := (v1) :: (w7) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage0Part0Model, v0, v1] using stage0Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h1 : runInstructions stage0Part1Program {s with pc := N 5580, memory := s.memory, stack := (v1) :: (w7) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 5618, memory := s.memory, stack := (w8) :: (v1) :: (w7) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage0Part1Model, v2, v3, v4] using stage0Part1_run ({s with memory := s.memory}) (v1) (w7) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (v0) (w11) (w12) (w13) rest hcap hact
  have h2 : runInstructions stage0Part2Program {s with pc := N 5618, memory := s.memory, stack := (w8) :: (v1) :: (w7) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 5626, memory := s.memory, stack := (v6) :: (v5) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage0Part2Model, v5, v6] using stage0Part2_run ({s with memory := s.memory}) (w8) (v1) (w7) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (v0) (w11) (w12) (w13) rest hcap hact
  have h3 : runInstructions stage0Part3Program {s with pc := N 5626, memory := s.memory, stack := (v6) :: (v5) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 5631, memory := s.memory, stack := (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (v0) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage0Part3Model, v7, v8] using stage0Part3_run ({s with memory := s.memory}) (v6) (v5) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (v0) (w11) (w12) (w13) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 h3)))

def stage1Part0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op .ADD,
   .op (.Dup dA0),
   .push 2 768,
   .op .MSTORE,
   .op (.Dup dA9)]
def stage1Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (v0) + (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 768
  {s with pc := N 5643, memory := v2, stack := (w8) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage1Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part0Program {s with pc := N 5631, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage1Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage1Part0Program, stage1Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]

def stage1Part1Program : List Instr :=
  [.op (.Dup dA1),
   .op (.Dup dA7),
   .op .MULMOD,
   .op (.Swap sA0),
   .op (.Dup dA6),
   .op .MUL,
   .op (.Dup dA2),
   .op .ADD]
def stage1Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w6) (w1) (w0)
  let v1 : W := (w6) * (w1)
  let v2 : W := (w2) + (v1)
  {s with pc := N 5651, memory := s.memory, stack := (v2) :: (v0) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage1Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part1Program {s with pc := N 5643, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage1Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage1Part1Program, stage1Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Part2Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA13),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12)]
def stage1Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w12) * (w11)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w2) + (w1)
  {s with pc := N 5659, memory := s.memory, stack := (w12) :: (w10) :: (v2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage1Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part2Program {s with pc := N 5651, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage1Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage1Part2Program, stage1Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Part3Program : List Instr :=
  [.op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA14),
   .op (.Dup dA2),
   .op (.Swap sA4)]
def stage1Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w12) (w0) (w1)
  let v1 : W := (v0) + (w2)
  {s with pc := N 5667, memory := s.memory, stack := (w3) :: (w14) :: (w15) :: (w11) :: (v1) :: (w11) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage1Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part3Program {s with pc := N 5659, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage1Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage1Part3Program, stage1Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Part4Program : List Instr :=
  [.op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA11),
   .op .POP,
   .op .MULMOD,
   .op .ADD]
def stage1Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v0)
  let v2 : W := UInt256.mulMod (v1) (w2) (w3)
  let v3 : W := (v2) + (w4)
  {s with pc := N 5705, memory := s.memory, stack := (v3) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (v1) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage1Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part4Program {s with pc := N 5667, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage1Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage1Part4Program, stage1Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Part5Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]
def stage1Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) (w0) (w1)
  {s with pc := N 5709, memory := s.memory, stack := (v0) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage1Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part5Program {s with pc := N 5705, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage1Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage1Part5Program, stage1Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Program : List Instr := (stage1Part0Program ++ (stage1Part1Program ++ (stage1Part2Program ++ (stage1Part3Program ++ (stage1Part4Program ++ (stage1Part5Program))))))
def stage1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (v0) + (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 768
  let v3 : W := UInt256.mulMod (w4) (v1) (w8)
  let v4 : W := (w4) * (v1)
  let v5 : W := (w0) + (v4)
  let v6 : W := (w10) * (w9)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w0) + (v3)
  let v9 : W := UInt256.mulMod (w9) (w10) (w8)
  let v10 : W := (v9) + (v8)
  let v11 : W := (v7) * (w11)
  let v12 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v11)
  let v13 : W := UInt256.mulMod (v12) (w12) (w8)
  let v14 : W := (v13) + (v10)
  let v15 : W := UInt256.mulMod (N 2048) (v14) (w8)
  {s with pc := N 5709, memory := v2, stack := (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v12) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Program {s with pc := N 5631, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (v0) + (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 768
  let v3 : W := UInt256.mulMod (w4) (v1) (w8)
  let v4 : W := (w4) * (v1)
  let v5 : W := (w0) + (v4)
  let v6 : W := (w10) * (w9)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w0) + (v3)
  let v9 : W := UInt256.mulMod (w9) (w10) (w8)
  let v10 : W := (v9) + (v8)
  let v11 : W := (v7) * (w11)
  let v12 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v11)
  let v13 : W := UInt256.mulMod (v12) (w12) (w8)
  let v14 : W := (v13) + (v10)
  let v15 : W := UInt256.mulMod (N 2048) (v14) (w8)
  have h0 : runInstructions stage1Part0Program {s with pc := N 5631, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5643, memory := v2, stack := (w8) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage1Part0Model, v0, v1, v2] using stage1Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage1Part1Program {s with pc := N 5643, memory := v2, stack := (w8) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5651, memory := v2, stack := (v5) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage1Part1Model, v3, v4, v5] using stage1Part1_run ({s with memory := v2}) (w8) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage1Part2Program {s with pc := N 5651, memory := v2, stack := (v5) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5659, memory := v2, stack := (w10) :: (w8) :: (v8) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage1Part2Model, v6, v7, v8] using stage1Part2_run ({s with memory := v2}) (v5) (v3) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage1Part3Program {s with pc := N 5659, memory := v2, stack := (w10) :: (w8) :: (v8) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5667, memory := v2, stack := (v7) :: (w11) :: (w12) :: (w8) :: (v10) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage1Part3Model, v9, v10] using stage1Part3_run ({s with memory := v2}) (w10) (w8) (v8) (v7) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage1Part4Program {s with pc := N 5667, memory := v2, stack := (v7) :: (w11) :: (w12) :: (w8) :: (v10) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5705, memory := v2, stack := (v14) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v12) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage1Part4Model, v11, v12, v13, v14] using stage1Part4_run ({s with memory := v2}) (v7) (w11) (w12) (w8) (v10) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage1Part5Program {s with pc := N 5705, memory := v2, stack := (v14) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v12) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5709, memory := v2, stack := (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v12) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage1Part5Model, v15] using stage1Part5_run ({s with memory := v2}) (v14) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (v12) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 h5)))))

def stage2Part0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Dup dA11),
   .op .MUL,
   .op (.Dup dA6),
   .op (.Dup dA0),
   .op .MUL]
def stage2Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (w9) * (w1)
  let v2 : W := (w4) * (w4)
  {s with pc := N 5719, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage2Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part0Program {s with pc := N 5709, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage2Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage2Part0Program, stage2Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]

def stage2Part1Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA10),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA9),
   .op .MUL,
   .op (.Dup dA4)]
def stage2Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w8) (w2) (w11)
  let v1 : W := (w8) * (w2)
  {s with pc := N 5727, memory := s.memory, stack := (w3) :: (v1) :: (w0) :: (w1) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage2Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part1Program {s with pc := N 5719, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage2Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage2Part1Program, stage2Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part2Program : List Instr :=
  [.op .ADD,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA13),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA1)]
def stage2Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (v1) + (w3)
  let v3 : W := (w15) * (w12)
  let v4 : W := (v3) + (v2)
  {s with pc := N 5735, memory := s.memory, stack := (w5) :: (w4) :: (v4) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage2Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part2Program {s with pc := N 5727, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage2Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage2Part2Program, stage2Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD,
   .op (.Swap sA7),
   .op .MULMOD]
def stage2Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w6) + (w6)
  let v2 : W := UInt256.mulMod (w6) (w6) (w10)
  {s with pc := N 5743, memory := s.memory, stack := (v2) :: (v0) :: (w2) :: (w3) :: (w4) :: (w5) :: (v1) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage2Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part3Program {s with pc := N 5735, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage2Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage2Part3Program, stage2Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12)]
def stage2Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (w11) (w3) (w10)
  let v2 : W := (v1) + (v0)
  {s with pc := N 5751, memory := s.memory, stack := (w12) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage2Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part4Program {s with pc := N 5743, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage2Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage2Part4Program, stage2Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part5Program : List Instr :=
  [.op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA14),
   .op (.Dup dA2),
   .op (.Swap sA4)]
def stage2Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w10) (w0) (w1)
  let v1 : W := (v0) + (w2)
  {s with pc := N 5759, memory := s.memory, stack := (w3) :: (w14) :: (w15) :: (w11) :: (v1) :: (w11) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage2Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part5Program {s with pc := N 5751, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage2Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage2Part5Program, stage2Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part6Program : List Instr :=
  [.op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .push 1 192,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD]
def stage2Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 192
  let v3 : W := UInt256.mulMod (v1) (w2) (w3)
  let v4 : W := (v3) + (w4)
  {s with pc := N 5798, memory := v2, stack := (v4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage2Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part6Program {s with pc := N 5759, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage2Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage2Part6Program, stage2Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage2Part7Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]
def stage2Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) (w0) (w1)
  {s with pc := N 5802, memory := s.memory, stack := (v0) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage2Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part7Program {s with pc := N 5798, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage2Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage2Part7Program, stage2Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Program : List Instr := (stage2Part0Program ++ (stage2Part1Program ++ (stage2Part2Program ++ (stage2Part3Program ++ (stage2Part4Program ++ (stage2Part5Program ++ (stage2Part6Program ++ (stage2Part7Program))))))))
def stage2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (w9) * (w1)
  let v2 : W := (w4) * (w4)
  let v3 : W := UInt256.mulMod (w5) (v0) (w8)
  let v4 : W := (w5) * (v0)
  let v5 : W := (w0) + (v4)
  let v6 : W := (v5) + (v2)
  let v7 : W := (v6) + (v1)
  let v8 : W := (w10) * (w7)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w0) + (v3)
  let v11 : W := (w4) + (w4)
  let v12 : W := UInt256.mulMod (w4) (w4) (w8)
  let v13 : W := (v12) + (v10)
  let v14 : W := UInt256.mulMod (w9) (w1) (w8)
  let v15 : W := (v14) + (v13)
  let v16 : W := UInt256.mulMod (w7) (w10) (w8)
  let v17 : W := (v16) + (v15)
  let v18 : W := (v9) * (w11)
  let v19 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v18)
  let v20 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v19).toNat 32) 192
  let v21 : W := UInt256.mulMod (v19) (w12) (w8)
  let v22 : W := (v21) + (v17)
  let v23 : W := UInt256.mulMod (N 2048) (v22) (w8)
  {s with pc := N 5802, memory := v20, stack := (v23) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Program {s with pc := N 5709, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (w9) * (w1)
  let v2 : W := (w4) * (w4)
  let v3 : W := UInt256.mulMod (w5) (v0) (w8)
  let v4 : W := (w5) * (v0)
  let v5 : W := (w0) + (v4)
  let v6 : W := (v5) + (v2)
  let v7 : W := (v6) + (v1)
  let v8 : W := (w10) * (w7)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w0) + (v3)
  let v11 : W := (w4) + (w4)
  let v12 : W := UInt256.mulMod (w4) (w4) (w8)
  let v13 : W := (v12) + (v10)
  let v14 : W := UInt256.mulMod (w9) (w1) (w8)
  let v15 : W := (v14) + (v13)
  let v16 : W := UInt256.mulMod (w7) (w10) (w8)
  let v17 : W := (v16) + (v15)
  let v18 : W := (v9) * (w11)
  let v19 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v18)
  let v20 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v19).toNat 32) 192
  let v21 : W := UInt256.mulMod (v19) (w12) (w8)
  let v22 : W := (v21) + (v17)
  let v23 : W := UInt256.mulMod (N 2048) (v22) (w8)
  have h0 : runInstructions stage2Part0Program {s with pc := N 5709, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5719, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part0Model, v0, v1, v2] using stage2Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage2Part1Program {s with pc := N 5719, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5727, memory := s.memory, stack := (w0) :: (v4) :: (v2) :: (v1) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part1Model, v3, v4] using stage2Part1_run ({s with memory := s.memory}) (v2) (v1) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage2Part2Program {s with pc := N 5727, memory := s.memory, stack := (w0) :: (v4) :: (v2) :: (v1) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5735, memory := s.memory, stack := (w0) :: (v3) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part2Model, v5, v6, v7, v8, v9] using stage2Part2_run ({s with memory := s.memory}) (w0) (v4) (v2) (v1) (v3) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage2Part3Program {s with pc := N 5735, memory := s.memory, stack := (w0) :: (v3) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5743, memory := s.memory, stack := (v12) :: (v10) :: (v9) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part3Model, v10, v11, v12] using stage2Part3_run ({s with memory := s.memory}) (w0) (v3) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage2Part4Program {s with pc := N 5743, memory := s.memory, stack := (v12) :: (v10) :: (v9) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5751, memory := s.memory, stack := (w10) :: (w8) :: (v15) :: (v9) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part4Model, v13, v14, v15] using stage2Part4_run ({s with memory := s.memory}) (v12) (v10) (v9) (w1) (w2) (w3) (v11) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage2Part5Program {s with pc := N 5751, memory := s.memory, stack := (w10) :: (w8) :: (v15) :: (v9) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5759, memory := s.memory, stack := (v9) :: (w11) :: (w12) :: (w8) :: (v17) :: (w8) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part5Model, v16, v17] using stage2Part5_run ({s with memory := s.memory}) (w10) (w8) (v15) (v9) (w1) (w2) (w3) (v11) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage2Part6Program {s with pc := N 5759, memory := s.memory, stack := (v9) :: (w11) :: (w12) :: (w8) :: (v17) :: (w8) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5798, memory := v20, stack := (v22) :: (w8) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part6Model, v18, v19, v20, v21, v22] using stage2Part6_run ({s with memory := s.memory}) (v9) (w11) (w12) (w8) (v17) (w8) (w1) (w2) (w3) (v11) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage2Part7Program {s with pc := N 5798, memory := v20, stack := (v22) :: (w8) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5802, memory := v20, stack := (v23) :: (w1) :: (w2) :: (w3) :: (v11) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part7Model, v23] using stage2Part7_run ({s with memory := v20}) (v22) (w8) (w1) (w2) (w3) (v11) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 h7)))))))

def stage3Part0Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage3Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  {s with pc := N 5813, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage3Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part0Program {s with pc := N 5802, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage3Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part0Program, stage3Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha768, hf768]

def stage3Part1Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10),
   .op (.Dup dA8)]
def stage3Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w8) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := UInt256.mulMod (w3) (w1) (w2)
  {s with pc := N 5821, memory := s.memory, stack := (w9) :: (w12) :: (v2) :: (v1) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage3Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part1Program {s with pc := N 5813, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage3Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part1Program, stage3Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part2Program : List Instr :=
  [.op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA14)]
def stage3Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w8) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (w4) + (v1)
  let v3 : W := (w4) + (w3)
  {s with pc := N 5829, memory := s.memory, stack := (w17) :: (v3) :: (v2) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage3Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part2Program {s with pc := N 5821, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage3Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part2Program, stage3Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part3Program : List Instr :=
  [.op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def stage3Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w11) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (w9) * (w3)
  let v3 : W := (v2) + (v1)
  {s with pc := N 5837, memory := s.memory, stack := (w12) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage3Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part3Program {s with pc := N 5829, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage3Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part3Program, stage3Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part4Program : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA12)]
def stage3Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 5846, memory := s.memory, stack := (w11) :: (w15) :: (w10) :: (w2) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage3Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part4Program {s with pc := N 5837, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage3Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part4Program, stage3Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage3Part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage3Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w11) (w5) (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 5854, memory := s.memory, stack := (w12) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage3Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part5Program {s with pc := N 5846, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage3Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part5Program, stage3Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part6Program : List Instr :=
  [.op (.Dup dA12),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA14)]
def stage3Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod (v0) (w12) (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 5863, memory := s.memory, stack := (w13) :: (w14) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage3Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part6Program {s with pc := N 5854, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage3Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part6Program, stage3Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage3Part7Program : List Instr :=
  [.op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .push 0 0,
   .op .MSTORE]
def stage3Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w4) * (w0)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 0
  {s with pc := N 5901, memory := v2, stack := (v1) :: (w1) :: (w2) :: (w3) :: (w2) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage3Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part7Program {s with pc := N 5863, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage3Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part7Program, stage3Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage3Part8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage3Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w4)
  {s with pc := N 5907, memory := s.memory, stack := (v2) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage3Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part8Program {s with pc := N 5901, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage3Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part8Program, stage3Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Program : List Instr := (stage3Part0Program ++ (stage3Part1Program ++ (stage3Part2Program ++ (stage3Part3Program ++ (stage3Part4Program ++ (stage3Part5Program ++ (stage3Part6Program ++ (stage3Part7Program ++ (stage3Part8Program)))))))))
def stage3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := (w4) * (w5)
  let v4 : W := (v3) + (v2)
  let v5 : W := UInt256.mulMod (v0) (v1) (w8)
  let v6 : W := UInt256.mulMod (w4) (w5) (w8)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w0) + (v7)
  let v9 : W := (w0) + (v4)
  let v10 : W := (w9) * (w13)
  let v11 : W := (v10) + (v9)
  let v12 : W := (w7) * (w1)
  let v13 : W := (v12) + (v11)
  let v14 : W := MachineState.readWord (s.memory) 192
  let v15 : W := (v14) * (w10)
  let v16 : W := (v15) + (v13)
  let v17 : W := UInt256.mulMod (w9) (w13) (w8)
  let v18 : W := (v17) + (v8)
  let v19 : W := UInt256.mulMod (w7) (w1) (w8)
  let v20 : W := (v19) + (v18)
  let v21 : W := MachineState.readWord (s.memory) 192
  let v22 : W := UInt256.mulMod (v21) (w10) (w8)
  let v23 : W := (v22) + (v20)
  let v24 : W := (v16) * (w11)
  let v25 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v24)
  let v26 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v25).toNat 32) 0
  let v27 : W := UInt256.mulMod (v25) (w12) (w8)
  let v28 : W := (v27) + (v23)
  let v29 : W := UInt256.mulMod (N 2048) (v28) (w8)
  {s with pc := N 5907, memory := v26, stack := (v29) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Program {s with pc := N 5802, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := (w4) * (w5)
  let v4 : W := (v3) + (v2)
  let v5 : W := UInt256.mulMod (v0) (v1) (w8)
  let v6 : W := UInt256.mulMod (w4) (w5) (w8)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w0) + (v7)
  let v9 : W := (w0) + (v4)
  let v10 : W := (w9) * (w13)
  let v11 : W := (v10) + (v9)
  let v12 : W := (w7) * (w1)
  let v13 : W := (v12) + (v11)
  let v14 : W := MachineState.readWord (s.memory) 192
  let v15 : W := (v14) * (w10)
  let v16 : W := (v15) + (v13)
  let v17 : W := UInt256.mulMod (w9) (w13) (w8)
  let v18 : W := (v17) + (v8)
  let v19 : W := UInt256.mulMod (w7) (w1) (w8)
  let v20 : W := (v19) + (v18)
  let v21 : W := MachineState.readWord (s.memory) 192
  let v22 : W := UInt256.mulMod (v21) (w10) (w8)
  let v23 : W := (v22) + (v20)
  let v24 : W := (v16) * (w11)
  let v25 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v24)
  let v26 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v25).toNat 32) 0
  let v27 : W := UInt256.mulMod (v25) (w12) (w8)
  let v28 : W := (v27) + (v23)
  let v29 : W := UInt256.mulMod (N 2048) (v28) (w8)
  have h0 : runInstructions stage3Part0Program {s with pc := N 5802, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5813, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part0Model, v0, v1, v2] using stage3Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage3Part1Program {s with pc := N 5813, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5821, memory := s.memory, stack := (w5) :: (w8) :: (v5) :: (v4) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part1Model, v3, v4, v5] using stage3Part1_run ({s with memory := s.memory}) (v2) (v1) (w8) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage3Part2Program {s with pc := N 5821, memory := s.memory, stack := (w5) :: (w8) :: (v5) :: (v4) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5829, memory := s.memory, stack := (w13) :: (v9) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part2Model, v6, v7, v8, v9] using stage3Part2_run ({s with memory := s.memory}) (w5) (w8) (v5) (v4) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage3Part3Program {s with pc := N 5829, memory := s.memory, stack := (w13) :: (v9) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5837, memory := s.memory, stack := (w10) :: (v13) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part3Model, v10, v11, v12, v13] using stage3Part3_run ({s with memory := s.memory}) (w13) (v9) (v8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage3Part4Program {s with pc := N 5837, memory := s.memory, stack := (w10) :: (v13) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5846, memory := s.memory, stack := (w9) :: (w13) :: (w8) :: (v8) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part4Model, v14, v15, v16] using stage3Part4_run ({s with memory := s.memory}) (w10) (v13) (v8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage3Part5Program {s with pc := N 5846, memory := s.memory, stack := (w9) :: (w13) :: (w8) :: (v8) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5854, memory := s.memory, stack := (w8) :: (v20) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part5Model, v17, v18, v19, v20] using stage3Part5_run ({s with memory := s.memory}) (w9) (w13) (w8) (v8) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage3Part6Program {s with pc := N 5854, memory := s.memory, stack := (w8) :: (v20) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5863, memory := s.memory, stack := (w11) :: (w12) :: (w8) :: (v23) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part6Model, v21, v22, v23] using stage3Part6_run ({s with memory := s.memory}) (w8) (v20) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage3Part7Program {s with pc := N 5863, memory := s.memory, stack := (w11) :: (w12) :: (w8) :: (v23) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5901, memory := v26, stack := (v25) :: (w12) :: (w8) :: (v23) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part7Model, v24, v25, v26] using stage3Part7_run ({s with memory := s.memory}) (w11) (w12) (w8) (v23) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage3Part8Program {s with pc := N 5901, memory := v26, stack := (v25) :: (w12) :: (w8) :: (v23) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5907, memory := v26, stack := (v29) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage3Part8Model, v27, v28, v29] using stage3Part8_run ({s with memory := v26}) (v25) (w12) (w8) (v23) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

def stage4Part0Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage4Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  {s with pc := N 5918, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage4Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part0Program {s with pc := N 5907, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage4Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part0Program, stage4Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha768, hf768]

def stage4Part1Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10)]
def stage4Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := (w8) * (v0)
  let v2 : W := (v1) + (w0)
  let v3 : W := UInt256.mulMod (w3) (w1) (w2)
  {s with pc := N 5927, memory := s.memory, stack := (w12) :: (v3) :: (v2) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage4Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part1Program {s with pc := N 5918, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage4Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part1Program, stage4Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage4Part2Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1)]
def stage4Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := UInt256.mulMod (w7) (v0) (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := (w3) + (v2)
  {s with pc := N 5936, memory := s.memory, stack := (w3) :: (w2) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage4Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part2Program {s with pc := N 5927, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage4Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part2Program, stage4Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage4Part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA0),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA4),
   .op (.Dup dA11),
   .op .MUL]
def stage4Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w7) * (w7)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w11) * (w5)
  {s with pc := N 5944, memory := s.memory, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage4Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part3Program {s with pc := N 5936, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage4Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage4Part3Program, stage4Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .push 1 192,
   .op .MLOAD]
def stage4Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w9) * (w15)
  let v2 : W := (v1) + (v0)
  let v3 : W := MachineState.readWord (s.memory) 192
  {s with pc := N 5953, memory := s.memory, stack := (v3) :: (w3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage4Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part4Program {s with pc := N 5944, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage4Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part4Program, stage4Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage4Part5Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0)]
def stage4Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := MachineState.readWord (s.memory) 0
  let v3 : W := (v2) * (w13)
  let v4 : W := (v3) + (v1)
  {s with pc := N 5961, memory := s.memory, stack := (w3) :: (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage4Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part5Program {s with pc := N 5953, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage4Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part5Program, stage4Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage4Part6Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD,
   .op (.Swap sA8),
   .op .MULMOD,
   .op .ADD]
def stage4Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w6) + (w6)
  let v1 : W := UInt256.mulMod (w6) (w6) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 5969, memory := s.memory, stack := (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (v0) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage4Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part6Program {s with pc := N 5961, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage4Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage4Part6Program, stage4Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part7Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA5),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA10)]
def stage4Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w10) (w4) (w9)
  let v1 : W := (v0) + (w0)
  {s with pc := N 5977, memory := s.memory, stack := (w8) :: (w14) :: (w9) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage4Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part7Program {s with pc := N 5969, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage4Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage4Part7Program, stage4Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage4Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := UInt256.mulMod (v2) (w5) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 5986, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage4Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part8Program {s with pc := N 5977, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage4Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part8Program, stage4Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage4Part9Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA12),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14)]
def stage4Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod (v0) (w11) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 5994, memory := s.memory, stack := (w13) :: (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage4Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part9Program {s with pc := N 5986, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage4Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part9Program, stage4Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage4Part10Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0)]
def stage4Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w3) * (w14)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v0)
  {s with pc := N 6031, memory := s.memory, stack := (v1) :: (v1) :: (w0) :: (w1) :: (w2) :: (w1) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage4Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part10Program {s with pc := N 5994, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage4Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage4Part10Program, stage4Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part11Program : List Instr :=
  [.push 1 224,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage4Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w0).toNat 32) 224
  let v1 : W := UInt256.mulMod (w1) (w2) (w3)
  let v2 : W := (v1) + (w4)
  let v3 : W := UInt256.mulMod (N 2048) (v2) (w5)
  {s with pc := N 6040, memory := v0, stack := (v3) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage4Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part11Program {s with pc := N 6031, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage4Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part11Program, stage4Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage4Program : List Instr := (stage4Part0Program ++ (stage4Part1Program ++ (stage4Part2Program ++ (stage4Part3Program ++ (stage4Part4Program ++ (stage4Part5Program ++ (stage4Part6Program ++ (stage4Part7Program ++ (stage4Part8Program ++ (stage4Part9Program ++ (stage4Part10Program ++ (stage4Part11Program))))))))))))
def stage4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := (w4) * (v3)
  let v5 : W := (v4) + (v2)
  let v6 : W := UInt256.mulMod (v0) (v1) (w8)
  let v7 : W := MachineState.readWord (s.memory) 32
  let v8 : W := UInt256.mulMod (w4) (v7) (w8)
  let v9 : W := (v8) + (v6)
  let v10 : W := (w0) + (v9)
  let v11 : W := (w0) + (v5)
  let v12 : W := (w5) * (w5)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w9) * (w3)
  let v15 : W := (v14) + (v13)
  let v16 : W := (w7) * (w13)
  let v17 : W := (v16) + (v15)
  let v18 : W := MachineState.readWord (s.memory) 192
  let v19 : W := (v18) * (w1)
  let v20 : W := (v19) + (v17)
  let v21 : W := MachineState.readWord (s.memory) 0
  let v22 : W := (v21) * (w10)
  let v23 : W := (v22) + (v20)
  let v24 : W := (w5) + (w5)
  let v25 : W := UInt256.mulMod (w5) (w5) (w8)
  let v26 : W := (v25) + (v10)
  let v27 : W := UInt256.mulMod (w9) (w3) (w8)
  let v28 : W := (v27) + (v26)
  let v29 : W := UInt256.mulMod (w7) (w13) (w8)
  let v30 : W := (v29) + (v28)
  let v31 : W := MachineState.readWord (s.memory) 192
  let v32 : W := UInt256.mulMod (v31) (w1) (w8)
  let v33 : W := (v32) + (v30)
  let v34 : W := MachineState.readWord (s.memory) 0
  let v35 : W := UInt256.mulMod (v34) (w10) (w8)
  let v36 : W := (v35) + (v33)
  let v37 : W := (v23) * (w11)
  let v38 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v37)
  let v39 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v38).toNat 32) 224
  let v40 : W := UInt256.mulMod (v38) (w12) (w8)
  let v41 : W := (v40) + (v36)
  let v42 : W := UInt256.mulMod (N 2048) (v41) (w8)
  {s with pc := N 6040, memory := v39, stack := (v42) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Program {s with pc := N 5907, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := (w4) * (v3)
  let v5 : W := (v4) + (v2)
  let v6 : W := UInt256.mulMod (v0) (v1) (w8)
  let v7 : W := MachineState.readWord (s.memory) 32
  let v8 : W := UInt256.mulMod (w4) (v7) (w8)
  let v9 : W := (v8) + (v6)
  let v10 : W := (w0) + (v9)
  let v11 : W := (w0) + (v5)
  let v12 : W := (w5) * (w5)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w9) * (w3)
  let v15 : W := (v14) + (v13)
  let v16 : W := (w7) * (w13)
  let v17 : W := (v16) + (v15)
  let v18 : W := MachineState.readWord (s.memory) 192
  let v19 : W := (v18) * (w1)
  let v20 : W := (v19) + (v17)
  let v21 : W := MachineState.readWord (s.memory) 0
  let v22 : W := (v21) * (w10)
  let v23 : W := (v22) + (v20)
  let v24 : W := (w5) + (w5)
  let v25 : W := UInt256.mulMod (w5) (w5) (w8)
  let v26 : W := (v25) + (v10)
  let v27 : W := UInt256.mulMod (w9) (w3) (w8)
  let v28 : W := (v27) + (v26)
  let v29 : W := UInt256.mulMod (w7) (w13) (w8)
  let v30 : W := (v29) + (v28)
  let v31 : W := MachineState.readWord (s.memory) 192
  let v32 : W := UInt256.mulMod (v31) (w1) (w8)
  let v33 : W := (v32) + (v30)
  let v34 : W := MachineState.readWord (s.memory) 0
  let v35 : W := UInt256.mulMod (v34) (w10) (w8)
  let v36 : W := (v35) + (v33)
  let v37 : W := (v23) * (w11)
  let v38 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v37)
  let v39 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v38).toNat 32) 224
  let v40 : W := UInt256.mulMod (v38) (w12) (w8)
  let v41 : W := (v40) + (v36)
  let v42 : W := UInt256.mulMod (N 2048) (v41) (w8)
  have h0 : runInstructions stage4Part0Program {s with pc := N 5907, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5918, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part0Model, v0, v1, v2] using stage4Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage4Part1Program {s with pc := N 5918, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5927, memory := s.memory, stack := (w8) :: (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part1Model, v3, v4, v5, v6] using stage4Part1_run ({s with memory := s.memory}) (v2) (v1) (w8) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage4Part2Program {s with pc := N 5927, memory := s.memory, stack := (w8) :: (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5936, memory := s.memory, stack := (w0) :: (v5) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part2Model, v7, v8, v9, v10] using stage4Part2_run ({s with memory := s.memory}) (w8) (v6) (v5) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage4Part3Program {s with pc := N 5936, memory := s.memory, stack := (w0) :: (v5) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5944, memory := s.memory, stack := (v14) :: (v13) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part3Model, v11, v12, v13, v14] using stage4Part3_run ({s with memory := s.memory}) (w0) (v5) (v10) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage4Part4Program {s with pc := N 5944, memory := s.memory, stack := (v14) :: (v13) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5953, memory := s.memory, stack := (v18) :: (w1) :: (v17) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part4Model, v15, v16, v17, v18] using stage4Part4_run ({s with memory := s.memory}) (v14) (v13) (v10) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage4Part5Program {s with pc := N 5953, memory := s.memory, stack := (v18) :: (w1) :: (v17) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5961, memory := s.memory, stack := (v10) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part5Model, v19, v20, v21, v22, v23] using stage4Part5_run ({s with memory := s.memory}) (v18) (w1) (v17) (v10) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage4Part6Program {s with pc := N 5961, memory := s.memory, stack := (v10) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5969, memory := s.memory, stack := (v26) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part6Model, v24, v25, v26] using stage4Part6_run ({s with memory := s.memory}) (v10) (v23) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage4Part7Program {s with pc := N 5969, memory := s.memory, stack := (v26) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5977, memory := s.memory, stack := (w7) :: (w13) :: (w8) :: (v28) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part7Model, v27, v28] using stage4Part7_run ({s with memory := s.memory}) (v26) (v23) (w1) (w2) (w3) (w4) (v24) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage4Part8Program {s with pc := N 5977, memory := s.memory, stack := (w7) :: (w13) :: (w8) :: (v28) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5986, memory := s.memory, stack := (v33) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part8Model, v29, v30, v31, v32, v33] using stage4Part8_run ({s with memory := s.memory}) (w7) (w13) (w8) (v28) (v23) (w1) (w2) (w3) (w4) (v24) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage4Part9Program {s with pc := N 5986, memory := s.memory, stack := (v33) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 5994, memory := s.memory, stack := (w12) :: (w8) :: (v36) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part9Model, v34, v35, v36] using stage4Part9_run ({s with memory := s.memory}) (v33) (v23) (w1) (w2) (w3) (w4) (v24) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage4Part10Program {s with pc := N 5994, memory := s.memory, stack := (w12) :: (w8) :: (v36) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6031, memory := s.memory, stack := (v38) :: (v38) :: (w12) :: (w8) :: (v36) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part10Model, v37, v38] using stage4Part10_run ({s with memory := s.memory}) (w12) (w8) (v36) (v23) (w1) (w2) (w3) (w4) (v24) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage4Part11Program {s with pc := N 6031, memory := s.memory, stack := (v38) :: (v38) :: (w12) :: (w8) :: (v36) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6040, memory := v39, stack := (v42) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage4Part11Model, v39, v40, v41, v42] using stage4Part11_run ({s with memory := s.memory}) (v38) (v38) (w12) (w8) (v36) (w8) (w1) (w2) (w3) (w4) (v24) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

def stage5Part0Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage5Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  {s with pc := N 6051, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage5Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part0Program {s with pc := N 6040, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage5Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part0Program, stage5Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha768, hf768]

def stage5Part1Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA10)]
def stage5Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := (w8) * (v0)
  let v2 : W := (v1) + (w0)
  let v3 : W := MachineState.readWord (s.memory) 32
  {s with pc := N 6061, memory := s.memory, stack := (w9) :: (v3) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part1Program {s with pc := N 6051, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage5Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part1Program, stage5Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha32, hf32]

def stage5Part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA8)]
def stage5Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w5) (w3) (w4)
  let v3 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 6070, memory := s.memory, stack := (w10) :: (v3) :: (w14) :: (v2) :: (v1) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage5Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part2Program {s with pc := N 6061, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} = some (stage5Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part2Program, stage5Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]

def stage5Part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA10),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD]
def stage5Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 32
  let v3 : W := UInt256.mulMod (w10) (v2) (w13)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6079, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage5Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part3Program {s with pc := N 6070, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage5Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part3Program, stage5Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage5Part4Program : List Instr :=
  [.op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA7),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD]
def stage5Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w2) + (w0)
  let v1 : W := (w2) + (w1)
  let v2 : W := (w11) * (w8)
  let v3 : W := (v2) + (v1)
  {s with pc := N 6087, memory := s.memory, stack := (v3) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage5Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part4Program {s with pc := N 6079, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage5Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage5Part4Program, stage5Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part5Program : List Instr :=
  [.op (.Dup dA4),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 192,
   .op .MLOAD,
   .op .MUL]
def stage5Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w8) * (w4)
  let v1 : W := (v0) + (w0)
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := (v2) * (w14)
  {s with pc := N 6096, memory := s.memory, stack := (v3) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage5Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part5Program {s with pc := N 6087, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage5Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part5Program, stage5Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage5Part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA2),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def stage5Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 0
  let v2 : W := (v1) * (w3)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6103, memory := s.memory, stack := (w12) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage5Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part6Program {s with pc := N 6096, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage5Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part6Program, stage5Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage5Part7Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA8),
   .op (.Dup dA12)]
def stage5Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 6112, memory := s.memory, stack := (w11) :: (w8) :: (w10) :: (w2) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage5Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part7Program {s with pc := N 6103, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage5Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part7Program, stage5Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage5Part8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage5Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w11) (w7) (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 6120, memory := s.memory, stack := (w12) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part8Program {s with pc := N 6112, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage5Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage5Part8Program, stage5Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part9Program : List Instr :=
  [.op (.Dup dA15),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3)]
def stage5Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod (v0) (w15) (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 6128, memory := s.memory, stack := (w3) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage5Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part9Program {s with pc := N 6120, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage5Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part9Program, stage5Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage5Part10Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .push 1 224,
   .op .MLOAD]
def stage5Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod (v0) (w0) (w1)
  let v2 : W := (v1) + (w2)
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 6137, memory := s.memory, stack := (v3) :: (w13) :: (w11) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage5Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part10Program {s with pc := N 6128, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage5Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part10Program, stage5Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]

def stage5Part11Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA14),
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL]
def stage5Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := (w4) * (w15)
  {s with pc := N 6145, memory := s.memory, stack := (v2) :: (w16) :: (w12) :: (v1) :: (w12) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part11Program {s with pc := N 6137, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage5Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage5Part11Program, stage5Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part12Program : List Instr :=
  [.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .push 2 1216,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]
def stage5Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (w0)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v0).toNat 32) 1216
  let v2 : W := UInt256.mulMod (v0) (w1) (w2)
  let v3 : W := (v2) + (w3)
  {s with pc := N 6187, memory := v1, stack := (N 2048) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part12Program {s with pc := N 6145, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage5Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage5Part12Program, stage5Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]

def stage5Part13Program : List Instr :=
  [.op .MULMOD]
def stage5Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  {s with pc := N 6188, memory := s.memory, stack := (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage5Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part13Program {s with pc := N 6187, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage5Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage5Part13Program, stage5Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Program : List Instr := (stage5Part0Program ++ (stage5Part1Program ++ (stage5Part2Program ++ (stage5Part3Program ++ (stage5Part4Program ++ (stage5Part5Program ++ (stage5Part6Program ++ (stage5Part7Program ++ (stage5Part8Program ++ (stage5Part9Program ++ (stage5Part10Program ++ (stage5Part11Program ++ (stage5Part12Program ++ (stage5Part13Program))))))))))))))
def stage5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := MachineState.readWord (s.memory) 64
  let v4 : W := (w4) * (v3)
  let v5 : W := (v4) + (v2)
  let v6 : W := MachineState.readWord (s.memory) 32
  let v7 : W := (w5) * (v6)
  let v8 : W := (v7) + (v5)
  let v9 : W := UInt256.mulMod (v0) (v1) (w8)
  let v10 : W := MachineState.readWord (s.memory) 64
  let v11 : W := UInt256.mulMod (w4) (v10) (w8)
  let v12 : W := (v11) + (v9)
  let v13 : W := MachineState.readWord (s.memory) 32
  let v14 : W := UInt256.mulMod (w5) (v13) (w8)
  let v15 : W := (v14) + (v12)
  let v16 : W := (w0) + (v15)
  let v17 : W := (w0) + (v8)
  let v18 : W := (w9) * (w6)
  let v19 : W := (v18) + (v17)
  let v20 : W := (w7) * (w3)
  let v21 : W := (v20) + (v19)
  let v22 : W := MachineState.readWord (s.memory) 192
  let v23 : W := (v22) * (w13)
  let v24 : W := (v23) + (v21)
  let v25 : W := MachineState.readWord (s.memory) 0
  let v26 : W := (v25) * (w1)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 224
  let v29 : W := (v28) * (w10)
  let v30 : W := (v29) + (v27)
  let v31 : W := UInt256.mulMod (w9) (w6) (w8)
  let v32 : W := (v31) + (v16)
  let v33 : W := UInt256.mulMod (w7) (w3) (w8)
  let v34 : W := (v33) + (v32)
  let v35 : W := MachineState.readWord (s.memory) 192
  let v36 : W := UInt256.mulMod (v35) (w13) (w8)
  let v37 : W := (v36) + (v34)
  let v38 : W := MachineState.readWord (s.memory) 0
  let v39 : W := UInt256.mulMod (v38) (w1) (w8)
  let v40 : W := (v39) + (v37)
  let v41 : W := MachineState.readWord (s.memory) 224
  let v42 : W := UInt256.mulMod (v41) (w10) (w8)
  let v43 : W := (v42) + (v40)
  let v44 : W := (v30) * (w11)
  let v45 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v44)
  let v46 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v45).toNat 32) 1216
  let v47 : W := UInt256.mulMod (v45) (w12) (w8)
  let v48 : W := (v47) + (v43)
  let v49 : W := UInt256.mulMod (N 2048) (v48) (w8)
  {s with pc := N 6188, memory := v46, stack := (v49) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Program {s with pc := N 6040, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := MachineState.readWord (s.memory) 64
  let v4 : W := (w4) * (v3)
  let v5 : W := (v4) + (v2)
  let v6 : W := MachineState.readWord (s.memory) 32
  let v7 : W := (w5) * (v6)
  let v8 : W := (v7) + (v5)
  let v9 : W := UInt256.mulMod (v0) (v1) (w8)
  let v10 : W := MachineState.readWord (s.memory) 64
  let v11 : W := UInt256.mulMod (w4) (v10) (w8)
  let v12 : W := (v11) + (v9)
  let v13 : W := MachineState.readWord (s.memory) 32
  let v14 : W := UInt256.mulMod (w5) (v13) (w8)
  let v15 : W := (v14) + (v12)
  let v16 : W := (w0) + (v15)
  let v17 : W := (w0) + (v8)
  let v18 : W := (w9) * (w6)
  let v19 : W := (v18) + (v17)
  let v20 : W := (w7) * (w3)
  let v21 : W := (v20) + (v19)
  let v22 : W := MachineState.readWord (s.memory) 192
  let v23 : W := (v22) * (w13)
  let v24 : W := (v23) + (v21)
  let v25 : W := MachineState.readWord (s.memory) 0
  let v26 : W := (v25) * (w1)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 224
  let v29 : W := (v28) * (w10)
  let v30 : W := (v29) + (v27)
  let v31 : W := UInt256.mulMod (w9) (w6) (w8)
  let v32 : W := (v31) + (v16)
  let v33 : W := UInt256.mulMod (w7) (w3) (w8)
  let v34 : W := (v33) + (v32)
  let v35 : W := MachineState.readWord (s.memory) 192
  let v36 : W := UInt256.mulMod (v35) (w13) (w8)
  let v37 : W := (v36) + (v34)
  let v38 : W := MachineState.readWord (s.memory) 0
  let v39 : W := UInt256.mulMod (v38) (w1) (w8)
  let v40 : W := (v39) + (v37)
  let v41 : W := MachineState.readWord (s.memory) 224
  let v42 : W := UInt256.mulMod (v41) (w10) (w8)
  let v43 : W := (v42) + (v40)
  let v44 : W := (v30) * (w11)
  let v45 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v44)
  let v46 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v45).toNat 32) 1216
  let v47 : W := UInt256.mulMod (v45) (w12) (w8)
  let v48 : W := (v47) + (v43)
  let v49 : W := UInt256.mulMod (N 2048) (v48) (w8)
  have h0 : runInstructions stage5Part0Program {s with pc := N 6040, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6051, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part0Model, v0, v1, v2] using stage5Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage5Part1Program {s with pc := N 6051, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6061, memory := s.memory, stack := (w5) :: (v6) :: (v5) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part1Model, v3, v4, v5, v6] using stage5Part1_run ({s with memory := s.memory}) (v2) (v1) (w8) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage5Part2Program {s with pc := N 6061, memory := s.memory, stack := (w5) :: (v6) :: (v5) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6070, memory := s.memory, stack := (w4) :: (v10) :: (w8) :: (v9) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part2Model, v7, v8, v9, v10] using stage5Part2_run ({s with memory := s.memory}) (w5) (v6) (v5) (v1) (w8) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage5Part3Program {s with pc := N 6070, memory := s.memory, stack := (w4) :: (v10) :: (w8) :: (v9) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6079, memory := s.memory, stack := (v15) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part3Model, v11, v12, v13, v14, v15] using stage5Part3_run ({s with memory := s.memory}) (w4) (v10) (w8) (v9) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage5Part4Program {s with pc := N 6079, memory := s.memory, stack := (v15) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6087, memory := s.memory, stack := (v19) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part4Model, v16, v17, v18, v19] using stage5Part4_run ({s with memory := s.memory}) (v15) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage5Part5Program {s with pc := N 6087, memory := s.memory, stack := (v19) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6096, memory := s.memory, stack := (v23) :: (v21) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part5Model, v20, v21, v22, v23] using stage5Part5_run ({s with memory := s.memory}) (v19) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage5Part6Program {s with pc := N 6096, memory := s.memory, stack := (v23) :: (v21) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6103, memory := s.memory, stack := (w10) :: (v27) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part6Model, v24, v25, v26, v27] using stage5Part6_run ({s with memory := s.memory}) (v23) (v21) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage5Part7Program {s with pc := N 6103, memory := s.memory, stack := (w10) :: (v27) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6112, memory := s.memory, stack := (w9) :: (w6) :: (w8) :: (v16) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part7Model, v28, v29, v30] using stage5Part7_run ({s with memory := s.memory}) (w10) (v27) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage5Part8Program {s with pc := N 6112, memory := s.memory, stack := (w9) :: (w6) :: (w8) :: (v16) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6120, memory := s.memory, stack := (w8) :: (v34) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part8Model, v31, v32, v33, v34] using stage5Part8_run ({s with memory := s.memory}) (w9) (w6) (w8) (v16) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage5Part9Program {s with pc := N 6120, memory := s.memory, stack := (w8) :: (v34) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6128, memory := s.memory, stack := (w1) :: (w8) :: (v37) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part9Model, v35, v36, v37] using stage5Part9_run ({s with memory := s.memory}) (w8) (v34) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage5Part10Program {s with pc := N 6128, memory := s.memory, stack := (w1) :: (w8) :: (v37) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6137, memory := s.memory, stack := (v41) :: (w10) :: (w8) :: (v40) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part10Model, v38, v39, v40, v41] using stage5Part10_run ({s with memory := s.memory}) (w1) (w8) (v37) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage5Part11Program {s with pc := N 6137, memory := s.memory, stack := (v41) :: (w10) :: (w8) :: (v40) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6145, memory := s.memory, stack := (v44) :: (w12) :: (w8) :: (v43) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part11Model, v42, v43, v44] using stage5Part11_run ({s with memory := s.memory}) (v41) (w10) (w8) (v40) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage5Part12Program {s with pc := N 6145, memory := s.memory, stack := (v44) :: (w12) :: (w8) :: (v43) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6187, memory := v46, stack := (N 2048) :: (v48) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part12Model, v45, v46, v47, v48] using stage5Part12_run ({s with memory := s.memory}) (v44) (w12) (w8) (v43) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions stage5Part13Program {s with pc := N 6187, memory := v46, stack := (N 2048) :: (v48) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6188, memory := v46, stack := (v49) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage5Part13Model, v49] using stage5Part13_run ({s with memory := v46}) (N 2048) (v48) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

def stage6Part0Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage6Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  {s with pc := N 6199, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage6Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part0Program {s with pc := N 6188, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage6Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part0Program, stage6Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha768, hf768]

def stage6Part1Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA10)]
def stage6Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := (w8) * (v0)
  let v2 : W := (v1) + (w0)
  let v3 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 6209, memory := s.memory, stack := (w9) :: (v3) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage6Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part1Program {s with pc := N 6199, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage6Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part1Program, stage6Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha64, hf64]

def stage6Part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA8)]
def stage6Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w5) (w3) (w4)
  let v3 : W := MachineState.readWord (s.memory) 96
  {s with pc := N 6218, memory := s.memory, stack := (w10) :: (v3) :: (w14) :: (v2) :: (v1) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage6Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part2Program {s with pc := N 6209, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} = some (stage6Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part2Program, stage6Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]

def stage6Part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA10),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD]
def stage6Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := UInt256.mulMod (w10) (v2) (w13)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6227, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage6Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part3Program {s with pc := N 6218, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage6Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part3Program, stage6Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]

def stage6Part4Program : List Instr :=
  [.op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA0),
   .op .MUL]
def stage6Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w2) + (w0)
  let v1 : W := (w2) + (w1)
  let v2 : W := MachineState.readWord (s.memory) 32
  let v3 : W := (v2) * (v2)
  {s with pc := N 6236, memory := s.memory, stack := (v3) :: (v1) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part4Program {s with pc := N 6227, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part4Program, stage6Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage6Part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA3),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA7),
   .op (.Dup dA9),
   .op .MUL]
def stage6Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w11) * (w4)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w9) * (w8)
  {s with pc := N 6244, memory := s.memory, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part5Program {s with pc := N 6236, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage6Part5Program, stage6Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA4),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14)]
def stage6Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 192
  let v2 : W := (v1) * (w5)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6252, memory := s.memory, stack := (w15) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part6Program {s with pc := N 6244, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part6Program, stage6Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage6Part7Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .push 1 224,
   .op .MLOAD,
   .op .MUL]
def stage6Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 224
  let v4 : W := (v3) * (w3)
  {s with pc := N 6261, memory := s.memory, stack := (v4) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part7Program {s with pc := N 6252, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part7Program, stage6Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]

def stage6Part8Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA11),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9)]
def stage6Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 1216
  let v2 : W := (v1) * (w12)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6271, memory := s.memory, stack := (w10) :: (w2) :: (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part8Program {s with pc := N 6261, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part8Program, stage6Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]

def stage6Part9Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD,
   .push 1 32,
   .op .MSTORE]
def stage6Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := (v0) + (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 32
  {s with pc := N 6281, memory := v2, stack := (v0) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part9Program {s with pc := N 6271, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part9Program, stage6Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage6Part10Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA4),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage6Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w13) (w6) (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 6289, memory := s.memory, stack := (w12) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage6Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part10Program {s with pc := N 6281, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage6Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage6Part10Program, stage6Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part11Program : List Instr :=
  [.op (.Dup dA8),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5),
   .push 1 192,
   .op .MLOAD]
def stage6Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w9) (w8) (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := MachineState.readWord (s.memory) 192
  {s with pc := N 6298, memory := s.memory, stack := (v2) :: (w5) :: (w10) :: (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part11Program {s with pc := N 6289, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part11Program, stage6Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage6Part12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage6Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 0
  let v3 : W := UInt256.mulMod (v2) (w17) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6306, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage6Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part12Program {s with pc := N 6298, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage6Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part12Program, stage6Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage6Part13Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA3),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12)]
def stage6Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod (v0) (w2) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 6315, memory := s.memory, stack := (w11) :: (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage6Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part13Program {s with pc := N 6306, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage6Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part13Program, stage6Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage6Part14Program : List Instr :=
  [.push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA14),
   .op (.Dup dA2)]
def stage6Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := UInt256.mulMod (v0) (w0) (w1)
  let v2 : W := (v1) + (w2)
  {s with pc := N 6325, memory := s.memory, stack := (w11) :: (w14) :: (w15) :: (w11) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage6Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part14Program {s with pc := N 6315, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage6Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part14Program, stage6Part14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]

def stage6Part15Program : List Instr :=
  [.op (.Swap sA4),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .push 2 1248,
   .op .MSTORE,
   .op .MULMOD]
def stage6Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := (w5) * (w1)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 1248
  let v3 : W := UInt256.mulMod (v1) (w2) (w3)
  {s with pc := N 6365, memory := v2, stack := (v3) :: (w4) :: (w0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage6Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part15Program {s with pc := N 6325, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage6Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage6Part15Program, stage6Part15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]

def stage6Part16Program : List Instr :=
  [.op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage6Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (N 2048) (v0) (w2)
  {s with pc := N 6370, memory := s.memory, stack := (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part16Program {s with pc := N 6365, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage6Part16Program, stage6Part16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Program : List Instr := (stage6Part0Program ++ (stage6Part1Program ++ (stage6Part2Program ++ (stage6Part3Program ++ (stage6Part4Program ++ (stage6Part5Program ++ (stage6Part6Program ++ (stage6Part7Program ++ (stage6Part8Program ++ (stage6Part9Program ++ (stage6Part10Program ++ (stage6Part11Program ++ (stage6Part12Program ++ (stage6Part13Program ++ (stage6Part14Program ++ (stage6Part15Program ++ (stage6Part16Program)))))))))))))))))
def stage6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := MachineState.readWord (s.memory) 96
  let v4 : W := (w4) * (v3)
  let v5 : W := (v4) + (v2)
  let v6 : W := MachineState.readWord (s.memory) 64
  let v7 : W := (w5) * (v6)
  let v8 : W := (v7) + (v5)
  let v9 : W := UInt256.mulMod (v0) (v1) (w8)
  let v10 : W := MachineState.readWord (s.memory) 96
  let v11 : W := UInt256.mulMod (w4) (v10) (w8)
  let v12 : W := (v11) + (v9)
  let v13 : W := MachineState.readWord (s.memory) 64
  let v14 : W := UInt256.mulMod (w5) (v13) (w8)
  let v15 : W := (v14) + (v12)
  let v16 : W := (w0) + (v15)
  let v17 : W := (w0) + (v8)
  let v18 : W := MachineState.readWord (s.memory) 32
  let v19 : W := (v18) * (v18)
  let v20 : W := (v19) + (v17)
  let v21 : W := (w9) * (w2)
  let v22 : W := (v21) + (v20)
  let v23 : W := (w7) * (w6)
  let v24 : W := (v23) + (v22)
  let v25 : W := MachineState.readWord (s.memory) 192
  let v26 : W := (v25) * (w3)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 0
  let v29 : W := (v28) * (w13)
  let v30 : W := (v29) + (v27)
  let v31 : W := MachineState.readWord (s.memory) 224
  let v32 : W := (v31) * (w1)
  let v33 : W := (v32) + (v30)
  let v34 : W := MachineState.readWord (s.memory) 1216
  let v35 : W := (v34) * (w10)
  let v36 : W := (v35) + (v33)
  let v37 : W := MachineState.readWord (s.memory) 32
  let v38 : W := (v37) + (v37)
  let v39 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v38).toNat 32) 32
  let v40 : W := UInt256.mulMod (v37) (v37) (w8)
  let v41 : W := (v40) + (v16)
  let v42 : W := UInt256.mulMod (w9) (w2) (w8)
  let v43 : W := (v42) + (v41)
  let v44 : W := UInt256.mulMod (w7) (w6) (w8)
  let v45 : W := (v44) + (v43)
  let v46 : W := MachineState.readWord (v39) 192
  let v47 : W := UInt256.mulMod (v46) (w3) (w8)
  let v48 : W := (v47) + (v45)
  let v49 : W := MachineState.readWord (v39) 0
  let v50 : W := UInt256.mulMod (v49) (w13) (w8)
  let v51 : W := (v50) + (v48)
  let v52 : W := MachineState.readWord (v39) 224
  let v53 : W := UInt256.mulMod (v52) (w1) (w8)
  let v54 : W := (v53) + (v51)
  let v55 : W := MachineState.readWord (v39) 1216
  let v56 : W := UInt256.mulMod (v55) (w10) (w8)
  let v57 : W := (v56) + (v54)
  let v58 : W := (v36) * (w11)
  let v59 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v58)
  let v60 : ByteArray := MachineState.writeBytes (v39) (Data.Bytes.natToBytesPadded (v59).toNat 32) 1248
  let v61 : W := UInt256.mulMod (v59) (w12) (w8)
  let v62 : W := (v61) + (v57)
  let v63 : W := UInt256.mulMod (N 2048) (v62) (w8)
  {s with pc := N 6370, memory := v60, stack := (v63) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Program {s with pc := N 6188, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := (v0) * (v1)
  let v3 : W := MachineState.readWord (s.memory) 96
  let v4 : W := (w4) * (v3)
  let v5 : W := (v4) + (v2)
  let v6 : W := MachineState.readWord (s.memory) 64
  let v7 : W := (w5) * (v6)
  let v8 : W := (v7) + (v5)
  let v9 : W := UInt256.mulMod (v0) (v1) (w8)
  let v10 : W := MachineState.readWord (s.memory) 96
  let v11 : W := UInt256.mulMod (w4) (v10) (w8)
  let v12 : W := (v11) + (v9)
  let v13 : W := MachineState.readWord (s.memory) 64
  let v14 : W := UInt256.mulMod (w5) (v13) (w8)
  let v15 : W := (v14) + (v12)
  let v16 : W := (w0) + (v15)
  let v17 : W := (w0) + (v8)
  let v18 : W := MachineState.readWord (s.memory) 32
  let v19 : W := (v18) * (v18)
  let v20 : W := (v19) + (v17)
  let v21 : W := (w9) * (w2)
  let v22 : W := (v21) + (v20)
  let v23 : W := (w7) * (w6)
  let v24 : W := (v23) + (v22)
  let v25 : W := MachineState.readWord (s.memory) 192
  let v26 : W := (v25) * (w3)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 0
  let v29 : W := (v28) * (w13)
  let v30 : W := (v29) + (v27)
  let v31 : W := MachineState.readWord (s.memory) 224
  let v32 : W := (v31) * (w1)
  let v33 : W := (v32) + (v30)
  let v34 : W := MachineState.readWord (s.memory) 1216
  let v35 : W := (v34) * (w10)
  let v36 : W := (v35) + (v33)
  let v37 : W := MachineState.readWord (s.memory) 32
  let v38 : W := (v37) + (v37)
  let v39 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v38).toNat 32) 32
  let v40 : W := UInt256.mulMod (v37) (v37) (w8)
  let v41 : W := (v40) + (v16)
  let v42 : W := UInt256.mulMod (w9) (w2) (w8)
  let v43 : W := (v42) + (v41)
  let v44 : W := UInt256.mulMod (w7) (w6) (w8)
  let v45 : W := (v44) + (v43)
  let v46 : W := MachineState.readWord (v39) 192
  let v47 : W := UInt256.mulMod (v46) (w3) (w8)
  let v48 : W := (v47) + (v45)
  let v49 : W := MachineState.readWord (v39) 0
  let v50 : W := UInt256.mulMod (v49) (w13) (w8)
  let v51 : W := (v50) + (v48)
  let v52 : W := MachineState.readWord (v39) 224
  let v53 : W := UInt256.mulMod (v52) (w1) (w8)
  let v54 : W := (v53) + (v51)
  let v55 : W := MachineState.readWord (v39) 1216
  let v56 : W := UInt256.mulMod (v55) (w10) (w8)
  let v57 : W := (v56) + (v54)
  let v58 : W := (v36) * (w11)
  let v59 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v58)
  let v60 : ByteArray := MachineState.writeBytes (v39) (Data.Bytes.natToBytesPadded (v59).toNat 32) 1248
  let v61 : W := UInt256.mulMod (v59) (w12) (w8)
  let v62 : W := (v61) + (v57)
  let v63 : W := UInt256.mulMod (N 2048) (v62) (w8)
  have h0 : runInstructions stage6Part0Program {s with pc := N 6188, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6199, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part0Model, v0, v1, v2] using stage6Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage6Part1Program {s with pc := N 6199, memory := s.memory, stack := (v2) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6209, memory := s.memory, stack := (w5) :: (v6) :: (v5) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part1Model, v3, v4, v5, v6] using stage6Part1_run ({s with memory := s.memory}) (v2) (v1) (w8) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage6Part2Program {s with pc := N 6209, memory := s.memory, stack := (w5) :: (v6) :: (v5) :: (v1) :: (w8) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6218, memory := s.memory, stack := (w4) :: (v10) :: (w8) :: (v9) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part2Model, v7, v8, v9, v10] using stage6Part2_run ({s with memory := s.memory}) (w5) (v6) (v5) (v1) (w8) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage6Part3Program {s with pc := N 6218, memory := s.memory, stack := (w4) :: (v10) :: (w8) :: (v9) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6227, memory := s.memory, stack := (v15) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part3Model, v11, v12, v13, v14, v15] using stage6Part3_run ({s with memory := s.memory}) (w4) (v10) (w8) (v9) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage6Part4Program {s with pc := N 6227, memory := s.memory, stack := (v15) :: (v8) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6236, memory := s.memory, stack := (v19) :: (v17) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part4Model, v16, v17, v18, v19] using stage6Part4_run ({s with memory := s.memory}) (v15) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage6Part5Program {s with pc := N 6236, memory := s.memory, stack := (v19) :: (v17) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6244, memory := s.memory, stack := (v23) :: (v22) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part5Model, v20, v21, v22, v23] using stage6Part5_run ({s with memory := s.memory}) (v19) (v17) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage6Part6Program {s with pc := N 6244, memory := s.memory, stack := (v23) :: (v22) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6252, memory := s.memory, stack := (w13) :: (v27) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part6Model, v24, v25, v26, v27] using stage6Part6_run ({s with memory := s.memory}) (v23) (v22) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage6Part7Program {s with pc := N 6252, memory := s.memory, stack := (w13) :: (v27) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6261, memory := s.memory, stack := (v32) :: (v30) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part7Model, v28, v29, v30, v31, v32] using stage6Part7_run ({s with memory := s.memory}) (w13) (v27) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage6Part8Program {s with pc := N 6261, memory := s.memory, stack := (v32) :: (v30) :: (v16) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6271, memory := s.memory, stack := (w8) :: (v16) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part8Model, v33, v34, v35, v36] using stage6Part8_run ({s with memory := s.memory}) (v32) (v30) (v16) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage6Part9Program {s with pc := N 6271, memory := s.memory, stack := (w8) :: (v16) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6281, memory := v39, stack := (v37) :: (v37) :: (w8) :: (v16) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part9Model, v37, v38, v39] using stage6Part9_run ({s with memory := s.memory}) (w8) (v16) (v36) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage6Part10Program {s with pc := N 6281, memory := v39, stack := (v37) :: (v37) :: (w8) :: (v16) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6289, memory := v39, stack := (w8) :: (v43) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part10Model, v40, v41, v42, v43] using stage6Part10_run ({s with memory := v39}) (v37) (v37) (w8) (v16) (v36) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage6Part11Program {s with pc := N 6289, memory := v39, stack := (w8) :: (v43) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6298, memory := v39, stack := (v46) :: (w3) :: (w8) :: (v45) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part11Model, v44, v45, v46] using stage6Part11_run ({s with memory := v39}) (w8) (v43) (v36) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage6Part12Program {s with pc := N 6298, memory := v39, stack := (v46) :: (w3) :: (w8) :: (v45) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6306, memory := v39, stack := (v51) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part12Model, v47, v48, v49, v50, v51] using stage6Part12_run ({s with memory := v39}) (v46) (w3) (w8) (v45) (v36) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions stage6Part13Program {s with pc := N 6306, memory := v39, stack := (v51) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6315, memory := v39, stack := (w10) :: (w8) :: (v54) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part13Model, v52, v53, v54] using stage6Part13_run ({s with memory := v39}) (v51) (v36) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h14 : runInstructions stage6Part14Program {s with pc := N 6315, memory := v39, stack := (w10) :: (w8) :: (v54) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6325, memory := v39, stack := (w8) :: (w11) :: (w12) :: (w8) :: (v57) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part14Model, v55, v56, v57] using stage6Part14_run ({s with memory := v39}) (w10) (w8) (v54) (v36) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h15 : runInstructions stage6Part15Program {s with pc := N 6325, memory := v39, stack := (w8) :: (w11) :: (w12) :: (w8) :: (v57) :: (v36) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6365, memory := v60, stack := (v61) :: (v57) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part15Model, v58, v59, v60, v61] using stage6Part15_run ({s with memory := v39}) (w8) (w11) (w12) (w8) (v57) (v36) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h16 : runInstructions stage6Part16Program {s with pc := N 6365, memory := v60, stack := (v61) :: (v57) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6370, memory := v60, stack := (v63) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage6Part16Model, v62, v63] using stage6Part16_run ({s with memory := v60}) (v61) (v57) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 h16))))))))))))))))

def stage7Part0Program : List Instr :=
  [.push 2 1568,
   .op .MLOAD,
   .op (.Swap sA7),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA10),
   .push 2 768,
   .op .MLOAD]
def stage7Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 768
  {s with pc := N 6383, memory := s.memory, stack := (v2) :: (w8) :: (v1) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage7Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part0Program {s with pc := N 6370, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage7Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1568 : (1568 : W).toNat = 1568 := rfl
  have hf1568 := Monpro.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part0Program, stage7Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1568, hf1568, ha768, hf768, ha160, hf160]

def stage7Part1Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL,
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]
def stage7Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w2) * (w0)
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) * (w8)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6392, memory := s.memory, stack := (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage7Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part1Program {s with pc := N 6383, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage7Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part1Program, stage7Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]

def stage7Part2Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD]
def stage7Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := (w10) * (v0)
  let v2 : W := (v1) + (w0)
  let v3 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 6401, memory := s.memory, stack := (v3) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage7Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part2Program {s with pc := N 6392, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage7Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part2Program, stage7Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha64, hf64]

def stage7Part3Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA11)]
def stage7Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := UInt256.mulMod (w4) (w2) (w3)
  {s with pc := N 6409, memory := s.memory, stack := (w14) :: (v3) :: (v2) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage7Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part3Program {s with pc := N 6401, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} = some (stage7Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part3Program, stage7Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage7Part4Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA11),
   .push 1 96,
   .op .MLOAD]
def stage7Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := UInt256.mulMod (w8) (v0) (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 96
  {s with pc := N 6419, memory := s.memory, stack := (v3) :: (w12) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage7Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part4Program {s with pc := N 6409, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage7Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part4Program, stage7Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha96, hf96]

def stage7Part5Program : List Instr :=
  [.op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA11),
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]
def stage7Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w10) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := MachineState.readWord (s.memory) 32
  {s with pc := N 6429, memory := s.memory, stack := (v3) :: (v2) :: (w13) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage7Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part5Program {s with pc := N 6419, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage7Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part5Program, stage7Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha32, hf32]

def stage7Part6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA3),
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA10)]
def stage7Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := (w6) + (v1)
  let v3 : W := (w6) + (w4)
  {s with pc := N 6437, memory := s.memory, stack := (w13) :: (w15) :: (v3) :: (w5) :: (v2) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage7Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part6Program {s with pc := N 6429, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} = some (stage7Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage7Part6Program, stage7Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part7Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup dA4),
   .op (.Dup dA2),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA8)]
def stage7Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (w3) * (w6)
  let v3 : W := (v2) + (v1)
  {s with pc := N 6444, memory := s.memory, stack := (w10) :: (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage7Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part7Program {s with pc := N 6437, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage7Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage7Part7Program, stage7Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part8Program : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]
def stage7Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 0
  let v4 : W := (v3) * (w6)
  {s with pc := N 6453, memory := s.memory, stack := (v4) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part8Program {s with pc := N 6444, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage7Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part8Program, stage7Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192, ha0, hf0]

def stage7Part9Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA15),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3)]
def stage7Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 224
  let v2 : W := (v1) * (w16)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6461, memory := s.memory, stack := (w4) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part9Program {s with pc := N 6453, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage7Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part9Program, stage7Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage7Part10Program : List Instr :=
  [.push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL]
def stage7Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 1248
  let v4 : W := (v3) * (w13)
  {s with pc := N 6473, memory := s.memory, stack := (v4) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part10Program {s with pc := N 6461, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage7Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part10Program, stage7Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216, ha1248, hf1248]

def stage7Part11Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA10),
   .op (.Dup dA12),
   .op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10)]
def stage7Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (w10) (w12) (w11)
  let v2 : W := (v1) + (w3)
  {s with pc := N 6481, memory := s.memory, stack := (w11) :: (v2) :: (w2) :: (v0) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part11Program {s with pc := N 6473, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage7Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage7Part11Program, stage7Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part12Program : List Instr :=
  [.op (.Dup dA5),
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .push 2 1088,
   .op .MSTORE,
   .op (.Dup dA9)]
def stage7Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w2) (w5) (w0)
  let v1 : W := (v0) + (w1)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w2).toNat 32) 1088
  {s with pc := N 6491, memory := v2, stack := (w11) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part12Program {s with pc := N 6481, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage7Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part12Program, stage7Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]

def stage7Part13Program : List Instr :=
  [.op (.Dup dA8),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5)]
def stage7Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod (v0) (w8) (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 6499, memory := s.memory, stack := (w5) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage7Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part13Program {s with pc := N 6491, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage7Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part13Program, stage7Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage7Part14Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .push 1 224,
   .op .MLOAD]
def stage7Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod (v0) (w0) (w1)
  let v2 : W := (v1) + (w2)
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 6508, memory := s.memory, stack := (v3) :: (w16) :: (w11) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part14Program {s with pc := N 6499, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage7Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part14Program, stage7Part14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]

def stage7Part15Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage7Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 1216
  let v3 : W := UInt256.mulMod (v2) (w5) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6518, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage7Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part15Program {s with pc := N 6508, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage7Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part15Program, stage7Part15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]

def stage7Part16Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA12),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14)]
def stage7Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := UInt256.mulMod (v0) (w11) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 6528, memory := s.memory, stack := (w13) :: (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage7Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part16Program {s with pc := N 6518, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage7Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part16Program, stage7Part16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]

def stage7Part17Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0)]
def stage7Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w3) * (w14)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v0)
  {s with pc := N 6565, memory := s.memory, stack := (v1) :: (v1) :: (w0) :: (w1) :: (w2) :: (w1) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part17Program {s with pc := N 6528, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage7Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage7Part17Program, stage7Part17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part18Program : List Instr :=
  [.push 2 1280,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage7Part18Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w0).toNat 32) 1280
  let v1 : W := UInt256.mulMod (w1) (w2) (w3)
  let v2 : W := (v1) + (w4)
  let v3 : W := UInt256.mulMod (N 2048) (v2) (w5)
  {s with pc := N 6575, memory := v0, stack := (v3) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage7Part18_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part18Program {s with pc := N 6565, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage7Part18Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage7Part18Program, stage7Part18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]

def stage7Program : List Instr := (stage7Part0Program ++ (stage7Part1Program ++ (stage7Part2Program ++ (stage7Part3Program ++ (stage7Part4Program ++ (stage7Part5Program ++ (stage7Part6Program ++ (stage7Part7Program ++ (stage7Part8Program ++ (stage7Part9Program ++ (stage7Part10Program ++ (stage7Part11Program ++ (stage7Part12Program ++ (stage7Part13Program ++ (stage7Part14Program ++ (stage7Part15Program ++ (stage7Part16Program ++ (stage7Part17Program ++ (stage7Part18Program)))))))))))))))))))
def stage7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 768
  let v3 : W := (v1) * (v2)
  let v4 : W := MachineState.readWord (s.memory) 128
  let v5 : W := (v4) * (w4)
  let v6 : W := (v5) + (v3)
  let v7 : W := MachineState.readWord (s.memory) 96
  let v8 : W := (w5) * (v7)
  let v9 : W := (v8) + (v6)
  let v10 : W := MachineState.readWord (s.memory) 64
  let v11 : W := MachineState.readWord (s.memory) 32
  let v12 : W := (v11) * (v10)
  let v13 : W := (v12) + (v9)
  let v14 : W := UInt256.mulMod (v1) (v2) (w8)
  let v15 : W := MachineState.readWord (s.memory) 128
  let v16 : W := UInt256.mulMod (w4) (v15) (w8)
  let v17 : W := (v16) + (v14)
  let v18 : W := MachineState.readWord (s.memory) 96
  let v19 : W := UInt256.mulMod (w5) (v18) (w8)
  let v20 : W := (v19) + (v17)
  let v21 : W := MachineState.readWord (s.memory) 64
  let v22 : W := MachineState.readWord (s.memory) 32
  let v23 : W := UInt256.mulMod (v22) (v21) (w8)
  let v24 : W := (v23) + (v20)
  let v25 : W := (w0) + (v24)
  let v26 : W := (w0) + (v13)
  let v27 : W := (v0) * (w9)
  let v28 : W := (v27) + (v26)
  let v29 : W := (w7) * (w2)
  let v30 : W := (v29) + (v28)
  let v31 : W := MachineState.readWord (s.memory) 192
  let v32 : W := (v31) * (w6)
  let v33 : W := (v32) + (v30)
  let v34 : W := MachineState.readWord (s.memory) 0
  let v35 : W := (v34) * (w3)
  let v36 : W := (v35) + (v33)
  let v37 : W := MachineState.readWord (s.memory) 224
  let v38 : W := (v37) * (w13)
  let v39 : W := (v38) + (v36)
  let v40 : W := MachineState.readWord (s.memory) 1216
  let v41 : W := (v40) * (w1)
  let v42 : W := (v41) + (v39)
  let v43 : W := MachineState.readWord (s.memory) 1248
  let v44 : W := (v43) * (w10)
  let v45 : W := (v44) + (v42)
  let v46 : W := UInt256.mulMod (v0) (w9) (w8)
  let v47 : W := (v46) + (v25)
  let v48 : W := UInt256.mulMod (w7) (w2) (w8)
  let v49 : W := (v48) + (v47)
  let v50 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w7).toNat 32) 1088
  let v51 : W := MachineState.readWord (v50) 192
  let v52 : W := UInt256.mulMod (v51) (w6) (w8)
  let v53 : W := (v52) + (v49)
  let v54 : W := MachineState.readWord (v50) 0
  let v55 : W := UInt256.mulMod (v54) (w3) (w8)
  let v56 : W := (v55) + (v53)
  let v57 : W := MachineState.readWord (v50) 224
  let v58 : W := UInt256.mulMod (v57) (w13) (w8)
  let v59 : W := (v58) + (v56)
  let v60 : W := MachineState.readWord (v50) 1216
  let v61 : W := UInt256.mulMod (v60) (w1) (w8)
  let v62 : W := (v61) + (v59)
  let v63 : W := MachineState.readWord (v50) 1248
  let v64 : W := UInt256.mulMod (v63) (w10) (w8)
  let v65 : W := (v64) + (v62)
  let v66 : W := (v45) * (w11)
  let v67 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v66)
  let v68 : ByteArray := MachineState.writeBytes (v50) (Data.Bytes.natToBytesPadded (v67).toNat 32) 1280
  let v69 : W := UInt256.mulMod (v67) (w12) (w8)
  let v70 : W := (v69) + (v65)
  let v71 : W := UInt256.mulMod (N 2048) (v70) (w8)
  {s with pc := N 6575, memory := v68, stack := (v71) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Program {s with pc := N 6370, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 768
  let v3 : W := (v1) * (v2)
  let v4 : W := MachineState.readWord (s.memory) 128
  let v5 : W := (v4) * (w4)
  let v6 : W := (v5) + (v3)
  let v7 : W := MachineState.readWord (s.memory) 96
  let v8 : W := (w5) * (v7)
  let v9 : W := (v8) + (v6)
  let v10 : W := MachineState.readWord (s.memory) 64
  let v11 : W := MachineState.readWord (s.memory) 32
  let v12 : W := (v11) * (v10)
  let v13 : W := (v12) + (v9)
  let v14 : W := UInt256.mulMod (v1) (v2) (w8)
  let v15 : W := MachineState.readWord (s.memory) 128
  let v16 : W := UInt256.mulMod (w4) (v15) (w8)
  let v17 : W := (v16) + (v14)
  let v18 : W := MachineState.readWord (s.memory) 96
  let v19 : W := UInt256.mulMod (w5) (v18) (w8)
  let v20 : W := (v19) + (v17)
  let v21 : W := MachineState.readWord (s.memory) 64
  let v22 : W := MachineState.readWord (s.memory) 32
  let v23 : W := UInt256.mulMod (v22) (v21) (w8)
  let v24 : W := (v23) + (v20)
  let v25 : W := (w0) + (v24)
  let v26 : W := (w0) + (v13)
  let v27 : W := (v0) * (w9)
  let v28 : W := (v27) + (v26)
  let v29 : W := (w7) * (w2)
  let v30 : W := (v29) + (v28)
  let v31 : W := MachineState.readWord (s.memory) 192
  let v32 : W := (v31) * (w6)
  let v33 : W := (v32) + (v30)
  let v34 : W := MachineState.readWord (s.memory) 0
  let v35 : W := (v34) * (w3)
  let v36 : W := (v35) + (v33)
  let v37 : W := MachineState.readWord (s.memory) 224
  let v38 : W := (v37) * (w13)
  let v39 : W := (v38) + (v36)
  let v40 : W := MachineState.readWord (s.memory) 1216
  let v41 : W := (v40) * (w1)
  let v42 : W := (v41) + (v39)
  let v43 : W := MachineState.readWord (s.memory) 1248
  let v44 : W := (v43) * (w10)
  let v45 : W := (v44) + (v42)
  let v46 : W := UInt256.mulMod (v0) (w9) (w8)
  let v47 : W := (v46) + (v25)
  let v48 : W := UInt256.mulMod (w7) (w2) (w8)
  let v49 : W := (v48) + (v47)
  let v50 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w7).toNat 32) 1088
  let v51 : W := MachineState.readWord (v50) 192
  let v52 : W := UInt256.mulMod (v51) (w6) (w8)
  let v53 : W := (v52) + (v49)
  let v54 : W := MachineState.readWord (v50) 0
  let v55 : W := UInt256.mulMod (v54) (w3) (w8)
  let v56 : W := (v55) + (v53)
  let v57 : W := MachineState.readWord (v50) 224
  let v58 : W := UInt256.mulMod (v57) (w13) (w8)
  let v59 : W := (v58) + (v56)
  let v60 : W := MachineState.readWord (v50) 1216
  let v61 : W := UInt256.mulMod (v60) (w1) (w8)
  let v62 : W := (v61) + (v59)
  let v63 : W := MachineState.readWord (v50) 1248
  let v64 : W := UInt256.mulMod (v63) (w10) (w8)
  let v65 : W := (v64) + (v62)
  let v66 : W := (v45) * (w11)
  let v67 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v66)
  let v68 : ByteArray := MachineState.writeBytes (v50) (Data.Bytes.natToBytesPadded (v67).toNat 32) 1280
  let v69 : W := UInt256.mulMod (v67) (w12) (w8)
  let v70 : W := (v69) + (v65)
  let v71 : W := UInt256.mulMod (N 2048) (v70) (w8)
  have h0 : runInstructions stage7Part0Program {s with pc := N 6370, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6383, memory := s.memory, stack := (v2) :: (w8) :: (v1) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part0Model, v0, v1, v2] using stage7Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage7Part1Program {s with pc := N 6383, memory := s.memory, stack := (v2) :: (w8) :: (v1) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6392, memory := s.memory, stack := (v6) :: (v2) :: (w8) :: (v1) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part1Model, v3, v4, v5, v6] using stage7Part1_run ({s with memory := s.memory}) (v2) (w8) (v1) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage7Part2Program {s with pc := N 6392, memory := s.memory, stack := (v6) :: (v2) :: (w8) :: (v1) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6401, memory := s.memory, stack := (v10) :: (v9) :: (v2) :: (w8) :: (v1) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part2Model, v7, v8, v9, v10] using stage7Part2_run ({s with memory := s.memory}) (v6) (v2) (w8) (v1) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage7Part3Program {s with pc := N 6401, memory := s.memory, stack := (v10) :: (v9) :: (v2) :: (w8) :: (v1) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6409, memory := s.memory, stack := (w8) :: (v14) :: (v13) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part3Model, v11, v12, v13, v14] using stage7Part3_run ({s with memory := s.memory}) (v10) (v9) (v2) (w8) (v1) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage7Part4Program {s with pc := N 6409, memory := s.memory, stack := (w8) :: (v14) :: (v13) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6419, memory := s.memory, stack := (v18) :: (w8) :: (v17) :: (v13) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part4Model, v15, v16, v17, v18] using stage7Part4_run ({s with memory := s.memory}) (w8) (v14) (v13) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage7Part5Program {s with pc := N 6419, memory := s.memory, stack := (v18) :: (w8) :: (v17) :: (v13) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6429, memory := s.memory, stack := (v22) :: (v21) :: (w8) :: (v20) :: (v13) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part5Model, v19, v20, v21, v22] using stage7Part5_run ({s with memory := s.memory}) (v18) (w8) (v17) (v13) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage7Part6Program {s with pc := N 6429, memory := s.memory, stack := (v22) :: (v21) :: (w8) :: (v20) :: (v13) :: (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6437, memory := s.memory, stack := (v0) :: (w9) :: (v26) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part6Model, v23, v24, v25, v26] using stage7Part6_run ({s with memory := s.memory}) (v22) (v21) (w8) (v20) (v13) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage7Part7Program {s with pc := N 6437, memory := s.memory, stack := (v0) :: (w9) :: (v26) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6444, memory := s.memory, stack := (w6) :: (v30) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part7Model, v27, v28, v29, v30] using stage7Part7_run ({s with memory := s.memory}) (v0) (w9) (v26) (w7) (v25) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage7Part8Program {s with pc := N 6444, memory := s.memory, stack := (w6) :: (v30) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6453, memory := s.memory, stack := (v35) :: (v33) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part8Model, v31, v32, v33, v34, v35] using stage7Part8_run ({s with memory := s.memory}) (w6) (v30) (w7) (v25) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage7Part9Program {s with pc := N 6453, memory := s.memory, stack := (v35) :: (v33) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6461, memory := s.memory, stack := (w1) :: (v39) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part9Model, v36, v37, v38, v39] using stage7Part9_run ({s with memory := s.memory}) (v35) (v33) (w7) (v25) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage7Part10Program {s with pc := N 6461, memory := s.memory, stack := (w1) :: (v39) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6473, memory := s.memory, stack := (v44) :: (v42) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part10Model, v40, v41, v42, v43, v44] using stage7Part10_run ({s with memory := s.memory}) (w1) (v39) (w7) (v25) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage7Part11Program {s with pc := N 6473, memory := s.memory, stack := (v44) :: (v42) :: (w7) :: (v25) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6481, memory := s.memory, stack := (w8) :: (v47) :: (w7) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part11Model, v45, v46, v47] using stage7Part11_run ({s with memory := s.memory}) (v44) (v42) (w7) (v25) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage7Part12Program {s with pc := N 6481, memory := s.memory, stack := (w8) :: (v47) :: (w7) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6491, memory := v50, stack := (w8) :: (v49) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part12Model, v48, v49, v50] using stage7Part12_run ({s with memory := s.memory}) (w8) (v47) (w7) (v45) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions stage7Part13Program {s with pc := N 6491, memory := v50, stack := (w8) :: (v49) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6499, memory := v50, stack := (w3) :: (w8) :: (v53) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part13Model, v51, v52, v53] using stage7Part13_run ({s with memory := v50}) (w8) (v49) (v45) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h14 : runInstructions stage7Part14Program {s with pc := N 6499, memory := v50, stack := (w3) :: (w8) :: (v53) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6508, memory := v50, stack := (v57) :: (w13) :: (w8) :: (v56) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part14Model, v54, v55, v56, v57] using stage7Part14_run ({s with memory := v50}) (w3) (w8) (v53) (v45) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h15 : runInstructions stage7Part15Program {s with pc := N 6508, memory := v50, stack := (v57) :: (w13) :: (w8) :: (v56) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6518, memory := v50, stack := (v62) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part15Model, v58, v59, v60, v61, v62] using stage7Part15_run ({s with memory := v50}) (v57) (w13) (w8) (v56) (v45) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h16 : runInstructions stage7Part16Program {s with pc := N 6518, memory := v50, stack := (v62) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6528, memory := v50, stack := (w12) :: (w8) :: (v65) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part16Model, v63, v64, v65] using stage7Part16_run ({s with memory := v50}) (v62) (v45) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h17 : runInstructions stage7Part17Program {s with pc := N 6528, memory := v50, stack := (w12) :: (w8) :: (v65) :: (v45) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6565, memory := v50, stack := (v67) :: (v67) :: (w12) :: (w8) :: (v65) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part17Model, v66, v67] using stage7Part17_run ({s with memory := v50}) (w12) (w8) (v65) (v45) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h18 : runInstructions stage7Part18Program {s with pc := N 6565, memory := v50, stack := (v67) :: (v67) :: (w12) :: (w8) :: (v65) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6575, memory := v68, stack := (v71) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v0) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage7Part18Model, v68, v69, v70, v71] using stage7Part18_run ({s with memory := v50}) (v67) (v67) (w12) (w8) (v65) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (v0) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 h18))))))))))))))))))

def stage8Part0Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL,
   .op (.Dup dA8)]
def stage8Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (w14) * (v0)
  {s with pc := N 6585, memory := s.memory, stack := (w4) :: (v1) :: (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage8Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part0Program {s with pc := N 6575, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage8Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part0Program, stage8Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]

def stage8Part1Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MUL]
def stage8Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 128
  let v4 : W := (w10) * (v3)
  {s with pc := N 6595, memory := s.memory, stack := (v4) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage8Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part1Program {s with pc := N 6585, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage8Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part1Program, stage8Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha128, hf128]

def stage8Part2Program : List Instr :=
  [.op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2)]
def stage8Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 32
  let v3 : W := (v2) * (v1)
  let v4 : W := (v3) + (v0)
  {s with pc := N 6605, memory := s.memory, stack := (w4) :: (w2) :: (w3) :: (v4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage8Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part2Program {s with pc := N 6595, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage8Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part2Program, stage8Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha32, hf32]

def stage8Part3Program : List Instr :=
  [.op .MULMOD,
   .op (.Dup dA10),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10)]
def stage8Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := UInt256.mulMod (w8) (v1) (w12)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6614, memory := s.memory, stack := (w12) :: (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage8Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part3Program {s with pc := N 6605, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage8Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part3Program, stage8Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage8Part4Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10),
   .push 1 96,
   .op .MLOAD]
def stage8Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := UInt256.mulMod (w8) (v0) (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 96
  {s with pc := N 6624, memory := s.memory, stack := (v3) :: (w11) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage8Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part4Program {s with pc := N 6614, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage8Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part4Program, stage8Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha96, hf96]

def stage8Part5Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD]
def stage8Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := UInt256.mulMod (v0) (w0) (w1)
  let v2 : W := (v1) + (w2)
  let v3 : W := (w4) + (v2)
  let v4 : W := (w4) + (w3)
  {s with pc := N 6633, memory := s.memory, stack := (v4) :: (v3) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage8Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part5Program {s with pc := N 6624, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage8Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part5Program, stage8Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage8Part6Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup dA0),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap sA10)]
def stage8Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := (v0) * (v0)
  let v2 : W := (v1) + (w0)
  let v3 : W := MachineState.readWord (s.memory) 1600
  {s with pc := N 6644, memory := s.memory, stack := (w10) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v3) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage8Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part6Program {s with pc := N 6633, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage8Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1600 : (1600 : W).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part6Program, stage8Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha1600, hf1600]

def stage8Part7Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Swap sA2),
   .op (.Dup dA11),
   .op (.Dup dA2),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA2)]
def stage8Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w11) (w0) (w10)
  let v1 : W := (v0) + (w2)
  {s with pc := N 6652, memory := s.memory, stack := (w11) :: (w0) :: (w1) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part7Program {s with pc := N 6644, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage8Part7Program, stage8Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage8Part8Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3)]
def stage8Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := MachineState.readWord (s.memory) 1088
  let v3 : W := (w10) * (v2)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6662, memory := s.memory, stack := (w5) :: (v4) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage8Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part8Program {s with pc := N 6652, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage8Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part8Program, stage8Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]

def stage8Part9Program : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA7),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]
def stage8Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 0
  let v4 : W := (v3) * (w8)
  {s with pc := N 6671, memory := s.memory, stack := (v4) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part9Program {s with pc := N 6662, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part9Program, stage8Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192, ha0, hf0]

def stage8Part10Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA4),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14)]
def stage8Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 224
  let v2 : W := (v1) * (w5)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6679, memory := s.memory, stack := (w15) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part10Program {s with pc := N 6671, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part10Program, stage8Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage8Part11Program : List Instr :=
  [.push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL]
def stage8Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 1248
  let v4 : W := (v3) * (w3)
  {s with pc := N 6691, memory := s.memory, stack := (v4) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part11Program {s with pc := N 6679, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part11Program, stage8Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216, ha1248, hf1248]

def stage8Part12Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA11),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9)]
def stage8Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 1280
  let v2 : W := (v1) * (w12)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6701, memory := s.memory, stack := (w10) :: (w2) :: (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part12Program {s with pc := N 6691, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part12Program, stage8Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]

def stage8Part13Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD,
   .push 1 64,
   .op .MSTORE]
def stage8Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := (v0) + (v0)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 64
  {s with pc := N 6711, memory := v2, stack := (v0) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part13Program {s with pc := N 6701, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part13Program, stage8Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]

def stage8Part14Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD]
def stage8Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 1088
  let v3 : W := UInt256.mulMod (w11) (v2) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6721, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage8Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part14Program {s with pc := N 6711, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage8Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part14Program, stage8Part14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]

def stage8Part15Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA4),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA8)]
def stage8Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod (v0) (w3) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 6730, memory := s.memory, stack := (w7) :: (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage8Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part15Program {s with pc := N 6721, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage8Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part15Program, stage8Part15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage8Part16Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5),
   .push 1 224,
   .op .MLOAD]
def stage8Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod (v0) (w0) (w1)
  let v2 : W := (v1) + (w2)
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 6739, memory := s.memory, stack := (v3) :: (w6) :: (w11) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage8Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part16Program {s with pc := N 6730, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage8Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part16Program, stage8Part16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]

def stage8Part17Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage8Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 1216
  let v3 : W := UInt256.mulMod (v2) (w17) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6749, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage8Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part17Program {s with pc := N 6739, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage8Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part17Program, stage8Part17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]

def stage8Part18Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA3),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12)]
def stage8Part18Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := UInt256.mulMod (v0) (w2) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 6759, memory := s.memory, stack := (w11) :: (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage8Part18_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part18Program {s with pc := N 6749, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage8Part18Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part18Program, stage8Part18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]

def stage8Part19Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op (.Dup dA3),
   .op (.Dup dA15)]
def stage8Part19Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1280
  let v1 : W := UInt256.mulMod (v0) (w0) (w1)
  let v2 : W := (v1) + (w2)
  {s with pc := N 6799, memory := s.memory, stack := (w14) :: (w3) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (w11) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage8Part19_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part19Program {s with pc := N 6759, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage8Part19Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage8Part19Program, stage8Part19Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]

def stage8Part20Program : List Instr :=
  [.op .MUL,
   .op (.Dup dA1),
   .op (.Swap sA15),
   .op .POP,
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA15),
   .op .MULMOD]
def stage8Part20Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := UInt256.land (v0) (w2)
  let v2 : W := UInt256.mulMod (w17) (v1) (w3)
  {s with pc := N 6807, memory := s.memory, stack := (v2) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w2) :: (v1) :: (w18) :: (w19) :: rest}
theorem stage8Part20_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part20Program {s with pc := N 6799, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage8Part20Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage8Part20Program, stage8Part20Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage8Part21Program : List Instr :=
  [.op .ADD,
   .push 2 2048,
   .op (.Dup dA10),
   .op (.Swap sA2),
   .op .POP,
   .op .MULMOD]
def stage8Part21Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (N 2048) (v0) (w10)
  {s with pc := N 6815, memory := s.memory, stack := (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part21_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part21Program {s with pc := N 6807, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Part21Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage8Part21Program, stage8Part21Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage8Program : List Instr := (stage8Part0Program ++ (stage8Part1Program ++ (stage8Part2Program ++ (stage8Part3Program ++ (stage8Part4Program ++ (stage8Part5Program ++ (stage8Part6Program ++ (stage8Part7Program ++ (stage8Part8Program ++ (stage8Part9Program ++ (stage8Part10Program ++ (stage8Part11Program ++ (stage8Part12Program ++ (stage8Part13Program ++ (stage8Part14Program ++ (stage8Part15Program ++ (stage8Part16Program ++ (stage8Part17Program ++ (stage8Part18Program ++ (stage8Part19Program ++ (stage8Part20Program ++ (stage8Part21Program))))))))))))))))))))))
def stage8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (w14) * (v0)
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := (v2) * (w4)
  let v4 : W := (v3) + (v1)
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := (w5) * (v5)
  let v7 : W := (v6) + (v4)
  let v8 : W := MachineState.readWord (s.memory) 96
  let v9 : W := MachineState.readWord (s.memory) 32
  let v10 : W := (v9) * (v8)
  let v11 : W := (v10) + (v7)
  let v12 : W := UInt256.mulMod (w14) (v0) (w8)
  let v13 : W := MachineState.readWord (s.memory) 160
  let v14 : W := UInt256.mulMod (w4) (v13) (w8)
  let v15 : W := (v14) + (v12)
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := UInt256.mulMod (w5) (v16) (w8)
  let v18 : W := (v17) + (v15)
  let v19 : W := MachineState.readWord (s.memory) 96
  let v20 : W := MachineState.readWord (s.memory) 32
  let v21 : W := UInt256.mulMod (v20) (v19) (w8)
  let v22 : W := (v21) + (v18)
  let v23 : W := (w0) + (v22)
  let v24 : W := (w0) + (v11)
  let v25 : W := MachineState.readWord (s.memory) 64
  let v26 : W := (v25) * (v25)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 1600
  let v29 : W := UInt256.mulMod (v28) (w9) (w8)
  let v30 : W := (v29) + (v23)
  let v31 : W := (v28) * (w9)
  let v32 : W := (v31) + (v27)
  let v33 : W := MachineState.readWord (s.memory) 1088
  let v34 : W := (w7) * (v33)
  let v35 : W := (v34) + (v32)
  let v36 : W := MachineState.readWord (s.memory) 192
  let v37 : W := (v36) * (w2)
  let v38 : W := (v37) + (v35)
  let v39 : W := MachineState.readWord (s.memory) 0
  let v40 : W := (v39) * (w6)
  let v41 : W := (v40) + (v38)
  let v42 : W := MachineState.readWord (s.memory) 224
  let v43 : W := (v42) * (w3)
  let v44 : W := (v43) + (v41)
  let v45 : W := MachineState.readWord (s.memory) 1216
  let v46 : W := (v45) * (w13)
  let v47 : W := (v46) + (v44)
  let v48 : W := MachineState.readWord (s.memory) 1248
  let v49 : W := (v48) * (w1)
  let v50 : W := (v49) + (v47)
  let v51 : W := MachineState.readWord (s.memory) 1280
  let v52 : W := (v51) * (w10)
  let v53 : W := (v52) + (v50)
  let v54 : W := MachineState.readWord (s.memory) 64
  let v55 : W := (v54) + (v54)
  let v56 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v55).toNat 32) 64
  let v57 : W := UInt256.mulMod (v54) (v54) (w8)
  let v58 : W := (v57) + (v30)
  let v59 : W := MachineState.readWord (v56) 1088
  let v60 : W := UInt256.mulMod (w7) (v59) (w8)
  let v61 : W := (v60) + (v58)
  let v62 : W := MachineState.readWord (v56) 192
  let v63 : W := UInt256.mulMod (v62) (w2) (w8)
  let v64 : W := (v63) + (v61)
  let v65 : W := MachineState.readWord (v56) 0
  let v66 : W := UInt256.mulMod (v65) (w6) (w8)
  let v67 : W := (v66) + (v64)
  let v68 : W := MachineState.readWord (v56) 224
  let v69 : W := UInt256.mulMod (v68) (w3) (w8)
  let v70 : W := (v69) + (v67)
  let v71 : W := MachineState.readWord (v56) 1216
  let v72 : W := UInt256.mulMod (v71) (w13) (w8)
  let v73 : W := (v72) + (v70)
  let v74 : W := MachineState.readWord (v56) 1248
  let v75 : W := UInt256.mulMod (v74) (w1) (w8)
  let v76 : W := (v75) + (v73)
  let v77 : W := MachineState.readWord (v56) 1280
  let v78 : W := UInt256.mulMod (v77) (w10) (w8)
  let v79 : W := (v78) + (v76)
  let v80 : W := (w11) * (v53)
  let v81 : W := UInt256.land (v80) (N 1766847064778384329583297500742918515827483896875618958121606201292619775)
  let v82 : W := UInt256.mulMod (w12) (v81) (w8)
  let v83 : W := (v82) + (v79)
  let v84 : W := UInt256.mulMod (N 2048) (v83) (w8)
  {s with pc := N 6815, memory := v56, stack := (v84) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (v81) :: (w13) :: (w14) :: rest}
theorem stage8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Program {s with pc := N 6575, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := (w14) * (v0)
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := (v2) * (w4)
  let v4 : W := (v3) + (v1)
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := (w5) * (v5)
  let v7 : W := (v6) + (v4)
  let v8 : W := MachineState.readWord (s.memory) 96
  let v9 : W := MachineState.readWord (s.memory) 32
  let v10 : W := (v9) * (v8)
  let v11 : W := (v10) + (v7)
  let v12 : W := UInt256.mulMod (w14) (v0) (w8)
  let v13 : W := MachineState.readWord (s.memory) 160
  let v14 : W := UInt256.mulMod (w4) (v13) (w8)
  let v15 : W := (v14) + (v12)
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := UInt256.mulMod (w5) (v16) (w8)
  let v18 : W := (v17) + (v15)
  let v19 : W := MachineState.readWord (s.memory) 96
  let v20 : W := MachineState.readWord (s.memory) 32
  let v21 : W := UInt256.mulMod (v20) (v19) (w8)
  let v22 : W := (v21) + (v18)
  let v23 : W := (w0) + (v22)
  let v24 : W := (w0) + (v11)
  let v25 : W := MachineState.readWord (s.memory) 64
  let v26 : W := (v25) * (v25)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 1600
  let v29 : W := UInt256.mulMod (v28) (w9) (w8)
  let v30 : W := (v29) + (v23)
  let v31 : W := (v28) * (w9)
  let v32 : W := (v31) + (v27)
  let v33 : W := MachineState.readWord (s.memory) 1088
  let v34 : W := (w7) * (v33)
  let v35 : W := (v34) + (v32)
  let v36 : W := MachineState.readWord (s.memory) 192
  let v37 : W := (v36) * (w2)
  let v38 : W := (v37) + (v35)
  let v39 : W := MachineState.readWord (s.memory) 0
  let v40 : W := (v39) * (w6)
  let v41 : W := (v40) + (v38)
  let v42 : W := MachineState.readWord (s.memory) 224
  let v43 : W := (v42) * (w3)
  let v44 : W := (v43) + (v41)
  let v45 : W := MachineState.readWord (s.memory) 1216
  let v46 : W := (v45) * (w13)
  let v47 : W := (v46) + (v44)
  let v48 : W := MachineState.readWord (s.memory) 1248
  let v49 : W := (v48) * (w1)
  let v50 : W := (v49) + (v47)
  let v51 : W := MachineState.readWord (s.memory) 1280
  let v52 : W := (v51) * (w10)
  let v53 : W := (v52) + (v50)
  let v54 : W := MachineState.readWord (s.memory) 64
  let v55 : W := (v54) + (v54)
  let v56 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v55).toNat 32) 64
  let v57 : W := UInt256.mulMod (v54) (v54) (w8)
  let v58 : W := (v57) + (v30)
  let v59 : W := MachineState.readWord (v56) 1088
  let v60 : W := UInt256.mulMod (w7) (v59) (w8)
  let v61 : W := (v60) + (v58)
  let v62 : W := MachineState.readWord (v56) 192
  let v63 : W := UInt256.mulMod (v62) (w2) (w8)
  let v64 : W := (v63) + (v61)
  let v65 : W := MachineState.readWord (v56) 0
  let v66 : W := UInt256.mulMod (v65) (w6) (w8)
  let v67 : W := (v66) + (v64)
  let v68 : W := MachineState.readWord (v56) 224
  let v69 : W := UInt256.mulMod (v68) (w3) (w8)
  let v70 : W := (v69) + (v67)
  let v71 : W := MachineState.readWord (v56) 1216
  let v72 : W := UInt256.mulMod (v71) (w13) (w8)
  let v73 : W := (v72) + (v70)
  let v74 : W := MachineState.readWord (v56) 1248
  let v75 : W := UInt256.mulMod (v74) (w1) (w8)
  let v76 : W := (v75) + (v73)
  let v77 : W := MachineState.readWord (v56) 1280
  let v78 : W := UInt256.mulMod (v77) (w10) (w8)
  let v79 : W := (v78) + (v76)
  let v80 : W := (w11) * (v53)
  let v81 : W := UInt256.land (v80) (N 1766847064778384329583297500742918515827483896875618958121606201292619775)
  let v82 : W := UInt256.mulMod (w12) (v81) (w8)
  let v83 : W := (v82) + (v79)
  let v84 : W := UInt256.mulMod (N 2048) (v83) (w8)
  have h0 : runInstructions stage8Part0Program {s with pc := N 6575, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6585, memory := s.memory, stack := (w4) :: (v1) :: (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part0Model, v0, v1] using stage8Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage8Part1Program {s with pc := N 6585, memory := s.memory, stack := (w4) :: (v1) :: (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6595, memory := s.memory, stack := (v6) :: (v4) :: (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part1Model, v2, v3, v4, v5, v6] using stage8Part1_run ({s with memory := s.memory}) (w4) (v1) (v0) (w8) (w14) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage8Part2Program {s with pc := N 6595, memory := s.memory, stack := (v6) :: (v4) :: (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6605, memory := s.memory, stack := (w14) :: (v0) :: (w8) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part2Model, v7, v8, v9, v10, v11] using stage8Part2_run ({s with memory := s.memory}) (v6) (v4) (v0) (w8) (w14) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage8Part3Program {s with pc := N 6605, memory := s.memory, stack := (w14) :: (v0) :: (w8) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6614, memory := s.memory, stack := (w8) :: (v15) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part3Model, v12, v13, v14, v15] using stage8Part3_run ({s with memory := s.memory}) (w14) (v0) (w8) (v11) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage8Part4Program {s with pc := N 6614, memory := s.memory, stack := (w8) :: (v15) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6624, memory := s.memory, stack := (v19) :: (w8) :: (v18) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part4Model, v16, v17, v18, v19] using stage8Part4_run ({s with memory := s.memory}) (w8) (v15) (v11) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage8Part5Program {s with pc := N 6624, memory := s.memory, stack := (v19) :: (w8) :: (v18) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6633, memory := s.memory, stack := (v24) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part5Model, v20, v21, v22, v23, v24] using stage8Part5_run ({s with memory := s.memory}) (v19) (w8) (v18) (v11) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage8Part6Program {s with pc := N 6633, memory := s.memory, stack := (v24) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6644, memory := s.memory, stack := (w9) :: (v27) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part6Model, v25, v26, v27, v28] using stage8Part6_run ({s with memory := s.memory}) (v24) (v23) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage8Part7Program {s with pc := N 6644, memory := s.memory, stack := (w9) :: (v27) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6652, memory := s.memory, stack := (v28) :: (w9) :: (v27) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part7Model, v29, v30] using stage8Part7_run ({s with memory := s.memory}) (w9) (v27) (v23) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage8Part8Program {s with pc := N 6652, memory := s.memory, stack := (v28) :: (w9) :: (v27) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6662, memory := s.memory, stack := (w2) :: (v35) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part8Model, v31, v32, v33, v34, v35] using stage8Part8_run ({s with memory := s.memory}) (v28) (w9) (v27) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage8Part9Program {s with pc := N 6662, memory := s.memory, stack := (w2) :: (v35) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6671, memory := s.memory, stack := (v40) :: (v38) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part9Model, v36, v37, v38, v39, v40] using stage8Part9_run ({s with memory := s.memory}) (w2) (v35) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage8Part10Program {s with pc := N 6671, memory := s.memory, stack := (v40) :: (v38) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6679, memory := s.memory, stack := (w13) :: (v44) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part10Model, v41, v42, v43, v44] using stage8Part10_run ({s with memory := s.memory}) (v40) (v38) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage8Part11Program {s with pc := N 6679, memory := s.memory, stack := (w13) :: (v44) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6691, memory := s.memory, stack := (v49) :: (v47) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part11Model, v45, v46, v47, v48, v49] using stage8Part11_run ({s with memory := s.memory}) (w13) (v44) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage8Part12Program {s with pc := N 6691, memory := s.memory, stack := (v49) :: (v47) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6701, memory := s.memory, stack := (w8) :: (v30) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part12Model, v50, v51, v52, v53] using stage8Part12_run ({s with memory := s.memory}) (v49) (v47) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions stage8Part13Program {s with pc := N 6701, memory := s.memory, stack := (w8) :: (v30) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6711, memory := v56, stack := (v54) :: (v54) :: (w8) :: (v30) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part13Model, v54, v55, v56] using stage8Part13_run ({s with memory := s.memory}) (w8) (v30) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h14 : runInstructions stage8Part14Program {s with pc := N 6711, memory := v56, stack := (v54) :: (v54) :: (w8) :: (v30) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6721, memory := v56, stack := (v61) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part14Model, v57, v58, v59, v60, v61] using stage8Part14_run ({s with memory := v56}) (v54) (v54) (w8) (v30) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h15 : runInstructions stage8Part15Program {s with pc := N 6721, memory := v56, stack := (v61) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6730, memory := v56, stack := (w6) :: (w8) :: (v64) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part15Model, v62, v63, v64] using stage8Part15_run ({s with memory := v56}) (v61) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h16 : runInstructions stage8Part16Program {s with pc := N 6730, memory := v56, stack := (w6) :: (w8) :: (v64) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6739, memory := v56, stack := (v68) :: (w3) :: (w8) :: (v67) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part16Model, v65, v66, v67, v68] using stage8Part16_run ({s with memory := v56}) (w6) (w8) (v64) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h17 : runInstructions stage8Part17Program {s with pc := N 6739, memory := v56, stack := (v68) :: (w3) :: (w8) :: (v67) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6749, memory := v56, stack := (v73) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part17Model, v69, v70, v71, v72, v73] using stage8Part17_run ({s with memory := v56}) (v68) (w3) (w8) (v67) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h18 : runInstructions stage8Part18Program {s with pc := N 6749, memory := v56, stack := (v73) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6759, memory := v56, stack := (w10) :: (w8) :: (v76) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part18Model, v74, v75, v76] using stage8Part18_run ({s with memory := v56}) (v73) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h19 : runInstructions stage8Part19Program {s with pc := N 6759, memory := v56, stack := (w10) :: (w8) :: (v76) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6799, memory := v56, stack := (w11) :: (v53) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (w8) :: (v79) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part19Model, v77, v78, v79] using stage8Part19_run ({s with memory := v56}) (w10) (w8) (v76) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h20 : runInstructions stage8Part20Program {s with pc := N 6799, memory := v56, stack := (w11) :: (v53) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (w8) :: (v79) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6807, memory := v56, stack := (v82) :: (v79) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (v81) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part20Model, v80, v81, v82] using stage8Part20_run ({s with memory := v56}) (w11) (v53) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (w8) (v79) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h21 : runInstructions stage8Part21Program {s with pc := N 6807, memory := v56, stack := (v82) :: (v79) :: (v53) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (v81) :: (w13) :: (w14) :: rest} = some {s with pc := N 6815, memory := v56, stack := (v84) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v28) :: (w10) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (v81) :: (w13) :: (w14) :: rest} := by
    simpa only [stage8Part21Model, v83, v84] using stage8Part21_run ({s with memory := v56}) (v82) (v79) (v53) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (v28) (w10) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v81) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 (runInstructions_append_some _ _ _ _ _ h19 (runInstructions_append_some _ _ _ _ _ h20 h21)))))))))))))))))))))

def stage9Part0Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA9),
   .push 2 1248,
   .op .MLOAD,
   .op (.Swap sA6),
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage9Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := (w14) * (w4)
  {s with pc := N 6825, memory := s.memory, stack := (v1) :: (w4) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage9Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part0Program {s with pc := N 6815, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage9Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part0Program, stage9Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]

def stage9Part1Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD]
def stage9Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := (w9) * (v0)
  let v2 : W := (v1) + (w0)
  let v3 : W := MachineState.readWord (s.memory) 128
  {s with pc := N 6834, memory := s.memory, stack := (v3) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage9Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part1Program {s with pc := N 6825, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage9Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part1Program, stage9Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha128, hf128]

def stage9Part2Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD]
def stage9Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 96
  let v4 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 6845, memory := s.memory, stack := (v4) :: (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage9Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part2Program {s with pc := N 6834, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage9Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part2Program, stage9Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha64, hf64, ha96, hf96]

def stage9Part3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA9)]
def stage9Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w5) (w3) (w4)
  let v3 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 6854, memory := s.memory, stack := (w11) :: (v3) :: (w14) :: (v2) :: (v1) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage9Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part3Program {s with pc := N 6845, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} = some (stage9Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part3Program, stage9Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage9Part4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA10),
   .push 1 128,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD]
def stage9Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 128
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := UInt256.mulMod (v3) (v2) (w13)
  {s with pc := N 6864, memory := s.memory, stack := (v4) :: (v1) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage9Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part4Program {s with pc := N 6854, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage9Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part4Program, stage9Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha32, hf32]

def stage9Part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA10),
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage9Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := UInt256.mulMod (v2) (v1) (w11)
  let v4 : W := (v3) + (v0)
  {s with pc := N 6874, memory := s.memory, stack := (v4) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage9Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part5Program {s with pc := N 6864, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage9Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part5Program, stage9Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha64, hf64]

def stage9Part6Program : List Instr :=
  [.op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL]
def stage9Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w2) + (w0)
  let v1 : W := (w2) + (w1)
  let v2 : W := MachineState.readWord (s.memory) 1088
  let v3 : W := (w11) * (v2)
  {s with pc := N 6884, memory := s.memory, stack := (v3) :: (v1) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage9Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part6Program {s with pc := N 6874, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage9Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part6Program, stage9Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]

def stage9Part7Program : List Instr :=
  [.op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3)]
def stage9Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 192
  let v2 : W := (w9) * (v1)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6892, memory := s.memory, stack := (w4) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage9Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part7Program {s with pc := N 6884, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage9Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part7Program, stage9Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage9Part8Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA7),
   .push 1 224,
   .op .MLOAD,
   .op .MUL]
def stage9Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := (v0) * (w0)
  let v2 : W := (v1) + (w1)
  let v3 : W := MachineState.readWord (s.memory) 224
  let v4 : W := (v3) * (w8)
  {s with pc := N 6901, memory := s.memory, stack := (v4) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage9Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part8Program {s with pc := N 6892, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage9Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part8Program, stage9Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]

def stage9Part9Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA4),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA6)]
def stage9Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 1216
  let v2 : W := (v1) * (w5)
  let v3 : W := (v2) + (v0)
  {s with pc := N 6911, memory := s.memory, stack := (w6) :: (w15) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage9Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part9Program {s with pc := N 6901, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage9Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part9Program, stage9Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]

def stage9Part10Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def stage9Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := MachineState.readWord (s.memory) 1280
  let v3 : W := (v2) * (w4)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6921, memory := s.memory, stack := (w13) :: (v4) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage9Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part10Program {s with pc := N 6911, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage9Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part10Program, stage9Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]

def stage9Part11Program : List Instr :=
  [.op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA12)]
def stage9Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w14) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := MachineState.readWord (s.memory) 1088
  {s with pc := N 6931, memory := s.memory, stack := (w11) :: (v2) :: (w10) :: (w2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage9Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part11Program {s with pc := N 6921, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage9Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part11Program, stage9Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]

def stage9Part12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD]
def stage9Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := UInt256.mulMod (w11) (v2) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 6940, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage9Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part12Program {s with pc := N 6931, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage9Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part12Program, stage9Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage9Part13Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA4),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA8)]
def stage9Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod (v0) (w3) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 6948, memory := s.memory, stack := (w7) :: (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage9Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part13Program {s with pc := N 6940, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage9Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part13Program, stage9Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage9Part14Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5),
   .push 2 1216,
   .op .MLOAD]
def stage9Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod (v0) (w0) (w1)
  let v2 : W := (v1) + (w2)
  let v3 : W := MachineState.readWord (s.memory) 1216
  {s with pc := N 6959, memory := s.memory, stack := (v3) :: (w6) :: (w11) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage9Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part14Program {s with pc := N 6948, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage9Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part14Program, stage9Part14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224, ha1216, hf1216]

def stage9Part15Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage9Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w8) (w17) (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 6967, memory := s.memory, stack := (w12) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage9Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part15Program {s with pc := N 6959, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage9Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage9Part15Program, stage9Part15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage9Part16Program : List Instr :=
  [.op (.Dup dA3),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA15)]
def stage9Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1280
  let v1 : W := UInt256.mulMod (v0) (w3) (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 6977, memory := s.memory, stack := (w14) :: (w12) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage9Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part16Program {s with pc := N 6967, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage9Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part16Program, stage9Part16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]

def stage9Part17Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 2 768,
   .op .MSTORE]
def stage9Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.land (w15) (w4)
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v2).toNat 32) 768
  {s with pc := N 6987, memory := v3, stack := (v2) :: (v1) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage9Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part17Program {s with pc := N 6977, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage9Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part17Program, stage9Part17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]

def stage9Part18Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage9Part18Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w1) - (w0)
  let v1 : W := (w9) + (v0)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w9)
  {s with pc := N 6996, memory := s.memory, stack := (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage9Part18_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part18Program {s with pc := N 6987, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage9Part18Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage9Part18Program, stage9Part18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage9Program : List Instr := (stage9Part0Program ++ (stage9Part1Program ++ (stage9Part2Program ++ (stage9Part3Program ++ (stage9Part4Program ++ (stage9Part5Program ++ (stage9Part6Program ++ (stage9Part7Program ++ (stage9Part8Program ++ (stage9Part9Program ++ (stage9Part10Program ++ (stage9Part11Program ++ (stage9Part12Program ++ (stage9Part13Program ++ (stage9Part14Program ++ (stage9Part15Program ++ (stage9Part16Program ++ (stage9Part17Program ++ (stage9Part18Program)))))))))))))))))))
def stage9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := (w14) * (w4)
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := (w5) * (v2)
  let v4 : W := (v3) + (v1)
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := MachineState.readWord (s.memory) 32
  let v7 : W := (v6) * (v5)
  let v8 : W := (v7) + (v4)
  let v9 : W := MachineState.readWord (s.memory) 96
  let v10 : W := MachineState.readWord (s.memory) 64
  let v11 : W := (v10) * (v9)
  let v12 : W := (v11) + (v8)
  let v13 : W := UInt256.mulMod (w14) (w4) (w8)
  let v14 : W := MachineState.readWord (s.memory) 160
  let v15 : W := UInt256.mulMod (w5) (v14) (w8)
  let v16 : W := (v15) + (v13)
  let v17 : W := MachineState.readWord (s.memory) 128
  let v18 : W := MachineState.readWord (s.memory) 32
  let v19 : W := UInt256.mulMod (v18) (v17) (w8)
  let v20 : W := (v19) + (v16)
  let v21 : W := MachineState.readWord (s.memory) 96
  let v22 : W := MachineState.readWord (s.memory) 64
  let v23 : W := UInt256.mulMod (v22) (v21) (w8)
  let v24 : W := (v23) + (v20)
  let v25 : W := (w0) + (v24)
  let v26 : W := (w0) + (v12)
  let v27 : W := MachineState.readWord (s.memory) 1088
  let v28 : W := (w9) * (v27)
  let v29 : W := (v28) + (v26)
  let v30 : W := MachineState.readWord (s.memory) 192
  let v31 : W := (w7) * (v30)
  let v32 : W := (v31) + (v29)
  let v33 : W := MachineState.readWord (s.memory) 0
  let v34 : W := (v33) * (w2)
  let v35 : W := (v34) + (v32)
  let v36 : W := MachineState.readWord (s.memory) 224
  let v37 : W := (v36) * (w6)
  let v38 : W := (v37) + (v35)
  let v39 : W := MachineState.readWord (s.memory) 1216
  let v40 : W := (v39) * (w3)
  let v41 : W := (v40) + (v38)
  let v42 : W := (v0) * (w13)
  let v43 : W := (v42) + (v41)
  let v44 : W := MachineState.readWord (s.memory) 1280
  let v45 : W := (v44) * (w1)
  let v46 : W := (v45) + (v43)
  let v47 : W := (w12) * (w10)
  let v48 : W := (v47) + (v46)
  let v49 : W := MachineState.readWord (s.memory) 1088
  let v50 : W := UInt256.mulMod (w9) (v49) (w8)
  let v51 : W := (v50) + (v25)
  let v52 : W := MachineState.readWord (s.memory) 192
  let v53 : W := UInt256.mulMod (w7) (v52) (w8)
  let v54 : W := (v53) + (v51)
  let v55 : W := MachineState.readWord (s.memory) 0
  let v56 : W := UInt256.mulMod (v55) (w2) (w8)
  let v57 : W := (v56) + (v54)
  let v58 : W := MachineState.readWord (s.memory) 224
  let v59 : W := UInt256.mulMod (v58) (w6) (w8)
  let v60 : W := (v59) + (v57)
  let v61 : W := MachineState.readWord (s.memory) 1216
  let v62 : W := UInt256.mulMod (v61) (w3) (w8)
  let v63 : W := (v62) + (v60)
  let v64 : W := UInt256.mulMod (v0) (w13) (w8)
  let v65 : W := (v64) + (v63)
  let v66 : W := MachineState.readWord (s.memory) 1280
  let v67 : W := UInt256.mulMod (v66) (w1) (w8)
  let v68 : W := (v67) + (v65)
  let v69 : W := UInt256.mulMod (w12) (w10) (w8)
  let v70 : W := (v69) + (v68)
  let v71 : W := UInt256.land (w11) (v48)
  let v72 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v71).toNat 32) 768
  let v73 : W := (v70) - (v71)
  let v74 : W := (w8) + (v73)
  let v75 : W := UInt256.mulMod (N 2048) (v74) (w8)
  {s with pc := N 6996, memory := v72, stack := (v75) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Program {s with pc := N 6815, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := (w14) * (w4)
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := (w5) * (v2)
  let v4 : W := (v3) + (v1)
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := MachineState.readWord (s.memory) 32
  let v7 : W := (v6) * (v5)
  let v8 : W := (v7) + (v4)
  let v9 : W := MachineState.readWord (s.memory) 96
  let v10 : W := MachineState.readWord (s.memory) 64
  let v11 : W := (v10) * (v9)
  let v12 : W := (v11) + (v8)
  let v13 : W := UInt256.mulMod (w14) (w4) (w8)
  let v14 : W := MachineState.readWord (s.memory) 160
  let v15 : W := UInt256.mulMod (w5) (v14) (w8)
  let v16 : W := (v15) + (v13)
  let v17 : W := MachineState.readWord (s.memory) 128
  let v18 : W := MachineState.readWord (s.memory) 32
  let v19 : W := UInt256.mulMod (v18) (v17) (w8)
  let v20 : W := (v19) + (v16)
  let v21 : W := MachineState.readWord (s.memory) 96
  let v22 : W := MachineState.readWord (s.memory) 64
  let v23 : W := UInt256.mulMod (v22) (v21) (w8)
  let v24 : W := (v23) + (v20)
  let v25 : W := (w0) + (v24)
  let v26 : W := (w0) + (v12)
  let v27 : W := MachineState.readWord (s.memory) 1088
  let v28 : W := (w9) * (v27)
  let v29 : W := (v28) + (v26)
  let v30 : W := MachineState.readWord (s.memory) 192
  let v31 : W := (w7) * (v30)
  let v32 : W := (v31) + (v29)
  let v33 : W := MachineState.readWord (s.memory) 0
  let v34 : W := (v33) * (w2)
  let v35 : W := (v34) + (v32)
  let v36 : W := MachineState.readWord (s.memory) 224
  let v37 : W := (v36) * (w6)
  let v38 : W := (v37) + (v35)
  let v39 : W := MachineState.readWord (s.memory) 1216
  let v40 : W := (v39) * (w3)
  let v41 : W := (v40) + (v38)
  let v42 : W := (v0) * (w13)
  let v43 : W := (v42) + (v41)
  let v44 : W := MachineState.readWord (s.memory) 1280
  let v45 : W := (v44) * (w1)
  let v46 : W := (v45) + (v43)
  let v47 : W := (w12) * (w10)
  let v48 : W := (v47) + (v46)
  let v49 : W := MachineState.readWord (s.memory) 1088
  let v50 : W := UInt256.mulMod (w9) (v49) (w8)
  let v51 : W := (v50) + (v25)
  let v52 : W := MachineState.readWord (s.memory) 192
  let v53 : W := UInt256.mulMod (w7) (v52) (w8)
  let v54 : W := (v53) + (v51)
  let v55 : W := MachineState.readWord (s.memory) 0
  let v56 : W := UInt256.mulMod (v55) (w2) (w8)
  let v57 : W := (v56) + (v54)
  let v58 : W := MachineState.readWord (s.memory) 224
  let v59 : W := UInt256.mulMod (v58) (w6) (w8)
  let v60 : W := (v59) + (v57)
  let v61 : W := MachineState.readWord (s.memory) 1216
  let v62 : W := UInt256.mulMod (v61) (w3) (w8)
  let v63 : W := (v62) + (v60)
  let v64 : W := UInt256.mulMod (v0) (w13) (w8)
  let v65 : W := (v64) + (v63)
  let v66 : W := MachineState.readWord (s.memory) 1280
  let v67 : W := UInt256.mulMod (v66) (w1) (w8)
  let v68 : W := (v67) + (v65)
  let v69 : W := UInt256.mulMod (w12) (w10) (w8)
  let v70 : W := (v69) + (v68)
  let v71 : W := UInt256.land (w11) (v48)
  let v72 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v71).toNat 32) 768
  let v73 : W := (v70) - (v71)
  let v74 : W := (w8) + (v73)
  let v75 : W := UInt256.mulMod (N 2048) (v74) (w8)
  have h0 : runInstructions stage9Part0Program {s with pc := N 6815, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6825, memory := s.memory, stack := (v1) :: (w4) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part0Model, v0, v1] using stage9Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage9Part1Program {s with pc := N 6825, memory := s.memory, stack := (v1) :: (w4) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6834, memory := s.memory, stack := (v5) :: (v4) :: (w4) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part1Model, v2, v3, v4, v5] using stage9Part1_run ({s with memory := s.memory}) (v1) (w4) (w8) (w14) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage9Part2Program {s with pc := N 6834, memory := s.memory, stack := (v5) :: (v4) :: (w4) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6845, memory := s.memory, stack := (v10) :: (v9) :: (v8) :: (w4) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part2Model, v6, v7, v8, v9, v10] using stage9Part2_run ({s with memory := s.memory}) (v5) (v4) (w4) (w8) (w14) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage9Part3Program {s with pc := N 6845, memory := s.memory, stack := (v10) :: (v9) :: (v8) :: (w4) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6854, memory := s.memory, stack := (w5) :: (v14) :: (w8) :: (v13) :: (v12) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part3Model, v11, v12, v13, v14] using stage9Part3_run ({s with memory := s.memory}) (v10) (v9) (v8) (w4) (w8) (w14) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage9Part4Program {s with pc := N 6854, memory := s.memory, stack := (w5) :: (v14) :: (w8) :: (v13) :: (v12) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6864, memory := s.memory, stack := (v19) :: (v16) :: (v12) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part4Model, v15, v16, v17, v18, v19] using stage9Part4_run ({s with memory := s.memory}) (w5) (v14) (w8) (v13) (v12) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage9Part5Program {s with pc := N 6864, memory := s.memory, stack := (v19) :: (v16) :: (v12) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6874, memory := s.memory, stack := (v24) :: (v12) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part5Model, v20, v21, v22, v23, v24] using stage9Part5_run ({s with memory := s.memory}) (v19) (v16) (v12) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage9Part6Program {s with pc := N 6874, memory := s.memory, stack := (v24) :: (v12) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6884, memory := s.memory, stack := (v28) :: (v26) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part6Model, v25, v26, v27, v28] using stage9Part6_run ({s with memory := s.memory}) (v24) (v12) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage9Part7Program {s with pc := N 6884, memory := s.memory, stack := (v28) :: (v26) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6892, memory := s.memory, stack := (w2) :: (v32) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part7Model, v29, v30, v31, v32] using stage9Part7_run ({s with memory := s.memory}) (v28) (v26) (v25) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage9Part8Program {s with pc := N 6892, memory := s.memory, stack := (w2) :: (v32) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6901, memory := s.memory, stack := (v37) :: (v35) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part8Model, v33, v34, v35, v36, v37] using stage9Part8_run ({s with memory := s.memory}) (w2) (v32) (v25) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage9Part9Program {s with pc := N 6901, memory := s.memory, stack := (v37) :: (v35) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6911, memory := s.memory, stack := (v0) :: (w13) :: (v41) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part9Model, v38, v39, v40, v41] using stage9Part9_run ({s with memory := s.memory}) (v37) (v35) (v25) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage9Part10Program {s with pc := N 6911, memory := s.memory, stack := (v0) :: (w13) :: (v41) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6921, memory := s.memory, stack := (w10) :: (v46) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part10Model, v42, v43, v44, v45, v46] using stage9Part10_run ({s with memory := s.memory}) (v0) (w13) (v41) (v25) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage9Part11Program {s with pc := N 6921, memory := s.memory, stack := (w10) :: (v46) :: (v25) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6931, memory := s.memory, stack := (w9) :: (v49) :: (w8) :: (v25) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part11Model, v47, v48, v49] using stage9Part11_run ({s with memory := s.memory}) (w10) (v46) (v25) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage9Part12Program {s with pc := N 6931, memory := s.memory, stack := (w9) :: (v49) :: (w8) :: (v25) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6940, memory := s.memory, stack := (v54) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part12Model, v50, v51, v52, v53, v54] using stage9Part12_run ({s with memory := s.memory}) (w9) (v49) (w8) (v25) (v48) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions stage9Part13Program {s with pc := N 6940, memory := s.memory, stack := (v54) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6948, memory := s.memory, stack := (w6) :: (w8) :: (v57) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part13Model, v55, v56, v57] using stage9Part13_run ({s with memory := s.memory}) (v54) (v48) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h14 : runInstructions stage9Part14Program {s with pc := N 6948, memory := s.memory, stack := (w6) :: (w8) :: (v57) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6959, memory := s.memory, stack := (v61) :: (w3) :: (w8) :: (v60) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part14Model, v58, v59, v60, v61] using stage9Part14_run ({s with memory := s.memory}) (w6) (w8) (v57) (v48) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h15 : runInstructions stage9Part15Program {s with pc := N 6959, memory := s.memory, stack := (v61) :: (w3) :: (w8) :: (v60) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6967, memory := s.memory, stack := (w8) :: (v65) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part15Model, v62, v63, v64, v65] using stage9Part15_run ({s with memory := s.memory}) (v61) (w3) (w8) (v60) (v48) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h16 : runInstructions stage9Part16Program {s with pc := N 6967, memory := s.memory, stack := (w8) :: (v65) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6977, memory := s.memory, stack := (w12) :: (w10) :: (w8) :: (v68) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part16Model, v66, v67, v68] using stage9Part16_run ({s with memory := s.memory}) (w8) (v65) (v48) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h17 : runInstructions stage9Part17Program {s with pc := N 6977, memory := s.memory, stack := (w12) :: (w10) :: (w8) :: (v68) :: (v48) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6987, memory := v72, stack := (v71) :: (v70) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part17Model, v69, v70, v71, v72] using stage9Part17_run ({s with memory := s.memory}) (w12) (w10) (w8) (v68) (v48) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h18 : runInstructions stage9Part18Program {s with pc := N 6987, memory := v72, stack := (v71) :: (v70) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 6996, memory := v72, stack := (v75) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage9Part18Model, v73, v74, v75] using stage9Part18_run ({s with memory := v72}) (v71) (v70) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 h18))))))))))))))))))

def stage10Part0Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA9),
   .push 2 1216,
   .op .MLOAD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Swap sA13),
   .op .POP]
def stage10Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := MachineState.readWord (s.memory) 1280
  {s with pc := N 7008, memory := s.memory, stack := (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage10Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part0Program {s with pc := N 6996, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage10Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part0Program, stage10Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216, ha1280, hf1280]

def stage10Part1Program : List Instr :=
  [.op (.Swap sA7),
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]
def stage10Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w2) * (w8)
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 32
  {s with pc := N 7018, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w0) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage10Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part1Program {s with pc := N 7008, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage10Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part1Program, stage10Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha32, hf32]

def stage10Part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]
def stage10Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := MachineState.readWord (s.memory) 128
  let v3 : W := MachineState.readWord (s.memory) 64
  let v4 : W := (v3) * (v2)
  let v5 : W := (v4) + (v1)
  {s with pc := N 7028, memory := s.memory, stack := (v5) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage10Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part2Program {s with pc := N 7018, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} = some (stage10Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part2Program, stage10Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha64, hf64]

def stage10Part3Program : List Instr :=
  [.op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10),
   .push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD]
def stage10Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w3) (w1) (w2)
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 32
  let v3 : W := UInt256.mulMod (v2) (v1) (w12)
  {s with pc := N 7038, memory := s.memory, stack := (v3) :: (v0) :: (w0) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage10Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part3Program {s with pc := N 7028, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage10Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part3Program, stage10Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha32, hf32]

def stage10Part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA10),
   .push 1 128,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage10Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := UInt256.mulMod (v2) (v1) (w11)
  let v4 : W := (v3) + (v0)
  {s with pc := N 7048, memory := s.memory, stack := (v4) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage10Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part4Program {s with pc := N 7038, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage10Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part4Program, stage10Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha64, hf64]

def stage10Part5Program : List Instr :=
  [.op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA0),
   .op .MUL]
def stage10Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w2) + (w0)
  let v1 : W := (w2) + (w1)
  let v2 : W := MachineState.readWord (s.memory) 96
  let v3 : W := (v2) * (v2)
  {s with pc := N 7057, memory := s.memory, stack := (v3) :: (v1) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage10Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part5Program {s with pc := N 7048, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage10Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part5Program, stage10Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]

def stage10Part6Program : List Instr :=
  [.op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD]
def stage10Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 192
  let v2 : W := (w11) * (v1)
  let v3 : W := (v2) + (v0)
  let v4 : W := MachineState.readWord (s.memory) 0
  {s with pc := N 7066, memory := s.memory, stack := (v4) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage10Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part6Program {s with pc := N 7057, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage10Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part6Program, stage10Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192, ha0, hf0]

def stage10Part7Program : List Instr :=
  [.op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]
def stage10Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w9) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := MachineState.readWord (s.memory) 224
  let v3 : W := (v2) * (w4)
  let v4 : W := (v3) + (v1)
  {s with pc := N 7075, memory := s.memory, stack := (v4) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage10Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part7Program {s with pc := N 7066, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage10Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part7Program, stage10Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage10Part8Program : List Instr :=
  [.op (.Dup dA7),
   .op (.Dup dA7),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA4),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD]
def stage10Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w6) * (w7)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w5) * (w4)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7083, memory := s.memory, stack := (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage10Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part8Program {s with pc := N 7075, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage10Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage10Part8Program, stage10Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage10Part9Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .op (.Dup dA14),
   .op .MUL,
   .op .ADD]
def stage10Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w14) * (w11)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w13) * (w2)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7091, memory := s.memory, stack := (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage10Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part9Program {s with pc := N 7083, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage10Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage10Part9Program, stage10Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage10Part10Program : List Instr :=
  [.op (.Swap sA0),
   .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD]
def stage10Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := (v0) + (v0)
  {s with pc := N 7100, memory := s.memory, stack := (v1) :: (v0) :: (v0) :: (w9) :: (w1) :: (w0) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage10Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part10Program {s with pc := N 7091, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage10Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part10Program, stage10Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]

def stage10Part11Program : List Instr :=
  [.push 1 96,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA12)]
def stage10Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w0).toNat 32) 96
  let v1 : W := UInt256.mulMod (w1) (w2) (w3)
  let v2 : W := (v1) + (w4)
  let v3 : W := MachineState.readWord (v0) 192
  {s with pc := N 7110, memory := v0, stack := (w14) :: (v3) :: (w13) :: (v2) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage10Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part11Program {s with pc := N 7100, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage10Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part11Program, stage10Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha192, hf192]

def stage10Part12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD]
def stage10Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 0
  let v3 : W := UInt256.mulMod (w11) (v2) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 7118, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage10Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part12Program {s with pc := N 7110, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage10Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part12Program, stage10Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage10Part13Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA4),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA8)]
def stage10Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod (v0) (w3) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 7127, memory := s.memory, stack := (w7) :: (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage10Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part13Program {s with pc := N 7118, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage10Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part13Program, stage10Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage10Part14Program : List Instr :=
  [.op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD]
def stage10Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w8) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w7) (w6) (w11)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7135, memory := s.memory, stack := (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage10Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part14Program {s with pc := N 7127, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage10Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage10Part14Program, stage10Part14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage10Part15Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA15)]
def stage10Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w11) (w14) (w9)
  let v1 : W := (v0) + (w0)
  {s with pc := N 7143, memory := s.memory, stack := (w13) :: (w2) :: (w9) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage10Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part15Program {s with pc := N 7135, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage10Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage10Part15Program, stage10Part15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage10Part16Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 2 800,
   .op .MSTORE]
def stage10Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.land (w15) (w4)
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v2).toNat 32) 800
  {s with pc := N 7153, memory := v3, stack := (v2) :: (v1) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage10Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part16Program {s with pc := N 7143, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage10Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha800 : (800 : W).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage10Part16Program, stage10Part16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha800, hf800]

def stage10Part17Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage10Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w1) - (w0)
  let v1 : W := (w9) + (v0)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w9)
  {s with pc := N 7162, memory := s.memory, stack := (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage10Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part17Program {s with pc := N 7153, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage10Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage10Part17Program, stage10Part17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage10Program : List Instr := (stage10Part0Program ++ (stage10Part1Program ++ (stage10Part2Program ++ (stage10Part3Program ++ (stage10Part4Program ++ (stage10Part5Program ++ (stage10Part6Program ++ (stage10Part7Program ++ (stage10Part8Program ++ (stage10Part9Program ++ (stage10Part10Program ++ (stage10Part11Program ++ (stage10Part12Program ++ (stage10Part13Program ++ (stage10Part14Program ++ (stage10Part15Program ++ (stage10Part16Program ++ (stage10Part17Program))))))))))))))))))
def stage10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := MachineState.readWord (s.memory) 1280
  let v2 : W := (w14) * (w5)
  let v3 : W := MachineState.readWord (s.memory) 160
  let v4 : W := MachineState.readWord (s.memory) 32
  let v5 : W := (v4) * (v3)
  let v6 : W := (v5) + (v2)
  let v7 : W := MachineState.readWord (s.memory) 128
  let v8 : W := MachineState.readWord (s.memory) 64
  let v9 : W := (v8) * (v7)
  let v10 : W := (v9) + (v6)
  let v11 : W := UInt256.mulMod (w14) (w5) (w8)
  let v12 : W := MachineState.readWord (s.memory) 160
  let v13 : W := MachineState.readWord (s.memory) 32
  let v14 : W := UInt256.mulMod (v13) (v12) (w8)
  let v15 : W := (v14) + (v11)
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := MachineState.readWord (s.memory) 64
  let v18 : W := UInt256.mulMod (v17) (v16) (w8)
  let v19 : W := (v18) + (v15)
  let v20 : W := (w0) + (v19)
  let v21 : W := (w0) + (v10)
  let v22 : W := MachineState.readWord (s.memory) 96
  let v23 : W := (v22) * (v22)
  let v24 : W := (v23) + (v21)
  let v25 : W := MachineState.readWord (s.memory) 192
  let v26 : W := (w9) * (v25)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 0
  let v29 : W := (w7) * (v28)
  let v30 : W := (v29) + (v27)
  let v31 : W := MachineState.readWord (s.memory) 224
  let v32 : W := (v31) * (w2)
  let v33 : W := (v32) + (v30)
  let v34 : W := (v0) * (w6)
  let v35 : W := (v34) + (v33)
  let v36 : W := (w4) * (w3)
  let v37 : W := (v36) + (v35)
  let v38 : W := (w13) * (v1)
  let v39 : W := (v38) + (v37)
  let v40 : W := (w12) * (w1)
  let v41 : W := (v40) + (v39)
  let v42 : W := MachineState.readWord (s.memory) 96
  let v43 : W := (v42) + (v42)
  let v44 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v43).toNat 32) 96
  let v45 : W := UInt256.mulMod (v42) (v42) (w8)
  let v46 : W := (v45) + (v20)
  let v47 : W := MachineState.readWord (v44) 192
  let v48 : W := UInt256.mulMod (w9) (v47) (w8)
  let v49 : W := (v48) + (v46)
  let v50 : W := MachineState.readWord (v44) 0
  let v51 : W := UInt256.mulMod (w7) (v50) (w8)
  let v52 : W := (v51) + (v49)
  let v53 : W := MachineState.readWord (v44) 224
  let v54 : W := UInt256.mulMod (v53) (w2) (w8)
  let v55 : W := (v54) + (v52)
  let v56 : W := UInt256.mulMod (v0) (w6) (w8)
  let v57 : W := (v56) + (v55)
  let v58 : W := UInt256.mulMod (w4) (w3) (w8)
  let v59 : W := (v58) + (v57)
  let v60 : W := UInt256.mulMod (v1) (w13) (w8)
  let v61 : W := (v60) + (v59)
  let v62 : W := UInt256.mulMod (w12) (w1) (w8)
  let v63 : W := (v62) + (v61)
  let v64 : W := UInt256.land (w11) (v41)
  let v65 : ByteArray := MachineState.writeBytes (v44) (Data.Bytes.natToBytesPadded (v64).toNat 32) 800
  let v66 : W := (v63) - (v64)
  let v67 : W := (w8) + (v66)
  let v68 : W := UInt256.mulMod (N 2048) (v67) (w8)
  {s with pc := N 7162, memory := v65, stack := (v68) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Program {s with pc := N 6996, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := MachineState.readWord (s.memory) 1280
  let v2 : W := (w14) * (w5)
  let v3 : W := MachineState.readWord (s.memory) 160
  let v4 : W := MachineState.readWord (s.memory) 32
  let v5 : W := (v4) * (v3)
  let v6 : W := (v5) + (v2)
  let v7 : W := MachineState.readWord (s.memory) 128
  let v8 : W := MachineState.readWord (s.memory) 64
  let v9 : W := (v8) * (v7)
  let v10 : W := (v9) + (v6)
  let v11 : W := UInt256.mulMod (w14) (w5) (w8)
  let v12 : W := MachineState.readWord (s.memory) 160
  let v13 : W := MachineState.readWord (s.memory) 32
  let v14 : W := UInt256.mulMod (v13) (v12) (w8)
  let v15 : W := (v14) + (v11)
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := MachineState.readWord (s.memory) 64
  let v18 : W := UInt256.mulMod (v17) (v16) (w8)
  let v19 : W := (v18) + (v15)
  let v20 : W := (w0) + (v19)
  let v21 : W := (w0) + (v10)
  let v22 : W := MachineState.readWord (s.memory) 96
  let v23 : W := (v22) * (v22)
  let v24 : W := (v23) + (v21)
  let v25 : W := MachineState.readWord (s.memory) 192
  let v26 : W := (w9) * (v25)
  let v27 : W := (v26) + (v24)
  let v28 : W := MachineState.readWord (s.memory) 0
  let v29 : W := (w7) * (v28)
  let v30 : W := (v29) + (v27)
  let v31 : W := MachineState.readWord (s.memory) 224
  let v32 : W := (v31) * (w2)
  let v33 : W := (v32) + (v30)
  let v34 : W := (v0) * (w6)
  let v35 : W := (v34) + (v33)
  let v36 : W := (w4) * (w3)
  let v37 : W := (v36) + (v35)
  let v38 : W := (w13) * (v1)
  let v39 : W := (v38) + (v37)
  let v40 : W := (w12) * (w1)
  let v41 : W := (v40) + (v39)
  let v42 : W := MachineState.readWord (s.memory) 96
  let v43 : W := (v42) + (v42)
  let v44 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v43).toNat 32) 96
  let v45 : W := UInt256.mulMod (v42) (v42) (w8)
  let v46 : W := (v45) + (v20)
  let v47 : W := MachineState.readWord (v44) 192
  let v48 : W := UInt256.mulMod (w9) (v47) (w8)
  let v49 : W := (v48) + (v46)
  let v50 : W := MachineState.readWord (v44) 0
  let v51 : W := UInt256.mulMod (w7) (v50) (w8)
  let v52 : W := (v51) + (v49)
  let v53 : W := MachineState.readWord (v44) 224
  let v54 : W := UInt256.mulMod (v53) (w2) (w8)
  let v55 : W := (v54) + (v52)
  let v56 : W := UInt256.mulMod (v0) (w6) (w8)
  let v57 : W := (v56) + (v55)
  let v58 : W := UInt256.mulMod (w4) (w3) (w8)
  let v59 : W := (v58) + (v57)
  let v60 : W := UInt256.mulMod (v1) (w13) (w8)
  let v61 : W := (v60) + (v59)
  let v62 : W := UInt256.mulMod (w12) (w1) (w8)
  let v63 : W := (v62) + (v61)
  let v64 : W := UInt256.land (w11) (v41)
  let v65 : ByteArray := MachineState.writeBytes (v44) (Data.Bytes.natToBytesPadded (v64).toNat 32) 800
  let v66 : W := (v63) - (v64)
  let v67 : W := (w8) + (v66)
  let v68 : W := UInt256.mulMod (N 2048) (v67) (w8)
  have h0 : runInstructions stage10Part0Program {s with pc := N 6996, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7008, memory := s.memory, stack := (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part0Model, v0, v1] using stage10Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage10Part1Program {s with pc := N 7008, memory := s.memory, stack := (v0) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7018, memory := s.memory, stack := (v4) :: (v3) :: (v2) :: (w5) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part1Model, v2, v3, v4] using stage10Part1_run ({s with memory := s.memory}) (v0) (w8) (w14) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage10Part2Program {s with pc := N 7018, memory := s.memory, stack := (v4) :: (v3) :: (v2) :: (w5) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7028, memory := s.memory, stack := (v10) :: (w5) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part2Model, v5, v6, v7, v8, v9, v10] using stage10Part2_run ({s with memory := s.memory}) (v4) (v3) (v2) (w5) (w8) (w14) (w0) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage10Part3Program {s with pc := N 7028, memory := s.memory, stack := (v10) :: (w5) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7038, memory := s.memory, stack := (v14) :: (v11) :: (v10) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part3Model, v11, v12, v13, v14] using stage10Part3_run ({s with memory := s.memory}) (v10) (w5) (w8) (w14) (w0) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage10Part4Program {s with pc := N 7038, memory := s.memory, stack := (v14) :: (v11) :: (v10) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7048, memory := s.memory, stack := (v19) :: (v10) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part4Model, v15, v16, v17, v18, v19] using stage10Part4_run ({s with memory := s.memory}) (v14) (v11) (v10) (w0) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage10Part5Program {s with pc := N 7048, memory := s.memory, stack := (v19) :: (v10) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7057, memory := s.memory, stack := (v23) :: (v21) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part5Model, v20, v21, v22, v23] using stage10Part5_run ({s with memory := s.memory}) (v19) (v10) (w0) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage10Part6Program {s with pc := N 7057, memory := s.memory, stack := (v23) :: (v21) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7066, memory := s.memory, stack := (v28) :: (v27) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part6Model, v24, v25, v26, v27, v28] using stage10Part6_run ({s with memory := s.memory}) (v23) (v21) (v20) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage10Part7Program {s with pc := N 7066, memory := s.memory, stack := (v28) :: (v27) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7075, memory := s.memory, stack := (v33) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part7Model, v29, v30, v31, v32, v33] using stage10Part7_run ({s with memory := s.memory}) (v28) (v27) (v20) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage10Part8Program {s with pc := N 7075, memory := s.memory, stack := (v33) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7083, memory := s.memory, stack := (v37) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part8Model, v34, v35, v36, v37] using stage10Part8_run ({s with memory := s.memory}) (v33) (v20) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage10Part9Program {s with pc := N 7083, memory := s.memory, stack := (v37) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7091, memory := s.memory, stack := (v41) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part9Model, v38, v39, v40, v41] using stage10Part9_run ({s with memory := s.memory}) (v37) (v20) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage10Part10Program {s with pc := N 7091, memory := s.memory, stack := (v41) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7100, memory := s.memory, stack := (v43) :: (v42) :: (v42) :: (w8) :: (v20) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part10Model, v42, v43] using stage10Part10_run ({s with memory := s.memory}) (v41) (v20) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage10Part11Program {s with pc := N 7100, memory := s.memory, stack := (v43) :: (v42) :: (v42) :: (w8) :: (v20) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7110, memory := v44, stack := (w9) :: (v47) :: (w8) :: (v46) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part11Model, v44, v45, v46, v47] using stage10Part11_run ({s with memory := s.memory}) (v43) (v42) (v42) (w8) (v20) (v41) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage10Part12Program {s with pc := N 7110, memory := v44, stack := (w9) :: (v47) :: (w8) :: (v46) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7118, memory := v44, stack := (v52) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part12Model, v48, v49, v50, v51, v52] using stage10Part12_run ({s with memory := v44}) (w9) (v47) (w8) (v46) (v41) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions stage10Part13Program {s with pc := N 7118, memory := v44, stack := (v52) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7127, memory := v44, stack := (w6) :: (w8) :: (v55) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part13Model, v53, v54, v55] using stage10Part13_run ({s with memory := v44}) (v52) (v41) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h14 : runInstructions stage10Part14Program {s with pc := N 7127, memory := v44, stack := (w6) :: (w8) :: (v55) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7135, memory := v44, stack := (v59) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part14Model, v56, v57, v58, v59] using stage10Part14_run ({s with memory := v44}) (w6) (w8) (v55) (v41) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h15 : runInstructions stage10Part15Program {s with pc := N 7135, memory := v44, stack := (v59) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7143, memory := v44, stack := (w12) :: (w1) :: (w8) :: (v61) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part15Model, v60, v61] using stage10Part15_run ({s with memory := v44}) (v59) (v41) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h16 : runInstructions stage10Part16Program {s with pc := N 7143, memory := v44, stack := (w12) :: (w1) :: (w8) :: (v61) :: (v41) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7153, memory := v65, stack := (v64) :: (v63) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part16Model, v62, v63, v64, v65] using stage10Part16_run ({s with memory := v44}) (w12) (w1) (w8) (v61) (v41) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  have h17 : runInstructions stage10Part17Program {s with pc := N 7153, memory := v65, stack := (v64) :: (v63) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7162, memory := v65, stack := (v68) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage10Part17Model, v66, v67, v68] using stage10Part17_run ({s with memory := v65}) (v64) (v63) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (v1) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 h17)))))))))))))))))

def stage11Part0Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Swap sA0),
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .push 1 160,
   .op .MLOAD]
def stage11Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 7173, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage11Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part0Program {s with pc := N 7162, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage11Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage11Part0Program, stage11Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha96, hf96, ha160, hf160]

def stage11Part1Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA14),
   .op (.Dup dA7),
   .op (.Dup dA2),
   .op .MULMOD]
def stage11Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 32
  let v2 : W := UInt256.mulMod (v1) (w4) (w12)
  {s with pc := N 7183, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage11Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part1Program {s with pc := N 7173, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage11Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage11Part1Program, stage11Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha32, hf32]

def stage11Part2Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA5),
   .op (.Dup dA7)]
def stage11Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w3) (w2) (w15)
  let v1 : W := (v0) + (w0)
  {s with pc := N 7191, memory := s.memory, stack := (w5) :: (w4) :: (w15) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: rest}
theorem stage11Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part2Program {s with pc := N 7183, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: rest} = some (stage11Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage11Part2Program, stage11Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage11Part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA6),
   .op .ADD,
   .op (.Swap sA6),
   .op .MUL,
   .op (.Swap sA1),
   .op .MUL]
def stage11Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := (w9) + (v1)
  let v3 : W := (w10) * (w4)
  let v4 : W := (w6) * (w5)
  {s with pc := N 7199, memory := s.memory, stack := (v4) :: (v3) :: (w7) :: (w8) :: (w9) :: (v2) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: (w22) :: (w23) :: (w24) :: rest}
theorem stage11Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part3Program {s with pc := N 7191, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: (w22) :: (w23) :: (w24) :: rest} = some (stage11Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage11Part3Program, stage11Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage11Part4Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA1),
   .op .MUL,
   .op .ADD,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA11)]
def stage11Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w3) * (w2)
  let v2 : W := (v1) + (v0)
  let v3 : W := (v2) + (w4)
  let v4 : W := MachineState.readWord (s.memory) 0
  {s with pc := N 7207, memory := s.memory, stack := (w14) :: (v4) :: (v3) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage11Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part4Program {s with pc := N 7199, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} = some (stage11Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage11Part4Program, stage11Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage11Part5Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3)]
def stage11Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := MachineState.readWord (s.memory) 224
  let v3 : W := (w10) * (v2)
  let v4 : W := (v3) + (v1)
  {s with pc := N 7216, memory := s.memory, stack := (w5) :: (v4) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage11Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part5Program {s with pc := N 7207, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage11Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage11Part5Program, stage11Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage11Part6Program : List Instr :=
  [.op (.Dup dA7),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA7),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def stage11Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w7) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (w6) * (w8)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7224, memory := s.memory, stack := (w12) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage11Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part6Program {s with pc := N 7216, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage11Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage11Part6Program, stage11Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage11Part7Program : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0)]
def stage11Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w5) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (w14) * (w15)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7232, memory := s.memory, stack := (w2) :: (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage11Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part7Program {s with pc := N 7224, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage11Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage11Part7Program, stage11Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage11Part8Program : List Instr :=
  [.op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage11Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod (w10) (v0) (w9)
  let v2 : W := (v1) + (w0)
  {s with pc := N 7239, memory := s.memory, stack := (w9) :: (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage11Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part8Program {s with pc := N 7232, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage11Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage11Part8Program, stage11Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage11Part9Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA4),
   .op (.Dup dA8)]
def stage11Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod (w9) (v0) (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 7248, memory := s.memory, stack := (w7) :: (w4) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage11Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part9Program {s with pc := N 7239, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage11Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage11Part9Program, stage11Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage11Part10Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA8),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage11Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w8) (w10) (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7256, memory := s.memory, stack := (w12) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage11Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part10Program {s with pc := N 7248, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage11Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage11Part10Program, stage11Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage11Part11Program : List Instr :=
  [.op (.Dup dA5),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op .MULMOD]
def stage11Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w12) (w5) (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := UInt256.mulMod (w14) (w15) (w10)
  {s with pc := N 7264, memory := s.memory, stack := (v2) :: (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage11Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part11Program {s with pc := N 7256, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage11Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage11Part11Program, stage11Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage11Part12Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 2 832,
   .op .MSTORE,
   .op (.Dup dA9)]
def stage11Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.land (w13) (w2)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v1).toNat 32) 832
  {s with pc := N 7274, memory := v2, stack := (w10) :: (v1) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage11Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part12Program {s with pc := N 7264, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage11Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage11Part12Program, stage11Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha832, hf832]

def stage11Part13Program : List Instr :=
  [.op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage11Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w2) - (w1)
  let v1 : W := (w0) + (v0)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w0)
  {s with pc := N 7282, memory := s.memory, stack := (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage11Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part13Program {s with pc := N 7274, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage11Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage11Part13Program, stage11Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage11Program : List Instr := (stage11Part0Program ++ (stage11Part1Program ++ (stage11Part2Program ++ (stage11Part3Program ++ (stage11Part4Program ++ (stage11Part5Program ++ (stage11Part6Program ++ (stage11Part7Program ++ (stage11Part8Program ++ (stage11Part9Program ++ (stage11Part10Program ++ (stage11Part11Program ++ (stage11Part12Program ++ (stage11Part13Program))))))))))))))
def stage11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := MachineState.readWord (s.memory) 64
  let v4 : W := MachineState.readWord (s.memory) 32
  let v5 : W := UInt256.mulMod (v4) (w14) (w8)
  let v6 : W := UInt256.mulMod (v2) (v3) (w8)
  let v7 : W := (v6) + (v5)
  let v8 : W := UInt256.mulMod (v0) (v1) (w8)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w0) + (v9)
  let v11 : W := (w14) * (v4)
  let v12 : W := (v2) * (v3)
  let v13 : W := (v12) + (v11)
  let v14 : W := (v0) * (v1)
  let v15 : W := (v14) + (v13)
  let v16 : W := (v15) + (w0)
  let v17 : W := MachineState.readWord (s.memory) 0
  let v18 : W := (w9) * (v17)
  let v19 : W := (v18) + (v16)
  let v20 : W := MachineState.readWord (s.memory) 224
  let v21 : W := (w7) * (v20)
  let v22 : W := (v21) + (v19)
  let v23 : W := (w5) * (w2)
  let v24 : W := (v23) + (v22)
  let v25 : W := (w4) * (w6)
  let v26 : W := (v25) + (v24)
  let v27 : W := (w3) * (w10)
  let v28 : W := (v27) + (v26)
  let v29 : W := (w12) * (w13)
  let v30 : W := (v29) + (v28)
  let v31 : W := MachineState.readWord (s.memory) 0
  let v32 : W := UInt256.mulMod (w9) (v31) (w8)
  let v33 : W := (v32) + (v10)
  let v34 : W := MachineState.readWord (s.memory) 224
  let v35 : W := UInt256.mulMod (w7) (v34) (w8)
  let v36 : W := (v35) + (v33)
  let v37 : W := UInt256.mulMod (w5) (w2) (w8)
  let v38 : W := (v37) + (v36)
  let v39 : W := UInt256.mulMod (w4) (w6) (w8)
  let v40 : W := (v39) + (v38)
  let v41 : W := UInt256.mulMod (w10) (w3) (w8)
  let v42 : W := (v41) + (v40)
  let v43 : W := UInt256.mulMod (w12) (w13) (w8)
  let v44 : W := (v43) + (v42)
  let v45 : W := UInt256.land (w11) (v30)
  let v46 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v45).toNat 32) 832
  let v47 : W := (v44) - (v45)
  let v48 : W := (w8) + (v47)
  let v49 : W := UInt256.mulMod (N 2048) (v48) (w8)
  {s with pc := N 7282, memory := v46, stack := (v49) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Program {s with pc := N 7162, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := MachineState.readWord (s.memory) 64
  let v4 : W := MachineState.readWord (s.memory) 32
  let v5 : W := UInt256.mulMod (v4) (w14) (w8)
  let v6 : W := UInt256.mulMod (v2) (v3) (w8)
  let v7 : W := (v6) + (v5)
  let v8 : W := UInt256.mulMod (v0) (v1) (w8)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w0) + (v9)
  let v11 : W := (w14) * (v4)
  let v12 : W := (v2) * (v3)
  let v13 : W := (v12) + (v11)
  let v14 : W := (v0) * (v1)
  let v15 : W := (v14) + (v13)
  let v16 : W := (v15) + (w0)
  let v17 : W := MachineState.readWord (s.memory) 0
  let v18 : W := (w9) * (v17)
  let v19 : W := (v18) + (v16)
  let v20 : W := MachineState.readWord (s.memory) 224
  let v21 : W := (w7) * (v20)
  let v22 : W := (v21) + (v19)
  let v23 : W := (w5) * (w2)
  let v24 : W := (v23) + (v22)
  let v25 : W := (w4) * (w6)
  let v26 : W := (v25) + (v24)
  let v27 : W := (w3) * (w10)
  let v28 : W := (v27) + (v26)
  let v29 : W := (w12) * (w13)
  let v30 : W := (v29) + (v28)
  let v31 : W := MachineState.readWord (s.memory) 0
  let v32 : W := UInt256.mulMod (w9) (v31) (w8)
  let v33 : W := (v32) + (v10)
  let v34 : W := MachineState.readWord (s.memory) 224
  let v35 : W := UInt256.mulMod (w7) (v34) (w8)
  let v36 : W := (v35) + (v33)
  let v37 : W := UInt256.mulMod (w5) (w2) (w8)
  let v38 : W := (v37) + (v36)
  let v39 : W := UInt256.mulMod (w4) (w6) (w8)
  let v40 : W := (v39) + (v38)
  let v41 : W := UInt256.mulMod (w10) (w3) (w8)
  let v42 : W := (v41) + (v40)
  let v43 : W := UInt256.mulMod (w12) (w13) (w8)
  let v44 : W := (v43) + (v42)
  let v45 : W := UInt256.land (w11) (v30)
  let v46 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v45).toNat 32) 832
  let v47 : W := (v44) - (v45)
  let v48 : W := (w8) + (v47)
  let v49 : W := UInt256.mulMod (N 2048) (v48) (w8)
  have h0 : runInstructions stage11Part0Program {s with pc := N 7162, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7173, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part0Model, v0, v1, v2] using stage11Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage11Part1Program {s with pc := N 7173, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7183, memory := s.memory, stack := (v5) :: (v4) :: (v3) :: (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part1Model, v3, v4, v5] using stage11Part1_run ({s with memory := s.memory}) (v2) (v1) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage11Part2Program {s with pc := N 7183, memory := s.memory, stack := (v5) :: (v4) :: (v3) :: (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7191, memory := s.memory, stack := (v0) :: (v1) :: (w8) :: (v7) :: (v4) :: (v3) :: (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part2Model, v6, v7] using stage11Part2_run ({s with memory := s.memory}) (v5) (v4) (v3) (v2) (v1) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage11Part3Program {s with pc := N 7191, memory := s.memory, stack := (v0) :: (v1) :: (w8) :: (v7) :: (v4) :: (v3) :: (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7199, memory := s.memory, stack := (v12) :: (v11) :: (v1) :: (v0) :: (w0) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part3Model, v8, v9, v10, v11, v12] using stage11Part3_run ({s with memory := s.memory}) (v0) (v1) (w8) (v7) (v4) (v3) (v2) (v1) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage11Part4Program {s with pc := N 7199, memory := s.memory, stack := (v12) :: (v11) :: (v1) :: (v0) :: (w0) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7207, memory := s.memory, stack := (w9) :: (v17) :: (v16) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part4Model, v13, v14, v15, v16, v17] using stage11Part4_run ({s with memory := s.memory}) (v12) (v11) (v1) (v0) (w0) (v10) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage11Part5Program {s with pc := N 7207, memory := s.memory, stack := (w9) :: (v17) :: (v16) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7216, memory := s.memory, stack := (w2) :: (v22) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part5Model, v18, v19, v20, v21, v22] using stage11Part5_run ({s with memory := s.memory}) (w9) (v17) (v16) (v10) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage11Part6Program {s with pc := N 7216, memory := s.memory, stack := (w2) :: (v22) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7224, memory := s.memory, stack := (w10) :: (v26) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part6Model, v23, v24, v25, v26] using stage11Part6_run ({s with memory := s.memory}) (w2) (v22) (v10) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage11Part7Program {s with pc := N 7224, memory := s.memory, stack := (w10) :: (v26) :: (v10) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7232, memory := s.memory, stack := (v10) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part7Model, v27, v28, v29, v30] using stage11Part7_run ({s with memory := s.memory}) (w10) (v26) (v10) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage11Part8Program {s with pc := N 7232, memory := s.memory, stack := (v10) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7239, memory := s.memory, stack := (w8) :: (v33) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part8Model, v31, v32, v33] using stage11Part8_run ({s with memory := s.memory}) (v10) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage11Part9Program {s with pc := N 7239, memory := s.memory, stack := (w8) :: (v33) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7248, memory := s.memory, stack := (w5) :: (w2) :: (w8) :: (v36) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part9Model, v34, v35, v36] using stage11Part9_run ({s with memory := s.memory}) (w8) (v33) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage11Part10Program {s with pc := N 7248, memory := s.memory, stack := (w5) :: (w2) :: (w8) :: (v36) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7256, memory := s.memory, stack := (w8) :: (v40) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part10Model, v37, v38, v39, v40] using stage11Part10_run ({s with memory := s.memory}) (w5) (w2) (w8) (v36) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage11Part11Program {s with pc := N 7256, memory := s.memory, stack := (w8) :: (v40) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7264, memory := s.memory, stack := (v43) :: (v42) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part11Model, v41, v42, v43] using stage11Part11_run ({s with memory := s.memory}) (w8) (v40) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage11Part12Program {s with pc := N 7264, memory := s.memory, stack := (v43) :: (v42) :: (v30) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7274, memory := v46, stack := (w8) :: (v45) :: (v44) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part12Model, v44, v45, v46] using stage11Part12_run ({s with memory := s.memory}) (v43) (v42) (v30) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions stage11Part13Program {s with pc := N 7274, memory := v46, stack := (w8) :: (v45) :: (v44) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7282, memory := v46, stack := (v49) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage11Part13Model, v47, v48, v49] using stage11Part13_run ({s with memory := v46}) (w8) (v45) (v44) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

def stage12Part0Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Swap sA0),
   .push 1 160,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD]
def stage12Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 7293, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage12Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part0Program {s with pc := N 7282, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage12Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage12Part0Program, stage12Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha64, hf64, ha96, hf96]

def stage12Part1Program : List Instr :=
  [.op (.Dup dA12),
   .op (.Dup dA5),
   .op (.Dup dA2),
   .op .MULMOD,
   .op (.Dup dA13),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD]
def stage12Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w4) (w12)
  let v1 : W := UInt256.mulMod (w2) (w1) (w12)
  {s with pc := N 7301, memory := s.memory, stack := (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage12Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part1Program {s with pc := N 7293, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage12Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part1Program, stage12Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA4),
   .op .ADD,
   .op (.Swap sA4),
   .op .MUL,
   .op (.Swap sA1),
   .op .MUL,
   .op .ADD]
def stage12Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w5) + (v0)
  let v2 : W := (w6) * (w2)
  let v3 : W := (w4) * (w3)
  let v4 : W := (v3) + (v2)
  {s with pc := N 7309, memory := s.memory, stack := (v4) :: (w5) :: (v1) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage12Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part2Program {s with pc := N 7301, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} = some (stage12Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part2Program, stage12Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Part3Program : List Instr :=
  [.op .ADD,
   .push 1 128,
   .op .MLOAD,
   .op (.Dup dA0),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD]
def stage12Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) * (v1)
  let v3 : W := (v2) + (v0)
  let v4 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 7319, memory := s.memory, stack := (v4) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage12Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part3Program {s with pc := N 7309, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage12Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage12Part3Program, stage12Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha224, hf224]

def stage12Part4Program : List Instr :=
  [.op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3)]
def stage12Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w11) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (w9) * (w7)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7327, memory := s.memory, stack := (w4) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage12Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part4Program {s with pc := N 7319, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage12Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part4Program, stage12Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Part5Program : List Instr :=
  [.op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA4)]
def stage12Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w6) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (w8) * (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7335, memory := s.memory, stack := (w5) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage12Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part5Program {s with pc := N 7327, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage12Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part5Program, stage12Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Part6Program : List Instr :=
  [.op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup dA0)]
def stage12Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w14) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := MachineState.readWord (s.memory) 128
  {s with pc := N 7344, memory := s.memory, stack := (v2) :: (v2) :: (w10) :: (w2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage12Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part6Program {s with pc := N 7335, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage12Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage12Part6Program, stage12Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]

def stage12Part7Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD]
def stage12Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := MachineState.readWord (s.memory) 224
  let v3 : W := UInt256.mulMod (w13) (v2) (w12)
  let v4 : W := (v3) + (v1)
  {s with pc := N 7353, memory := s.memory, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage12Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part7Program {s with pc := N 7344, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage12Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage12Part7Program, stage12Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage12Part8Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA4),
   .op (.Dup dA7)]
def stage12Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w8) (w6) (w9)
  let v1 : W := (v0) + (w0)
  {s with pc := N 7361, memory := s.memory, stack := (w5) :: (w3) :: (w9) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage12Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part8Program {s with pc := N 7353, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage12Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part8Program, stage12Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Part9Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage12Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w10) (w14) (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7369, memory := s.memory, stack := (w12) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage12Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part9Program {s with pc := N 7361, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage12Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part9Program, stage12Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Part10Program : List Instr :=
  [.op (.Dup dA5),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0)]
def stage12Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w14) (w5) (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := UInt256.land (w13) (w2)
  {s with pc := N 7377, memory := s.memory, stack := (v2) :: (v2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage12Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part10Program {s with pc := N 7369, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage12Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part10Program, stage12Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Part11Program : List Instr :=
  [.push 1 32,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048]
def stage12Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w0).toNat 32) 32
  let v1 : W := (w2) - (w1)
  let v2 : W := (w10) + (v1)
  {s with pc := N 7388, memory := v0, stack := (N 2048) :: (v2) :: (w10) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage12Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part11Program {s with pc := N 7377, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage12Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage12Part11Program, stage12Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage12Part12Program : List Instr :=
  [.op .MULMOD]
def stage12Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  {s with pc := N 7389, memory := s.memory, stack := (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage12Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part12Program {s with pc := N 7388, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage12Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage12Part12Program, stage12Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage12Program : List Instr := (stage12Part0Program ++ (stage12Part1Program ++ (stage12Part2Program ++ (stage12Part3Program ++ (stage12Part4Program ++ (stage12Part5Program ++ (stage12Part6Program ++ (stage12Part7Program ++ (stage12Part8Program ++ (stage12Part9Program ++ (stage12Part10Program ++ (stage12Part11Program ++ (stage12Part12Program)))))))))))))
def stage12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := UInt256.mulMod (v2) (w14) (w8)
  let v4 : W := UInt256.mulMod (v0) (v1) (w8)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w0) + (v5)
  let v7 : W := (w14) * (v2)
  let v8 : W := (v0) * (v1)
  let v9 : W := (v8) + (v7)
  let v10 : W := (v9) + (w0)
  let v11 : W := MachineState.readWord (s.memory) 128
  let v12 : W := (v11) * (v11)
  let v13 : W := (v12) + (v10)
  let v14 : W := MachineState.readWord (s.memory) 224
  let v15 : W := (w9) * (v14)
  let v16 : W := (v15) + (v13)
  let v17 : W := (w7) * (w5)
  let v18 : W := (v17) + (v16)
  let v19 : W := (w4) * (w2)
  let v20 : W := (v19) + (v18)
  let v21 : W := (w6) * (w10)
  let v22 : W := (v21) + (v20)
  let v23 : W := (w12) * (w3)
  let v24 : W := (v23) + (v22)
  let v25 : W := MachineState.readWord (s.memory) 128
  let v26 : W := UInt256.mulMod (v25) (v25) (w8)
  let v27 : W := (v26) + (v6)
  let v28 : W := MachineState.readWord (s.memory) 224
  let v29 : W := UInt256.mulMod (w9) (v28) (w8)
  let v30 : W := (v29) + (v27)
  let v31 : W := UInt256.mulMod (w7) (w5) (w8)
  let v32 : W := (v31) + (v30)
  let v33 : W := UInt256.mulMod (w4) (w2) (w8)
  let v34 : W := (v33) + (v32)
  let v35 : W := UInt256.mulMod (w6) (w10) (w8)
  let v36 : W := (v35) + (v34)
  let v37 : W := UInt256.mulMod (w12) (w3) (w8)
  let v38 : W := (v37) + (v36)
  let v39 : W := UInt256.land (w11) (v24)
  let v40 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v39).toNat 32) 32
  let v41 : W := (v38) - (v39)
  let v42 : W := (w8) + (v41)
  let v43 : W := UInt256.mulMod (N 2048) (v42) (w8)
  {s with pc := N 7389, memory := v40, stack := (v43) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Program {s with pc := N 7282, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 96
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := UInt256.mulMod (v2) (w14) (w8)
  let v4 : W := UInt256.mulMod (v0) (v1) (w8)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w0) + (v5)
  let v7 : W := (w14) * (v2)
  let v8 : W := (v0) * (v1)
  let v9 : W := (v8) + (v7)
  let v10 : W := (v9) + (w0)
  let v11 : W := MachineState.readWord (s.memory) 128
  let v12 : W := (v11) * (v11)
  let v13 : W := (v12) + (v10)
  let v14 : W := MachineState.readWord (s.memory) 224
  let v15 : W := (w9) * (v14)
  let v16 : W := (v15) + (v13)
  let v17 : W := (w7) * (w5)
  let v18 : W := (v17) + (v16)
  let v19 : W := (w4) * (w2)
  let v20 : W := (v19) + (v18)
  let v21 : W := (w6) * (w10)
  let v22 : W := (v21) + (v20)
  let v23 : W := (w12) * (w3)
  let v24 : W := (v23) + (v22)
  let v25 : W := MachineState.readWord (s.memory) 128
  let v26 : W := UInt256.mulMod (v25) (v25) (w8)
  let v27 : W := (v26) + (v6)
  let v28 : W := MachineState.readWord (s.memory) 224
  let v29 : W := UInt256.mulMod (w9) (v28) (w8)
  let v30 : W := (v29) + (v27)
  let v31 : W := UInt256.mulMod (w7) (w5) (w8)
  let v32 : W := (v31) + (v30)
  let v33 : W := UInt256.mulMod (w4) (w2) (w8)
  let v34 : W := (v33) + (v32)
  let v35 : W := UInt256.mulMod (w6) (w10) (w8)
  let v36 : W := (v35) + (v34)
  let v37 : W := UInt256.mulMod (w12) (w3) (w8)
  let v38 : W := (v37) + (v36)
  let v39 : W := UInt256.land (w11) (v24)
  let v40 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v39).toNat 32) 32
  let v41 : W := (v38) - (v39)
  let v42 : W := (w8) + (v41)
  let v43 : W := UInt256.mulMod (N 2048) (v42) (w8)
  have h0 : runInstructions stage12Part0Program {s with pc := N 7282, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7293, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part0Model, v0, v1, v2] using stage12Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage12Part1Program {s with pc := N 7293, memory := s.memory, stack := (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7301, memory := s.memory, stack := (v4) :: (v3) :: (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part1Model, v3, v4] using stage12Part1_run ({s with memory := s.memory}) (v2) (v1) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage12Part2Program {s with pc := N 7301, memory := s.memory, stack := (v4) :: (v3) :: (v2) :: (v1) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7309, memory := s.memory, stack := (v9) :: (w0) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part2Model, v5, v6, v7, v8, v9] using stage12Part2_run ({s with memory := s.memory}) (v4) (v3) (v2) (v1) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage12Part3Program {s with pc := N 7309, memory := s.memory, stack := (v9) :: (w0) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7319, memory := s.memory, stack := (v14) :: (v13) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part3Model, v10, v11, v12, v13, v14] using stage12Part3_run ({s with memory := s.memory}) (v9) (w0) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage12Part4Program {s with pc := N 7319, memory := s.memory, stack := (v14) :: (v13) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7327, memory := s.memory, stack := (w2) :: (v18) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part4Model, v15, v16, v17, v18] using stage12Part4_run ({s with memory := s.memory}) (v14) (v13) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage12Part5Program {s with pc := N 7327, memory := s.memory, stack := (w2) :: (v18) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7335, memory := s.memory, stack := (w3) :: (v22) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part5Model, v19, v20, v21, v22] using stage12Part5_run ({s with memory := s.memory}) (w2) (v18) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage12Part6Program {s with pc := N 7335, memory := s.memory, stack := (w3) :: (v22) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7344, memory := s.memory, stack := (v25) :: (v25) :: (w8) :: (v6) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part6Model, v23, v24, v25] using stage12Part6_run ({s with memory := s.memory}) (w3) (v22) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage12Part7Program {s with pc := N 7344, memory := s.memory, stack := (v25) :: (v25) :: (w8) :: (v6) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7353, memory := s.memory, stack := (v30) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part7Model, v26, v27, v28, v29, v30] using stage12Part7_run ({s with memory := s.memory}) (v25) (v25) (w8) (v6) (v24) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage12Part8Program {s with pc := N 7353, memory := s.memory, stack := (v30) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7361, memory := s.memory, stack := (w4) :: (w2) :: (w8) :: (v32) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part8Model, v31, v32] using stage12Part8_run ({s with memory := s.memory}) (v30) (v24) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage12Part9Program {s with pc := N 7361, memory := s.memory, stack := (w4) :: (w2) :: (w8) :: (v32) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7369, memory := s.memory, stack := (w8) :: (v36) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part9Model, v33, v34, v35, v36] using stage12Part9_run ({s with memory := s.memory}) (w4) (w2) (w8) (v32) (v24) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions stage12Part10Program {s with pc := N 7369, memory := s.memory, stack := (w8) :: (v36) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7377, memory := s.memory, stack := (v39) :: (v39) :: (v38) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part10Model, v37, v38, v39] using stage12Part10_run ({s with memory := s.memory}) (w8) (v36) (v24) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions stage12Part11Program {s with pc := N 7377, memory := s.memory, stack := (v39) :: (v39) :: (v38) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7388, memory := v40, stack := (N 2048) :: (v42) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part11Model, v40, v41, v42] using stage12Part11_run ({s with memory := s.memory}) (v39) (v39) (v38) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions stage12Part12Program {s with pc := N 7388, memory := v40, stack := (N 2048) :: (v42) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7389, memory := v40, stack := (v43) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage12Part12Model, v43] using stage12Part12_run ({s with memory := v40}) (N 2048) (v42) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

def stage13Part0Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Swap sA0),
   .push 1 160,
   .op .MLOAD,
   .push 1 128,
   .op .MLOAD,
   .op (.Dup dA0),
   .op .ADD]
def stage13Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) + (v1)
  {s with pc := N 7399, memory := s.memory, stack := (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage13Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part0Program {s with pc := N 7389, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage13Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage13Part0Program, stage13Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha128, hf128]

def stage13Part1Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op (.Dup dA2),
   .op .MULMOD,
   .op (.Dup dA13),
   .op (.Dup dA3)]
def stage13Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := UInt256.mulMod (v0) (w3) (w11)
  {s with pc := N 7408, memory := s.memory, stack := (w0) :: (w11) :: (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage13Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part1Program {s with pc := N 7399, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage13Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage13Part1Program, stage13Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]

def stage13Part2Program : List Instr :=
  [.op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA4),
   .op .ADD,
   .op (.Swap sA4),
   .op .MUL,
   .op (.Swap sA1)]
def stage13Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w5) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (w6) + (v1)
  let v3 : W := (w7) * (w3)
  {s with pc := N 7416, memory := s.memory, stack := (w5) :: (w4) :: (v3) :: (w6) :: (v2) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: rest}
theorem stage13Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part2Program {s with pc := N 7408, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: rest} = some (stage13Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part2Program, stage13Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Part3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5)]
def stage13Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (v1) + (w3)
  let v3 : W := (w13) * (w9)
  let v4 : W := (v3) + (v2)
  {s with pc := N 7424, memory := s.memory, stack := (w8) :: (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage13Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part3Program {s with pc := N 7416, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage13Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part3Program, stage13Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Part4Program : List Instr :=
  [.op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA7)]
def stage13Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w9) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (w4) * (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7432, memory := s.memory, stack := (w8) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage13Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part4Program {s with pc := N 7424, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part4Program, stage13Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Part5Program : List Instr :=
  [.op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA12),
   .op .MULMOD]
def stage13Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w14) * (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := UInt256.mulMod (w11) (w7) (w10)
  {s with pc := N 7440, memory := s.memory, stack := (v2) :: (w2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage13Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part5Program {s with pc := N 7432, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part5Program, stage13Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA4)]
def stage13Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (w9) (w6) (w10)
  let v2 : W := (v1) + (v0)
  {s with pc := N 7448, memory := s.memory, stack := (w4) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage13Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part6Program {s with pc := N 7440, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part6Program, stage13Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Part7Program : List Instr :=
  [.op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA8),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD]
def stage13Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w13) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w15) (w9) (w11)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7456, memory := s.memory, stack := (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage13Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part7Program {s with pc := N 7448, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage13Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part7Program, stage13Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Part8Program : List Instr :=
  [.op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 1 64,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1)]
def stage13Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (w12) (w1)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v0).toNat 32) 64
  {s with pc := N 7465, memory := v1, stack := (w0) :: (v0) :: (w9) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage13Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part8Program {s with pc := N 7456, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage13Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage13Part8Program, stage13Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]

def stage13Part9Program : List Instr :=
  [.op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage13Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) - (w1)
  let v1 : W := (w2) + (v0)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w2)
  {s with pc := N 7472, memory := s.memory, stack := (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage13Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part9Program {s with pc := N 7465, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part9Program, stage13Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Program : List Instr := (stage13Part0Program ++ (stage13Part1Program ++ (stage13Part2Program ++ (stage13Part3Program ++ (stage13Part4Program ++ (stage13Part5Program ++ (stage13Part6Program ++ (stage13Part7Program ++ (stage13Part8Program ++ (stage13Part9Program))))))))))
def stage13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) + (v1)
  let v3 : W := MachineState.readWord (s.memory) 96
  let v4 : W := UInt256.mulMod (v3) (w14) (w8)
  let v5 : W := UInt256.mulMod (v0) (v2) (w8)
  let v6 : W := (v5) + (v4)
  let v7 : W := (w0) + (v6)
  let v8 : W := (w14) * (v3)
  let v9 : W := (v0) * (v2)
  let v10 : W := (v9) + (v8)
  let v11 : W := (v10) + (w0)
  let v12 : W := (w9) * (w5)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w7) * (w4)
  let v15 : W := (v14) + (v13)
  let v16 : W := (w2) * (w10)
  let v17 : W := (v16) + (v15)
  let v18 : W := (w12) * (w6)
  let v19 : W := (v18) + (v17)
  let v20 : W := UInt256.mulMod (w9) (w5) (w8)
  let v21 : W := (v20) + (v7)
  let v22 : W := UInt256.mulMod (w7) (w4) (w8)
  let v23 : W := (v22) + (v21)
  let v24 : W := UInt256.mulMod (w10) (w2) (w8)
  let v25 : W := (v24) + (v23)
  let v26 : W := UInt256.mulMod (w12) (w6) (w8)
  let v27 : W := (v26) + (v25)
  let v28 : W := UInt256.land (w11) (v19)
  let v29 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v28).toNat 32) 64
  let v30 : W := (v27) - (v28)
  let v31 : W := (w8) + (v30)
  let v32 : W := UInt256.mulMod (N 2048) (v31) (w8)
  {s with pc := N 7472, memory := v29, stack := (v32) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Program {s with pc := N 7389, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) + (v1)
  let v3 : W := MachineState.readWord (s.memory) 96
  let v4 : W := UInt256.mulMod (v3) (w14) (w8)
  let v5 : W := UInt256.mulMod (v0) (v2) (w8)
  let v6 : W := (v5) + (v4)
  let v7 : W := (w0) + (v6)
  let v8 : W := (w14) * (v3)
  let v9 : W := (v0) * (v2)
  let v10 : W := (v9) + (v8)
  let v11 : W := (v10) + (w0)
  let v12 : W := (w9) * (w5)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w7) * (w4)
  let v15 : W := (v14) + (v13)
  let v16 : W := (w2) * (w10)
  let v17 : W := (v16) + (v15)
  let v18 : W := (w12) * (w6)
  let v19 : W := (v18) + (v17)
  let v20 : W := UInt256.mulMod (w9) (w5) (w8)
  let v21 : W := (v20) + (v7)
  let v22 : W := UInt256.mulMod (w7) (w4) (w8)
  let v23 : W := (v22) + (v21)
  let v24 : W := UInt256.mulMod (w10) (w2) (w8)
  let v25 : W := (v24) + (v23)
  let v26 : W := UInt256.mulMod (w12) (w6) (w8)
  let v27 : W := (v26) + (v25)
  let v28 : W := UInt256.land (w11) (v19)
  let v29 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v28).toNat 32) 64
  let v30 : W := (v27) - (v28)
  let v31 : W := (w8) + (v30)
  let v32 : W := UInt256.mulMod (N 2048) (v31) (w8)
  have h0 : runInstructions stage13Part0Program {s with pc := N 7389, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7399, memory := s.memory, stack := (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part0Model, v0, v1, v2] using stage13Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage13Part1Program {s with pc := N 7399, memory := s.memory, stack := (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7408, memory := s.memory, stack := (v2) :: (w8) :: (v4) :: (v3) :: (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part1Model, v3, v4] using stage13Part1_run ({s with memory := s.memory}) (v2) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage13Part2Program {s with pc := N 7408, memory := s.memory, stack := (v2) :: (w8) :: (v4) :: (v3) :: (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7416, memory := s.memory, stack := (v0) :: (v2) :: (v8) :: (w0) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part2Model, v5, v6, v7, v8] using stage13Part2_run ({s with memory := s.memory}) (v2) (w8) (v4) (v3) (v2) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage13Part3Program {s with pc := N 7416, memory := s.memory, stack := (v0) :: (v2) :: (v8) :: (w0) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7424, memory := s.memory, stack := (w4) :: (v13) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part3Model, v9, v10, v11, v12, v13] using stage13Part3_run ({s with memory := s.memory}) (v0) (v2) (v8) (w0) (v7) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage13Part4Program {s with pc := N 7424, memory := s.memory, stack := (w4) :: (v13) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7432, memory := s.memory, stack := (w6) :: (v17) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part4Model, v14, v15, v16, v17] using stage13Part4_run ({s with memory := s.memory}) (w4) (v13) (v7) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage13Part5Program {s with pc := N 7432, memory := s.memory, stack := (w6) :: (v17) :: (v7) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7440, memory := s.memory, stack := (v20) :: (v7) :: (v19) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part5Model, v18, v19, v20] using stage13Part5_run ({s with memory := s.memory}) (w6) (v17) (v7) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage13Part6Program {s with pc := N 7440, memory := s.memory, stack := (v20) :: (v7) :: (v19) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7448, memory := s.memory, stack := (w2) :: (w8) :: (v23) :: (v19) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part6Model, v21, v22, v23] using stage13Part6_run ({s with memory := s.memory}) (v20) (v7) (v19) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage13Part7Program {s with pc := N 7448, memory := s.memory, stack := (w2) :: (w8) :: (v23) :: (v19) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7456, memory := s.memory, stack := (v27) :: (v19) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part7Model, v24, v25, v26, v27] using stage13Part7_run ({s with memory := s.memory}) (w2) (w8) (v23) (v19) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage13Part8Program {s with pc := N 7456, memory := s.memory, stack := (v27) :: (v19) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7465, memory := v29, stack := (v27) :: (v28) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part8Model, v28, v29] using stage13Part8_run ({s with memory := s.memory}) (v27) (v19) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage13Part9Program {s with pc := N 7465, memory := v29, stack := (v27) :: (v28) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7472, memory := v29, stack := (v32) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part9Model, v30, v31, v32] using stage13Part9_run ({s with memory := v29}) (v27) (v28) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))

def stage14Part0Program : List Instr :=
  [.push 2 832,
   .op .MLOAD,
   .op (.Swap sA5),
   .op .POP,
   .op (.Dup dA14),
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD]
def stage14Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 832
  let v1 : W := MachineState.readWord (s.memory) 128
  {s with pc := N 7483, memory := s.memory, stack := (v1) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage14Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part0Program {s with pc := N 7472, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage14Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage14Part0Program, stage14Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha832, hf832, ha128, hf128]

def stage14Part1Program : List Instr :=
  [.op (.Dup dA0),
   .op .ADD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA2)]
def stage14Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w0)
  let v1 : W := (w2) * (v0)
  let v2 : W := UInt256.mulMod (w2) (v0) (w1)
  {s with pc := N 7491, memory := s.memory, stack := (w3) :: (v2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage14Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part1Program {s with pc := N 7483, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage14Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage14Part1Program, stage14Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage14Part2Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA0),
   .op .MUL,
   .op .ADD]
def stage14Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w3) + (w2)
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := (v2) * (v2)
  let v4 : W := (v3) + (v1)
  {s with pc := N 7500, memory := s.memory, stack := (v4) :: (v0) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage14Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part2Program {s with pc := N 7491, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage14Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage14Part2Program, stage14Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage14Part3Program : List Instr :=
  [.op (.Dup dA5),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD]
def stage14Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w10) * (w5)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w8) * (w11)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7508, memory := s.memory, stack := (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage14Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part3Program {s with pc := N 7500, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage14Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage14Part3Program, stage14Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage14Part4Program : List Instr :=
  [.op (.Dup dA3),
   .op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 1 160,
   .op .MLOAD]
def stage14Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w13) * (w3)
  let v1 : W := (v0) + (w0)
  let v2 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 7517, memory := s.memory, stack := (v2) :: (w9) :: (w1) :: (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage14Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part4Program {s with pc := N 7508, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage14Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage14Part4Program, stage14Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage14Part5Program : List Instr :=
  [.op (.Dup dA0),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD]
def stage14Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w12) (w7) (w11)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7525, memory := s.memory, stack := (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage14Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part5Program {s with pc := N 7517, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage14Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage14Part5Program, stage14Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage14Part6Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA5)]
def stage14Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w8) (w11) (w9)
  let v1 : W := (v0) + (w0)
  {s with pc := N 7533, memory := s.memory, stack := (w3) :: (w13) :: (w9) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage14Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part6Program {s with pc := N 7525, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage14Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage14Part6Program, stage14Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage14Part7Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 1 96,
   .op .MSTORE]
def stage14Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.land (w15) (w4)
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v2).toNat 32) 96
  {s with pc := N 7542, memory := v3, stack := (v2) :: (v1) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage14Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part7Program {s with pc := N 7533, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage14Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage14Part7Program, stage14Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]

def stage14Part8Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage14Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w1) - (w0)
  let v1 : W := (w9) + (v0)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w9)
  {s with pc := N 7551, memory := s.memory, stack := (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage14Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part8Program {s with pc := N 7542, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage14Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage14Part8Program, stage14Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage14Program : List Instr := (stage14Part0Program ++ (stage14Part1Program ++ (stage14Part2Program ++ (stage14Part3Program ++ (stage14Part4Program ++ (stage14Part5Program ++ (stage14Part6Program ++ (stage14Part7Program ++ (stage14Part8Program)))))))))
def stage14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 832
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) + (v1)
  let v3 : W := (w14) * (v2)
  let v4 : W := UInt256.mulMod (w14) (v2) (w8)
  let v5 : W := (w0) + (v4)
  let v6 : W := (w0) + (v3)
  let v7 : W := MachineState.readWord (s.memory) 160
  let v8 : W := (v7) * (v7)
  let v9 : W := (v8) + (v6)
  let v10 : W := (w9) * (w4)
  let v11 : W := (v10) + (v9)
  let v12 : W := (w7) * (w10)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w12) * (w2)
  let v15 : W := (v14) + (v13)
  let v16 : W := MachineState.readWord (s.memory) 160
  let v17 : W := UInt256.mulMod (v16) (v16) (w8)
  let v18 : W := (v17) + (v5)
  let v19 : W := UInt256.mulMod (w9) (w4) (w8)
  let v20 : W := (v19) + (v18)
  let v21 : W := UInt256.mulMod (w7) (w10) (w8)
  let v22 : W := (v21) + (v20)
  let v23 : W := UInt256.mulMod (w2) (w12) (w8)
  let v24 : W := (v23) + (v22)
  let v25 : W := UInt256.land (w11) (v15)
  let v26 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v25).toNat 32) 96
  let v27 : W := (v24) - (v25)
  let v28 : W := (w8) + (v27)
  let v29 : W := UInt256.mulMod (N 2048) (v28) (w8)
  {s with pc := N 7551, memory := v26, stack := (v29) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Program {s with pc := N 7472, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 832
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) + (v1)
  let v3 : W := (w14) * (v2)
  let v4 : W := UInt256.mulMod (w14) (v2) (w8)
  let v5 : W := (w0) + (v4)
  let v6 : W := (w0) + (v3)
  let v7 : W := MachineState.readWord (s.memory) 160
  let v8 : W := (v7) * (v7)
  let v9 : W := (v8) + (v6)
  let v10 : W := (w9) * (w4)
  let v11 : W := (v10) + (v9)
  let v12 : W := (w7) * (w10)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w12) * (w2)
  let v15 : W := (v14) + (v13)
  let v16 : W := MachineState.readWord (s.memory) 160
  let v17 : W := UInt256.mulMod (v16) (v16) (w8)
  let v18 : W := (v17) + (v5)
  let v19 : W := UInt256.mulMod (w9) (w4) (w8)
  let v20 : W := (v19) + (v18)
  let v21 : W := UInt256.mulMod (w7) (w10) (w8)
  let v22 : W := (v21) + (v20)
  let v23 : W := UInt256.mulMod (w2) (w12) (w8)
  let v24 : W := (v23) + (v22)
  let v25 : W := UInt256.land (w11) (v15)
  let v26 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v25).toNat 32) 96
  let v27 : W := (v24) - (v25)
  let v28 : W := (w8) + (v27)
  let v29 : W := UInt256.mulMod (N 2048) (v28) (w8)
  have h0 : runInstructions stage14Part0Program {s with pc := N 7472, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7483, memory := s.memory, stack := (v1) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part0Model, v0, v1] using stage14Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage14Part1Program {s with pc := N 7483, memory := s.memory, stack := (v1) :: (w8) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7491, memory := s.memory, stack := (w0) :: (v4) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part1Model, v2, v3, v4] using stage14Part1_run ({s with memory := s.memory}) (v1) (w8) (w14) (w0) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage14Part2Program {s with pc := N 7491, memory := s.memory, stack := (w0) :: (v4) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7500, memory := s.memory, stack := (v9) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part2Model, v5, v6, v7, v8, v9] using stage14Part2_run ({s with memory := s.memory}) (w0) (v4) (v3) (w0) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage14Part3Program {s with pc := N 7500, memory := s.memory, stack := (v9) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7508, memory := s.memory, stack := (v13) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part3Model, v10, v11, v12, v13] using stage14Part3_run ({s with memory := s.memory}) (v9) (v5) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage14Part4Program {s with pc := N 7508, memory := s.memory, stack := (v13) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7517, memory := s.memory, stack := (v16) :: (w8) :: (v5) :: (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part4Model, v14, v15, v16] using stage14Part4_run ({s with memory := s.memory}) (v13) (v5) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage14Part5Program {s with pc := N 7517, memory := s.memory, stack := (v16) :: (w8) :: (v5) :: (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7525, memory := s.memory, stack := (v20) :: (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part5Model, v17, v18, v19, v20] using stage14Part5_run ({s with memory := s.memory}) (v16) (w8) (v5) (v15) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage14Part6Program {s with pc := N 7525, memory := s.memory, stack := (v20) :: (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7533, memory := s.memory, stack := (w2) :: (w12) :: (w8) :: (v22) :: (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part6Model, v21, v22] using stage14Part6_run ({s with memory := s.memory}) (v20) (v15) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage14Part7Program {s with pc := N 7533, memory := s.memory, stack := (w2) :: (w12) :: (w8) :: (v22) :: (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7542, memory := v26, stack := (v25) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part7Model, v23, v24, v25, v26] using stage14Part7_run ({s with memory := s.memory}) (w2) (w12) (w8) (v22) (v15) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage14Part8Program {s with pc := N 7542, memory := v26, stack := (v25) :: (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7551, memory := v26, stack := (v29) :: (w1) :: (w2) :: (w3) :: (w4) :: (v0) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage14Part8Model, v27, v28, v29] using stage14Part8_run ({s with memory := v26}) (v25) (v24) (w1) (w2) (w3) (w4) (v0) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

def stage15Part0Program : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op (.Swap sA4),
   .op .POP,
   .op (.Dup dA14),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA0)]
def stage15Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 800
  let v1 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 7562, memory := s.memory, stack := (v1) :: (v1) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage15Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part0Program {s with pc := N 7551, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage15Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha800 : (800 : W).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage15Part0Program, stage15Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha800, hf800, ha160, hf160]

def stage15Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .op (.Dup dA2)]
def stage15Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (w2) (v0) (w11)
  let v2 : W := (w2) * (v0)
  {s with pc := N 7570, memory := s.memory, stack := (w3) :: (v2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage15Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part1Program {s with pc := N 7562, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage15Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage15Part1Program, stage15Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage15Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA13),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op .MUL]
def stage15Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w13) * (w12)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w15) * (w10)
  {s with pc := N 7578, memory := s.memory, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage15Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part2Program {s with pc := N 7570, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage15Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage15Part2Program, stage15Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage15Part3Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA11),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD]
def stage15Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w3) + (w2)
  let v2 : W := UInt256.mulMod (w13) (w12) (w11)
  let v3 : W := (v2) + (v1)
  {s with pc := N 7586, memory := s.memory, stack := (v3) :: (v0) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage15Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part3Program {s with pc := N 7578, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage15Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage15Part3Program, stage15Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage15Part4Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND]
def stage15Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w8) (w13) (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := UInt256.land (w12) (w1)
  {s with pc := N 7594, memory := s.memory, stack := (v2) :: (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage15Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part4Program {s with pc := N 7586, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage15Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage15Part4Program, stage15Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage15Part5Program : List Instr :=
  [.op (.Dup dA0),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD]
def stage15Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (w0).toNat 32) 128
  let v1 : W := (w1) - (w0)
  let v2 : W := (w9) + (v1)
  {s with pc := N 7603, memory := v0, stack := (v2) :: (w9) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage15Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part5Program {s with pc := N 7594, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage15Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage15Part5Program, stage15Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]

def stage15Part6Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]
def stage15Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) (w0) (w1)
  {s with pc := N 7607, memory := s.memory, stack := (v0) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage15Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part6Program {s with pc := N 7603, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage15Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage15Part6Program, stage15Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage15Program : List Instr := (stage15Part0Program ++ (stage15Part1Program ++ (stage15Part2Program ++ (stage15Part3Program ++ (stage15Part4Program ++ (stage15Part5Program ++ (stage15Part6Program)))))))
def stage15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 800
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := (v1) + (v1)
  let v3 : W := UInt256.mulMod (w14) (v2) (w8)
  let v4 : W := (w14) * (v2)
  let v5 : W := (w0) + (v4)
  let v6 : W := (w10) * (w9)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w12) * (w7)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w0) + (v3)
  let v11 : W := UInt256.mulMod (w10) (w9) (w8)
  let v12 : W := (v11) + (v10)
  let v13 : W := UInt256.mulMod (w7) (w12) (w8)
  let v14 : W := (v13) + (v12)
  let v15 : W := UInt256.land (w11) (v9)
  let v16 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v15).toNat 32) 128
  let v17 : W := (v14) - (v15)
  let v18 : W := (w8) + (v17)
  let v19 : W := UInt256.mulMod (N 2048) (v18) (w8)
  {s with pc := N 7607, memory := v16, stack := (v19) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Program {s with pc := N 7551, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 800
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := (v1) + (v1)
  let v3 : W := UInt256.mulMod (w14) (v2) (w8)
  let v4 : W := (w14) * (v2)
  let v5 : W := (w0) + (v4)
  let v6 : W := (w10) * (w9)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w12) * (w7)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w0) + (v3)
  let v11 : W := UInt256.mulMod (w10) (w9) (w8)
  let v12 : W := (v11) + (v10)
  let v13 : W := UInt256.mulMod (w7) (w12) (w8)
  let v14 : W := (v13) + (v12)
  let v15 : W := UInt256.land (w11) (v9)
  let v16 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v15).toNat 32) 128
  let v17 : W := (v14) - (v15)
  let v18 : W := (w8) + (v17)
  let v19 : W := UInt256.mulMod (N 2048) (v18) (w8)
  have h0 : runInstructions stage15Part0Program {s with pc := N 7551, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7562, memory := s.memory, stack := (v1) :: (v1) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage15Part0Model, v0, v1] using stage15Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage15Part1Program {s with pc := N 7562, memory := s.memory, stack := (v1) :: (v1) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7570, memory := s.memory, stack := (w0) :: (v4) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage15Part1Model, v2, v3, v4] using stage15Part1_run ({s with memory := s.memory}) (v1) (v1) (w14) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage15Part2Program {s with pc := N 7570, memory := s.memory, stack := (w0) :: (v4) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7578, memory := s.memory, stack := (v8) :: (v7) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage15Part2Model, v5, v6, v7, v8] using stage15Part2_run ({s with memory := s.memory}) (w0) (v4) (v3) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage15Part3Program {s with pc := N 7578, memory := s.memory, stack := (v8) :: (v7) :: (v3) :: (w0) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7586, memory := s.memory, stack := (v12) :: (v9) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage15Part3Model, v9, v10, v11, v12] using stage15Part3_run ({s with memory := s.memory}) (v8) (v7) (v3) (w0) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage15Part4Program {s with pc := N 7586, memory := s.memory, stack := (v12) :: (v9) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7594, memory := s.memory, stack := (v15) :: (v14) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage15Part4Model, v13, v14, v15] using stage15Part4_run ({s with memory := s.memory}) (v12) (v9) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage15Part5Program {s with pc := N 7594, memory := s.memory, stack := (v15) :: (v14) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7603, memory := v16, stack := (v18) :: (w8) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage15Part5Model, v16, v17, v18] using stage15Part5_run ({s with memory := s.memory}) (v15) (v14) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage15Part6Program {s with pc := N 7603, memory := v16, stack := (v18) :: (w8) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7607, memory := v16, stack := (v19) :: (w1) :: (w2) :: (w3) :: (v0) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage15Part6Model, v19] using stage15Part6_run ({s with memory := v16}) (v18) (w8) (w1) (w2) (w3) (v0) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 h6))))))

def stage16Part0Program : List Instr :=
  [.op (.Swap sA9),
   .op .POP,
   .op (.Dup dA7),
   .op (.Dup dA9),
   .op (.Dup dA13),
   .op .MULMOD,
   .op (.Dup dA8),
   .op (.Dup dA15)]
def stage16Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w12) (w9) (w8)
  {s with pc := N 7615, memory := s.memory, stack := (w14) :: (w8) :: (v0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w0) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage16Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part0Program {s with pc := N 7607, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage16Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage16Part0Program, stage16Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage16Part1Program : List Instr :=
  [.op (.Dup dA0),
   .op .MULMOD,
   .op (.Dup dA11),
   .op .ADD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA13),
   .op .MUL]
def stage16Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w0) (w1)
  let v1 : W := (w12) + (v0)
  let v2 : W := (v1) + (w2)
  let v3 : W := (w14) * (w11)
  {s with pc := N 7623, memory := s.memory, stack := (v3) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage16Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part1Program {s with pc := N 7615, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage16Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage16Part1Program, stage16Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage16Part2Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA0),
   .op .MUL,
   .push 2 1376,
   .op .MLOAD,
   .op (.Swap sA12),
   .op .ADD,
   .op .ADD]
def stage16Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w15) * (w15)
  let v1 : W := MachineState.readWord (s.memory) 1376
  let v2 : W := (w11) + (v0)
  let v3 : W := (v2) + (w0)
  {s with pc := N 7633, memory := s.memory, stack := (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (v1) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage16Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part2Program {s with pc := N 7623, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage16Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1376 : (1376 : W).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage16Part2Program, stage16Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1376, hf1376]

def stage16Part3Program : List Instr :=
  [.op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 1 160,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB]
def stage16Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (w12) (w0)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v0).toNat 32) 160
  let v2 : W := (w1) - (v0)
  {s with pc := N 7642, memory := v1, stack := (v2) :: (w9) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage16Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part3Program {s with pc := N 7633, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage16Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage16Part3Program, stage16Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage16Part4Program : List Instr :=
  [.op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage16Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w1) + (w0)
  let v1 : W := UInt256.mulMod (N 2048) (v0) (w1)
  {s with pc := N 7648, memory := s.memory, stack := (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage16Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part4Program {s with pc := N 7642, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage16Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage16Part4Program, stage16Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage16Program : List Instr := (stage16Part0Program ++ (stage16Part1Program ++ (stage16Part2Program ++ (stage16Part3Program ++ (stage16Part4Program)))))
def stage16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w12) (w9) (w8)
  let v1 : W := UInt256.mulMod (w14) (w14) (w8)
  let v2 : W := (w0) + (v1)
  let v3 : W := (v2) + (v0)
  let v4 : W := (w12) * (w9)
  let v5 : W := (w14) * (w14)
  let v6 : W := MachineState.readWord (s.memory) 1376
  let v7 : W := (w0) + (v5)
  let v8 : W := (v7) + (v4)
  let v9 : W := UInt256.land (w11) (v8)
  let v10 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v9).toNat 32) 160
  let v11 : W := (v3) - (v9)
  let v12 : W := (w8) + (v11)
  let v13 : W := UInt256.mulMod (N 2048) (v12) (w8)
  {s with pc := N 7648, memory := v10, stack := (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v6) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Program {s with pc := N 7607, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := UInt256.mulMod (w12) (w9) (w8)
  let v1 : W := UInt256.mulMod (w14) (w14) (w8)
  let v2 : W := (w0) + (v1)
  let v3 : W := (v2) + (v0)
  let v4 : W := (w12) * (w9)
  let v5 : W := (w14) * (w14)
  let v6 : W := MachineState.readWord (s.memory) 1376
  let v7 : W := (w0) + (v5)
  let v8 : W := (v7) + (v4)
  let v9 : W := UInt256.land (w11) (v8)
  let v10 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v9).toNat 32) 160
  let v11 : W := (v3) - (v9)
  let v12 : W := (w8) + (v11)
  let v13 : W := UInt256.mulMod (N 2048) (v12) (w8)
  have h0 : runInstructions stage16Part0Program {s with pc := N 7607, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7615, memory := s.memory, stack := (w14) :: (w8) :: (v0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w0) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage16Part0Model, v0] using stage16Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage16Part1Program {s with pc := N 7615, memory := s.memory, stack := (w14) :: (w8) :: (v0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w0) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7623, memory := s.memory, stack := (v4) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w0) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage16Part1Model, v1, v2, v3, v4] using stage16Part1_run ({s with memory := s.memory}) (w14) (w8) (v0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w0) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage16Part2Program {s with pc := N 7623, memory := s.memory, stack := (v4) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w0) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7633, memory := s.memory, stack := (v8) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v6) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage16Part2Model, v5, v6, v7, v8] using stage16Part2_run ({s with memory := s.memory}) (v4) (v3) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w0) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage16Part3Program {s with pc := N 7633, memory := s.memory, stack := (v8) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v6) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7642, memory := v10, stack := (v11) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v6) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage16Part3Model, v9, v10, v11] using stage16Part3_run ({s with memory := s.memory}) (v8) (v3) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (v6) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage16Part4Program {s with pc := N 7642, memory := v10, stack := (v11) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v6) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7648, memory := v10, stack := (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v6) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage16Part4Model, v12, v13] using stage16Part4_run ({s with memory := v10}) (v11) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (v6) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))

def stage17Part0Program : List Instr :=
  [.op (.Swap sA13),
   .op .POP,
   .push 3 1344,
   .op .MLOAD,
   .op (.Swap sA11),
   .op .POP]
def stage17Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1344
  {s with pc := N 7657, memory := s.memory, stack := (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (v0) :: (w13) :: (w0) :: rest}
theorem stage17Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage17Part0Program {s with pc := N 7648, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage17Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1344 : (1344 : W).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage17Part0Program, stage17Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1344, hf1344]

def stage17Program : List Instr := (stage17Part0Program)
def stage17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1344
  {s with pc := N 7657, memory := s.memory, stack := (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (v0) :: (w13) :: (w0) :: rest}
theorem stage17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage17Program {s with pc := N 7648, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1344
  have h0 : runInstructions stage17Part0Program {s with pc := N 7648, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7657, memory := s.memory, stack := (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (v0) :: (w13) :: (w0) :: rest} := by
    simpa only [stage17Part0Model, v0] using stage17Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact h0

end R9InvCompactExec

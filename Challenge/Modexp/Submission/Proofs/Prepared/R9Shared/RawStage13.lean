import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.RawPrelude
open CycleSubmission.SharedStackArgs
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace R9InvConsumeExec
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open CycleSubmission.Prepared.Arithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

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
  {s with pc := N 7285, memory := s.memory, stack := (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}

theorem stage13Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part0Program {s with pc := N 7275, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage13Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage13Part0Program, stage13Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha160, hf160]

def stage13Part1Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op (.Dup dA2),
   .op .MULMOD,
   .op (.Dup dA13),
   .op (.Dup dA3)]
def stage13Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w14) (w3) (w11)
  {s with pc := N 7292, memory := s.memory, stack := (w0) :: (w11) :: (v0) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}

theorem stage13Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part1Program {s with pc := N 7285, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage13Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part1Program, stage13Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

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
  {s with pc := N 7300, memory := s.memory, stack := (w5) :: (w4) :: (v3) :: (w6) :: (v2) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: rest}

theorem stage13Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part2Program {s with pc := N 7292, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: (w21) :: rest} = some (stage13Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
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
  {s with pc := N 7308, memory := s.memory, stack := (w8) :: (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}

theorem stage13Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part3Program {s with pc := N 7300, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} = some (stage13Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
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
  {s with pc := N 7316, memory := s.memory, stack := (w8) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}

theorem stage13Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part4Program {s with pc := N 7308, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
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
  {s with pc := N 7324, memory := s.memory, stack := (v2) :: (w2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}

theorem stage13Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part5Program {s with pc := N 7316, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
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
  {s with pc := N 7332, memory := s.memory, stack := (w4) :: (w10) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}

theorem stage13Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part6Program {s with pc := N 7324, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
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
  {s with pc := N 7340, memory := s.memory, stack := (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}

theorem stage13Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part7Program {s with pc := N 7332, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} = some (stage13Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part7Program, stage13Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Part8Program : List Instr :=
  [.op (.Swap sA0),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .push 1 64,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1)]
def stage13Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (w1)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v0).toNat 32) 64
  {s with pc := N 7379, memory := v1, stack := (w0) :: (v0) :: (w9) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}

theorem stage13Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part8Program {s with pc := N 7340, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage13Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
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
  {s with pc := N 7386, memory := s.memory, stack := (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}

theorem stage13Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part9Program {s with pc := N 7379, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage13Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage13Part9Program, stage13Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage13Program : List Instr := (stage13Part0Program ++ (stage13Part1Program ++ (stage13Part2Program ++ (stage13Part3Program ++ (stage13Part4Program ++ (stage13Part5Program ++ (stage13Part6Program ++ (stage13Part7Program ++ (stage13Part8Program ++ stage13Part9Program)))))))))
def stage13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) + (v1)
  let v3 : W := UInt256.mulMod (w11) (w14) (w8)
  let v4 : W := UInt256.mulMod (v0) (v2) (w8)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w0) + (v5)
  let v7 : W := (w14) * (w11)
  let v8 : W := (v0) * (v2)
  let v9 : W := (v8) + (v7)
  let v10 : W := (v9) + (w0)
  let v11 : W := (w9) * (w5)
  let v12 : W := (v11) + (v10)
  let v13 : W := (w7) * (w4)
  let v14 : W := (v13) + (v12)
  let v15 : W := (w2) * (w10)
  let v16 : W := (v15) + (v14)
  let v17 : W := (w12) * (w6)
  let v18 : W := (v17) + (v16)
  let v19 : W := UInt256.mulMod (w9) (w5) (w8)
  let v20 : W := (v19) + (v6)
  let v21 : W := UInt256.mulMod (w7) (w4) (w8)
  let v22 : W := (v21) + (v20)
  let v23 : W := UInt256.mulMod (w10) (w2) (w8)
  let v24 : W := (v23) + (v22)
  let v25 : W := UInt256.mulMod (w12) (w6) (w8)
  let v26 : W := (v25) + (v24)
  let v27 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v18)
  let v28 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v27).toNat 32) 64
  let v29 : W := (v26) - (v27)
  let v30 : W := (w8) + (v29)
  let v31 : W := UInt256.mulMod (N 2048) (v30) (w8)
  {s with pc := N 7386, memory := v28, stack := (v31) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}

theorem stage13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Program {s with pc := N 7275, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := (v1) + (v1)
  let v3 : W := UInt256.mulMod (w11) (w14) (w8)
  let v4 : W := UInt256.mulMod (v0) (v2) (w8)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w0) + (v5)
  let v7 : W := (w14) * (w11)
  let v8 : W := (v0) * (v2)
  let v9 : W := (v8) + (v7)
  let v10 : W := (v9) + (w0)
  let v11 : W := (w9) * (w5)
  let v12 : W := (v11) + (v10)
  let v13 : W := (w7) * (w4)
  let v14 : W := (v13) + (v12)
  let v15 : W := (w2) * (w10)
  let v16 : W := (v15) + (v14)
  let v17 : W := (w12) * (w6)
  let v18 : W := (v17) + (v16)
  let v19 : W := UInt256.mulMod (w9) (w5) (w8)
  let v20 : W := (v19) + (v6)
  let v21 : W := UInt256.mulMod (w7) (w4) (w8)
  let v22 : W := (v21) + (v20)
  let v23 : W := UInt256.mulMod (w10) (w2) (w8)
  let v24 : W := (v23) + (v22)
  let v25 : W := UInt256.mulMod (w12) (w6) (w8)
  let v26 : W := (v25) + (v24)
  let v27 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v18)
  let v28 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (v27).toNat 32) 64
  let v29 : W := (v26) - (v27)
  let v30 : W := (w8) + (v29)
  let v31 : W := UInt256.mulMod (N 2048) (v30) (w8)
  have h0 : runInstructions stage13Part0Program {s with pc := N 7275, memory := s.memory, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7285, memory := s.memory, stack := (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part0Model, v0, v1, v2] using stage13Part0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage13Part1Program {s with pc := N 7285, memory := s.memory, stack := (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7292, memory := s.memory, stack := (v2) :: (w8) :: (v3) :: (w11) :: (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part1Model, v3] using stage13Part1_run ({s with memory := s.memory}) (v2) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage13Part2Program {s with pc := N 7292, memory := s.memory, stack := (v2) :: (w8) :: (v3) :: (w11) :: (v2) :: (v0) :: (w0) :: (w14) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7300, memory := s.memory, stack := (v0) :: (v2) :: (v7) :: (w0) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part2Model, v4, v5, v6, v7] using stage13Part2_run ({s with memory := s.memory}) (v2) (w8) (v3) (w11) (v2) (v0) (w0) (w14) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage13Part3Program {s with pc := N 7300, memory := s.memory, stack := (v0) :: (v2) :: (v7) :: (w0) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7308, memory := s.memory, stack := (w4) :: (v12) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part3Model, v8, v9, v10, v11, v12] using stage13Part3_run ({s with memory := s.memory}) (v0) (v2) (v7) (w0) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage13Part4Program {s with pc := N 7308, memory := s.memory, stack := (w4) :: (v12) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7316, memory := s.memory, stack := (w6) :: (v16) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part4Model, v13, v14, v15, v16] using stage13Part4_run ({s with memory := s.memory}) (w4) (v12) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage13Part5Program {s with pc := N 7316, memory := s.memory, stack := (w6) :: (v16) :: (v6) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7324, memory := s.memory, stack := (v19) :: (v6) :: (v18) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part5Model, v17, v18, v19] using stage13Part5_run ({s with memory := s.memory}) (w6) (v16) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage13Part6Program {s with pc := N 7324, memory := s.memory, stack := (v19) :: (v6) :: (v18) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7332, memory := s.memory, stack := (w2) :: (w8) :: (v22) :: (v18) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part6Model, v20, v21, v22] using stage13Part6_run ({s with memory := s.memory}) (v19) (v6) (v18) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions stage13Part7Program {s with pc := N 7332, memory := s.memory, stack := (w2) :: (w8) :: (v22) :: (v18) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7340, memory := s.memory, stack := (v26) :: (v18) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part7Model, v23, v24, v25, v26] using stage13Part7_run ({s with memory := s.memory}) (w2) (w8) (v22) (v18) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions stage13Part8Program {s with pc := N 7340, memory := s.memory, stack := (v26) :: (v18) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7379, memory := v28, stack := (v26) :: (v27) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part8Model, v27, v28] using stage13Part8_run ({s with memory := s.memory}) (v26) (v18) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions stage13Part9Program {s with pc := N 7379, memory := v28, stack := (v26) :: (v27) :: (w8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 7386, memory := v28, stack := (v31) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage13Part9Model, v29, v30, v31] using stage13Part9_run ({s with memory := v28}) (v26) (v27) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))

end R9InvConsumeExec

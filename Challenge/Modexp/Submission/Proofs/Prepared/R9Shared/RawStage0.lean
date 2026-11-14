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

def stage0Part0Program : List Instr :=
  [
  .push 2 768,
   .op .MLOAD,
   .op (.Dup dA8),
   .op (.Dup dA1)]
def stage0Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  {s with pc := N 3499, memory := s.memory, stack := v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest}

theorem stage0Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part0Program {s with pc := N 3493, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some (stage0Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage0Part0Program, stage0Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]

def stage0Part1Program : List Instr :=
  [
  .op (.Dup dA0),
   .op (.Dup dA0),
   .op .MUL,
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap sA11)]
def stage0Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 * w0
  let v1 : W := MachineState.readWord (s.memory) 2720
  let v2 : W := v1 * v0
  let v3 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v2
  {s with pc := N 3540, memory := s.memory, stack := w11 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v3 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage0Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part1Program {s with pc := N 3499, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage0Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage0Part1Program, stage0Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]

def stage0Part2Program : List Instr :=
  [
  .op .POP,
   .op (.Dup dA10),
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA1),
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MULMOD]
def stage0Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w3 w1 w2
  let v1 : W := UInt256.mulMod w15 w12 w11
  {s with pc := N 3548, memory := s.memory, stack := v1 :: v0 :: w11 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem stage0Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part2Program {s with pc := N 3540, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some (stage0Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage0Part2Program, stage0Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage0Part3Program : List Instr :=
  [
  .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage0Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod (N 2048) v0 w2
  {s with pc := N 3553, memory := s.memory, stack := v1 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage0Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part3Program {s with pc := N 3548, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage0Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage0Part3Program, stage0Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage0Program : List Instr := (stage0Part0Program ++ (stage0Part1Program ++ (stage0Part2Program ++ stage0Part3Program)))
def stage0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  {s with pc := N 3553, memory := s.memory, stack := v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest}

theorem stage0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Program {s with pc := N 3493, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some (stage0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  have h0 : runInstructions stage0Part0Program {s with pc := N 3493, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 3499, memory := s.memory, stack := v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [stage0Part0Model, v0] using stage0Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h1 : runInstructions stage0Part1Program {s with pc := N 3499, memory := s.memory, stack := v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 3540, memory := s.memory, stack := w8 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [stage0Part1Model, v1, v2, v3, v4] using stage0Part1_run ({s with memory := s.memory}) v0 w7 v0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h2 : runInstructions stage0Part2Program {s with pc := N 3540, memory := s.memory, stack := w8 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 3548, memory := s.memory, stack := v6 :: v5 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [stage0Part2Model, v5, v6] using stage0Part2_run ({s with memory := s.memory}) w8 v0 w7 v0 w0 w1 w2 w3 w4 w5 w6 w7 v4 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h3 : runInstructions stage0Part3Program {s with pc := N 3548, memory := s.memory, stack := v6 :: v5 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 3553, memory := s.memory, stack := v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [stage0Part3Model, v7, v8] using stage0Part3_run ({s with memory := s.memory}) v6 v5 w7 w0 w1 w2 w3 w4 w5 w6 w7 v4 w9 w10 w11 w12 w13 w14 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 h3)))

end R9InvConsumeExec

import Challenge.Modexp.Submission.Proofs.CRT.LifetimeCache
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace HistoricalSearch.GeneratedColumns
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.LifetimeCache Challenge.EvmProof.Memory

def col3part0Program : List Instr :=
  [.push 2 864,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def col3part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 864
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  {s with pc := UInt256.ofNat 6033, memory := s.memory, stack := v2 :: v1 :: x1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem col3part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part0Program {s with pc := UInt256.ofNat 6021, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (col3part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha864 : (864 : UInt256).toNat = 864 := rfl
  have hf864 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 864 32 (by decide) (by norm_num) hact
  simp [col3part0Program, col3part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha768, hf768, ha864, hf864]

#print axioms col3part0_run

def col3part1Program : List Instr :=
  [.push 2 832,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def col3part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 832
  let v1 : UInt256 := MachineState.readWord s.memory 800
  let v2 : UInt256 := v1 * v0
  let v3 : UInt256 := v2 + x0
  let v4 : UInt256 := v3 + v3
  {s with pc := UInt256.ofNat 6045, memory := s.memory, stack := v4 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col3part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part1Program {s with pc := UInt256.ofNat 6033, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col3part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [col3part1Program, col3part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha800, hf800, ha832, hf832]

#print axioms col3part1_run

def col3part2Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 832,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MULMOD]

def col3part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x1 x2
  let v1 : UInt256 := MachineState.readWord s.memory 832
  let v2 : UInt256 := MachineState.readWord s.memory 800
  let v3 : UInt256 := UInt256.mulMod v2 v1 x5
  {s with pc := UInt256.ofNat 6057, memory := s.memory, stack := v3 :: v0 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col3part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part2Program {s with pc := UInt256.ofNat 6045, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col3part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [col3part2Program, col3part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha800, hf800, ha832, hf832]

#print axioms col3part2_run

def col3part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩)]

def col3part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := x3 + v1
  let v3 : UInt256 := x3 + x2
  {s with pc := UInt256.ofNat 6065, memory := s.memory, stack := x13 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col3part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part3Program {s with pc := UInt256.ofNat 6057, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col3part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  simp [col3part3Program, col3part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

#print axioms col3part3_run

def col3part4Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def col3part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x7 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  let v3 : UInt256 := x6 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6075, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col3part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part4Program {s with pc := UInt256.ofNat 6065, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col3part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [col3part4Program, col3part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1088, hf1088]

#print axioms col3part4_run

def col3part5Program : List Instr :=
  [.push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def col3part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1120
  let v1 : UInt256 := x4 * v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 6085, memory := s.memory, stack := x11 :: x2 :: x1 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col3part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part5Program {s with pc := UInt256.ofNat 6075, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col3part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have ha1120 : (1120 : UInt256).toNat = 1120 := rfl
  have hf1120 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1120 32 (by decide) (by norm_num) hact
  simp [col3part5Program, col3part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1120, hf1120]

#print axioms col3part5_run

def col3part6Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD]

def col3part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  let v3 : UInt256 := UInt256.mulMod x7 v2 x4
  {s with pc := UInt256.ofNat 6095, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col3part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part6Program {s with pc := UInt256.ofNat 6085, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col3part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [col3part6Program, col3part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1088, hf1088]

#print axioms col3part6_run

def col3part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def col3part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1120
  let v2 : UInt256 := UInt256.mulMod x5 v1 x3
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 6105, memory := s.memory, stack := x3 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col3part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part7Program {s with pc := UInt256.ofNat 6095, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col3part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have ha1120 : (1120 : UInt256).toNat = 1120 := rfl
  have hf1120 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1120 32 (by decide) (by norm_num) hact
  simp [col3part7Program, col3part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1120, hf1120]

#print axioms col3part7_run

def col3part8Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def col3part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x14
  let v1 : UInt256 := UInt256.land x13 v0
  {s with pc := UInt256.ofNat 6113, memory := s.memory, stack := v1 :: v1 :: x4 :: x0 :: x1 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col3part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part8Program {s with pc := UInt256.ofNat 6105, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col3part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  simp [col3part8Program, col3part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

#print axioms col3part8_run

def col3part9Program : List Instr :=
  [.push 2 1152,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 1 128,
   .op .MULMOD]

def col3part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1152
  let v1 : UInt256 := UInt256.mulMod x1 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v2 x5
  {s with pc := UInt256.ofNat 6122, memory := v0, stack := v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem col3part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3part9Program {s with pc := UInt256.ofNat 6113, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (col3part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have ha1152 : (1152 : UInt256).toNat = 1152 := rfl
  have hf1152 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1152 32 (by decide) (by norm_num) hact
  simp [col3part9Program, col3part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha1152, hf1152]

#print axioms col3part9_run

def col3Program : List Instr :=
  [.push 2 864,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 2 832,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 832,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1152,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 1 128,
   .op .MULMOD]

def col3RawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 864
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 832
  let v4 : UInt256 := MachineState.readWord s.memory 800
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod v0 v1 P
  let v9 : UInt256 := MachineState.readWord s.memory 832
  let v10 : UInt256 := MachineState.readWord s.memory 800
  let v11 : UInt256 := UInt256.mulMod v10 v9 P
  let v12 : UInt256 := v11 + v8
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v7
  let v16 : UInt256 := n3 * n8
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := MachineState.readWord s.memory 1088
  let v19 : UInt256 := n2 * v18
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := MachineState.readWord s.memory 1120
  let v22 : UInt256 := n1 * v21
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := UInt256.mulMod n3 n8 P
  let v25 : UInt256 := v24 + v14
  let v26 : UInt256 := MachineState.readWord s.memory 1088
  let v27 : UInt256 := UInt256.mulMod n2 v26 P
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 1120
  let v30 : UInt256 := UInt256.mulMod n1 v29 P
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := v23 * minv
  let v33 : UInt256 := UInt256.land mask v32
  let v34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v33.toNat 32) 1152
  let v35 : UInt256 := UInt256.mulMod v33 n0 P
  let v36 : UInt256 := v35 + v31
  let v37 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v36 P
  {s with pc := UInt256.ofNat 6122, memory := v34, stack := v37 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col3_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col3Program {s with pc := UInt256.ofNat 6021, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col3RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 864
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 832
  let v4 : UInt256 := MachineState.readWord s.memory 800
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod v0 v1 P
  let v9 : UInt256 := MachineState.readWord s.memory 832
  let v10 : UInt256 := MachineState.readWord s.memory 800
  let v11 : UInt256 := UInt256.mulMod v10 v9 P
  let v12 : UInt256 := v11 + v8
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v7
  let v16 : UInt256 := n3 * n8
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := MachineState.readWord s.memory 1088
  let v19 : UInt256 := n2 * v18
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := MachineState.readWord s.memory 1120
  let v22 : UInt256 := n1 * v21
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := UInt256.mulMod n3 n8 P
  let v25 : UInt256 := v24 + v14
  let v26 : UInt256 := MachineState.readWord s.memory 1088
  let v27 : UInt256 := UInt256.mulMod n2 v26 P
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 1120
  let v30 : UInt256 := UInt256.mulMod n1 v29 P
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := v23 * minv
  let v33 : UInt256 := UInt256.land mask v32
  let v34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v33.toNat 32) 1152
  let v35 : UInt256 := UInt256.mulMod v33 n0 P
  let v36 : UInt256 := v35 + v31
  let v37 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v36 P
  have h0 : runInstructions col3part0Program {s with pc := UInt256.ofNat 6021, memory := s.memory, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6033, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part0Model, v0, v1, v2] using col3part0_run (s) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col3part1Program {s with pc := UInt256.ofNat 6033, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6045, memory := s.memory, stack := v7 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part1Model, v3, v4, v5, v6, v7] using col3part1_run (s) (v2) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h2 : runInstructions col3part2Program {s with pc := UInt256.ofNat 6045, memory := s.memory, stack := v7 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6057, memory := s.memory, stack := v11 :: v8 :: v7 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part2Model, v8, v9, v10, v11] using col3part2_run (s) (v7) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h3 : runInstructions col3part3Program {s with pc := UInt256.ofNat 6057, memory := s.memory, stack := v11 :: v8 :: v7 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6065, memory := s.memory, stack := n8 :: v15 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part3Model, v12, v13, v14, v15] using col3part3_run (s) (v11) (v8) (v7) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h4 : runInstructions col3part4Program {s with pc := UInt256.ofNat 6065, memory := s.memory, stack := n8 :: v15 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6075, memory := s.memory, stack := v20 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part4Model, v16, v17, v18, v19, v20] using col3part4_run (s) (n8) (v15) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h5 : runInstructions col3part5Program {s with pc := UInt256.ofNat 6075, memory := s.memory, stack := v20 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6085, memory := s.memory, stack := n8 :: P :: v14 :: v23 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part5Model, v21, v22, v23] using col3part5_run (s) (v20) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h6 : runInstructions col3part6Program {s with pc := UInt256.ofNat 6085, memory := s.memory, stack := n8 :: P :: v14 :: v23 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6095, memory := s.memory, stack := v27 :: v25 :: v23 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part6Model, v24, v25, v26, v27] using col3part6_run (s) (n8) (P) (v14) (v23) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h7 : runInstructions col3part7Program {s with pc := UInt256.ofNat 6095, memory := s.memory, stack := v27 :: v25 :: v23 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6105, memory := s.memory, stack := P :: v31 :: v23 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part7Model, v28, v29, v30, v31] using col3part7_run (s) (v27) (v25) (v23) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h8 : runInstructions col3part8Program {s with pc := UInt256.ofNat 6105, memory := s.memory, stack := P :: v31 :: v23 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6113, memory := s.memory, stack := v33 :: v33 :: n0 :: P :: v31 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part8Model, v32, v33] using col3part8_run (s) (P) (v31) (v23) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h9 : runInstructions col3part9Program {s with pc := UInt256.ofNat 6113, memory := s.memory, stack := v33 :: v33 :: n0 :: P :: v31 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6122, memory := v34, stack := v37 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col3part9Model, v34, v35, v36, v37] using col3part9_run (s) (v33) (v33) (n0) (P) (v31) (P) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))

#print axioms col3_raw_run

def col3Model (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 864
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := MachineState.readWord s.memory 832
  let v5 : UInt256 := MachineState.readWord s.memory 800
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 832
  let v9 : UInt256 := MachineState.readWord s.memory 800
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v7 + v7
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v12
  let v16 : UInt256 := MachineState.readWord s.memory 1056
  let v17 : UInt256 := UInt256.mulMod n3 v16 P
  let v18 : UInt256 := v17 + v14
  let v19 : UInt256 := MachineState.readWord s.memory 1088
  let v20 : UInt256 := UInt256.mulMod n2 v19 P
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 1120
  let v23 : UInt256 := UInt256.mulMod n1 v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := MachineState.readWord s.memory 1056
  let v26 : UInt256 := n3 * v25
  let v27 : UInt256 := v26 + v15
  let v28 : UInt256 := MachineState.readWord s.memory 1088
  let v29 : UInt256 := n2 * v28
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := MachineState.readWord s.memory 1120
  let v32 : UInt256 := n1 * v31
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := UInt256.land mask v33
  let v35 : UInt256 := minv * v34
  let v36 : UInt256 := UInt256.land mask v35
  let v37 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v36.toNat 32) 1152
  let v38 : UInt256 := n0 * v36
  let v39 : UInt256 := v38 + v33
  let v40 : UInt256 := UInt256.mulMod n0 v36 P
  let v41 : UInt256 := v40 + v24
  let v49 : UInt256 := UInt256.mulMod v41 (UInt256.ofNat 128) P
  {s with pc := UInt256.ofNat 6122, memory := v37, stack := v49 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col3_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1)) :
    runInstructions col3Program (cachedState 3
      {s with pc := UInt256.ofNat 6021, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 4 (col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  change runInstructions col3Program
    {s with pc := UInt256.ofNat 6021, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: (MachineState.readWord s.memory 1056) :: mask :: minv :: rest} = _
  rw [col3_raw_run s carry P n0 n1 n2 n3 n4 n5 n6 n7 (MachineState.readWord s.memory 1056) mask minv rest hcap hact]
  apply congrArg some
  subst mask
  simp only [col3RawModel, col3Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint]

#print axioms col3_run

theorem col3_read0 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col3Model, read_store_disjoint]

theorem col3_read224 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col3Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

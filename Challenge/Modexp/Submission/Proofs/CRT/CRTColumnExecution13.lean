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

def col13part0Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 928,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def col13part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 928
  let v2 : UInt256 := v0 * v1
  {s with pc := UInt256.ofNat 7829, memory := s.memory, stack := v2 :: v1 :: x1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem col13part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part0Program {s with pc := UInt256.ofNat 7817, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (col13part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
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
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  simp [col13part0Program, col13part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha928, hf928, ha1024, hf1024]

#print axioms col13part0_run

def col13part1Program : List Instr :=
  [.push 2 992,
   .op .MLOAD,
   .push 2 960,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def col13part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 992
  let v1 : UInt256 := MachineState.readWord s.memory 960
  let v2 : UInt256 := v1 * v0
  let v3 : UInt256 := v2 + x0
  let v4 : UInt256 := v3 + v3
  {s with pc := UInt256.ofNat 7841, memory := s.memory, stack := v4 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col13part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part1Program {s with pc := UInt256.ofNat 7829, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col13part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col13part1Program, col13part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha960, hf960, ha992, hf992]

#print axioms col13part1_run

def col13part2Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 992,
   .op .MLOAD,
   .push 2 960,
   .op .MLOAD,
   .op .MULMOD]

def col13part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x1 x2
  let v1 : UInt256 := MachineState.readWord s.memory 992
  let v2 : UInt256 := MachineState.readWord s.memory 960
  let v3 : UInt256 := UInt256.mulMod v2 v1 x5
  {s with pc := UInt256.ofNat 7853, memory := s.memory, stack := v3 :: v0 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col13part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part2Program {s with pc := UInt256.ofNat 7841, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col13part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col13part2Program, col13part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha960, hf960, ha992, hf992]

#print axioms col13part2_run

def col13part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 1216,
   .op .MLOAD]

def col13part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := x3 + v1
  let v3 : UInt256 := x3 + x2
  let v4 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 7864, memory := s.memory, stack := v4 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col13part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part3Program {s with pc := UInt256.ofNat 7853, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col13part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [col13part3Program, col13part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1216, hf1216]

#print axioms col13part3_run

def col13part4Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def col13part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x12 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1248
  let v3 : UInt256 := x11 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7874, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col13part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part4Program {s with pc := UInt256.ofNat 7864, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col13part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [col13part4Program, col13part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1248, hf1248]

#print axioms col13part4_run

def col13part5Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL]

def col13part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1280
  let v1 : UInt256 := x9 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := x8 * x3
  {s with pc := UInt256.ofNat 7884, memory := s.memory, stack := v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col13part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part5Program {s with pc := UInt256.ofNat 7874, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col13part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [col13part5Program, col13part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1280, hf1280]

#print axioms col13part5_run

def col13part6Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def col13part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1216
  let v2 : UInt256 := UInt256.mulMod x12 v1 x3
  let v3 : UInt256 := v2 + x2
  {s with pc := UInt256.ofNat 7894, memory := s.memory, stack := v3 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col13part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part6Program {s with pc := UInt256.ofNat 7884, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col13part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [col13part6Program, col13part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1216, hf1216]

#print axioms col13part6_run

def col13part7Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1280,
   .op .MLOAD]

def col13part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1248
  let v1 : UInt256 := UInt256.mulMod x10 v0 x2
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 1280
  {s with pc := UInt256.ofNat 7907, memory := s.memory, stack := v3 :: x2 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col13part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part7Program {s with pc := UInt256.ofNat 7894, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col13part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [col13part7Program, col13part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1248, hf1248, ha1280, hf1280]

#print axioms col13part7_run

def col13part8Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def col13part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x10 x5 x4
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7915, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col13part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part8Program {s with pc := UInt256.ofNat 7907, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col13part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col13part8Program, col13part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

#print axioms col13part8_run

def col13part9Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩)]

def col13part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot x1
  let v1 : UInt256 := UInt256.addMod x0 v0 x2
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 5)
  {s with pc := UInt256.ofNat 7924, memory := s.memory, stack := x1 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col13part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part9Program {s with pc := UInt256.ofNat 7915, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col13part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  simp [col13part9Program, col13part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

#print axioms col13part9_run

def col13part10Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 2 1504,
   .op .MSTORE,
   .push 1 12,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 244]

def col13part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x13 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1504
  let v2 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 12)
  {s with pc := UInt256.ofNat 7936, memory := v1, stack := (UInt256.ofNat 244) :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col13part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part10Program {s with pc := UInt256.ofNat 7924, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col13part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1504 : (1504 : UInt256).toNat = 1504 := rfl
  have hf1504 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1504 32 (by decide) (by norm_num) hact
  simp [col13part10Program, col13part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1504, hf1504]

#print axioms col13part10_run

def col13part11Program : List Instr :=
  [.op .SHR,
   .op .ADD]

def col13part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x1 x0
  let v1 : UInt256 := v0 + x2
  {s with pc := UInt256.ofNat 7938, memory := s.memory, stack := v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col13part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13part11Program {s with pc := UInt256.ofNat 7936, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col13part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col13part11Program, col13part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

#print axioms col13part11_run

def col13Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 928,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 2 992,
   .op .MLOAD,
   .push 2 960,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 992,
   .op .MLOAD,
   .push 2 960,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 2 1504,
   .op .MSTORE,
   .push 1 12,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 244,
   .op .SHR,
   .op .ADD]

def col13RawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 928
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 992
  let v4 : UInt256 := MachineState.readWord s.memory 960
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod v0 v1 P
  let v9 : UInt256 := MachineState.readWord s.memory 992
  let v10 : UInt256 := MachineState.readWord s.memory 960
  let v11 : UInt256 := UInt256.mulMod v10 v9 P
  let v12 : UInt256 := v11 + v8
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v7
  let v16 : UInt256 := MachineState.readWord s.memory 1216
  let v17 : UInt256 := n8 * v16
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := MachineState.readWord s.memory 1248
  let v20 : UInt256 := n7 * v19
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 1280
  let v23 : UInt256 := n6 * v22
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := n5 * n0
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := MachineState.readWord s.memory 1216
  let v28 : UInt256 := UInt256.mulMod n8 v27 P
  let v29 : UInt256 := v28 + v14
  let v30 : UInt256 := MachineState.readWord s.memory 1248
  let v31 : UInt256 := UInt256.mulMod n7 v30 P
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 1280
  let v34 : UInt256 := UInt256.mulMod n6 v33 P
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := UInt256.mulMod n5 n0 P
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := UInt256.lnot v26
  let v39 : UInt256 := UInt256.addMod v37 v38 P
  let v40 : UInt256 := UInt256.shiftRight v39 (UInt256.ofNat 5)
  let v41 : UInt256 := UInt256.land mask v26
  let v42 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v41.toNat 32) 1504
  let v43 : UInt256 := UInt256.shiftLeft v40 (UInt256.ofNat 12)
  let v44 : UInt256 := UInt256.shiftRight v26 (UInt256.ofNat 244)
  let v45 : UInt256 := v44 + v43
  {s with pc := UInt256.ofNat 7938, memory := v42, stack := v45 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col13_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col13Program {s with pc := UInt256.ofNat 7817, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col13RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 928
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 992
  let v4 : UInt256 := MachineState.readWord s.memory 960
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod v0 v1 P
  let v9 : UInt256 := MachineState.readWord s.memory 992
  let v10 : UInt256 := MachineState.readWord s.memory 960
  let v11 : UInt256 := UInt256.mulMod v10 v9 P
  let v12 : UInt256 := v11 + v8
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v7
  let v16 : UInt256 := MachineState.readWord s.memory 1216
  let v17 : UInt256 := n8 * v16
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := MachineState.readWord s.memory 1248
  let v20 : UInt256 := n7 * v19
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 1280
  let v23 : UInt256 := n6 * v22
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := n5 * n0
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := MachineState.readWord s.memory 1216
  let v28 : UInt256 := UInt256.mulMod n8 v27 P
  let v29 : UInt256 := v28 + v14
  let v30 : UInt256 := MachineState.readWord s.memory 1248
  let v31 : UInt256 := UInt256.mulMod n7 v30 P
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 1280
  let v34 : UInt256 := UInt256.mulMod n6 v33 P
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := UInt256.mulMod n5 n0 P
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := UInt256.lnot v26
  let v39 : UInt256 := UInt256.addMod v37 v38 P
  let v40 : UInt256 := UInt256.shiftRight v39 (UInt256.ofNat 5)
  let v41 : UInt256 := UInt256.land mask v26
  let v42 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v41.toNat 32) 1504
  let v43 : UInt256 := UInt256.shiftLeft v40 (UInt256.ofNat 12)
  let v44 : UInt256 := UInt256.shiftRight v26 (UInt256.ofNat 244)
  let v45 : UInt256 := v44 + v43
  have h0 : runInstructions col13part0Program {s with pc := UInt256.ofNat 7817, memory := s.memory, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7829, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part0Model, v0, v1, v2] using col13part0_run (s) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col13part1Program {s with pc := UInt256.ofNat 7829, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7841, memory := s.memory, stack := v7 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part1Model, v3, v4, v5, v6, v7] using col13part1_run (s) (v2) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h2 : runInstructions col13part2Program {s with pc := UInt256.ofNat 7841, memory := s.memory, stack := v7 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7853, memory := s.memory, stack := v11 :: v8 :: v7 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part2Model, v8, v9, v10, v11] using col13part2_run (s) (v7) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h3 : runInstructions col13part3Program {s with pc := UInt256.ofNat 7853, memory := s.memory, stack := v11 :: v8 :: v7 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7864, memory := s.memory, stack := v16 :: v15 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part3Model, v12, v13, v14, v15, v16] using col13part3_run (s) (v11) (v8) (v7) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h4 : runInstructions col13part4Program {s with pc := UInt256.ofNat 7864, memory := s.memory, stack := v16 :: v15 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7874, memory := s.memory, stack := v21 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part4Model, v17, v18, v19, v20, v21] using col13part4_run (s) (v16) (v15) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h5 : runInstructions col13part5Program {s with pc := UInt256.ofNat 7874, memory := s.memory, stack := v21 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7884, memory := s.memory, stack := v25 :: v24 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part5Model, v22, v23, v24, v25] using col13part5_run (s) (v21) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h6 : runInstructions col13part6Program {s with pc := UInt256.ofNat 7884, memory := s.memory, stack := v25 :: v24 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7894, memory := s.memory, stack := v29 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part6Model, v26, v27, v28, v29] using col13part6_run (s) (v25) (v24) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h7 : runInstructions col13part7Program {s with pc := UInt256.ofNat 7894, memory := s.memory, stack := v29 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7907, memory := s.memory, stack := v33 :: P :: v32 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part7Model, v30, v31, v32, v33] using col13part7_run (s) (v29) (v26) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h8 : runInstructions col13part8Program {s with pc := UInt256.ofNat 7907, memory := s.memory, stack := v33 :: P :: v32 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7915, memory := s.memory, stack := v37 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part8Model, v34, v35, v36, v37] using col13part8_run (s) (v33) (P) (v32) (v26) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h9 : runInstructions col13part9Program {s with pc := UInt256.ofNat 7915, memory := s.memory, stack := v37 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7924, memory := s.memory, stack := v26 :: v40 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part9Model, v38, v39, v40] using col13part9_run (s) (v37) (v26) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h10 : runInstructions col13part10Program {s with pc := UInt256.ofNat 7924, memory := s.memory, stack := v26 :: v40 :: v26 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7936, memory := v42, stack := (UInt256.ofNat 244) :: v26 :: v43 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part10Model, v41, v42, v43] using col13part10_run (s) (v26) (v40) (v26) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h11 : runInstructions col13part11Program {s with pc := UInt256.ofNat 7936, memory := v42, stack := (UInt256.ofNat 244) :: v26 :: v43 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7938, memory := v42, stack := v45 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col13part11Model, v44, v45] using col13part11_run ({s with memory := v42}) ((UInt256.ofNat 244)) (v26) (v43) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

#print axioms col13_raw_run

def col13Model (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 928
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := MachineState.readWord s.memory 992
  let v5 : UInt256 := MachineState.readWord s.memory 960
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 992
  let v9 : UInt256 := MachineState.readWord s.memory 960
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v7 + v7
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v12
  let v16 : UInt256 := MachineState.readWord s.memory 1216
  let v17 : UInt256 := UInt256.mulMod n8 v16 P
  let v18 : UInt256 := v17 + v14
  let v19 : UInt256 := MachineState.readWord s.memory 1248
  let v20 : UInt256 := UInt256.mulMod n7 v19 P
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 1280
  let v23 : UInt256 := UInt256.mulMod n6 v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := MachineState.readWord s.memory 1312
  let v26 : UInt256 := UInt256.mulMod n5 v25 P
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := MachineState.readWord s.memory 1216
  let v29 : UInt256 := n8 * v28
  let v30 : UInt256 := v29 + v15
  let v31 : UInt256 := MachineState.readWord s.memory 1248
  let v32 : UInt256 := n7 * v31
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := MachineState.readWord s.memory 1280
  let v35 : UInt256 := n6 * v34
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := MachineState.readWord s.memory 1312
  let v38 : UInt256 := n5 * v37
  let v39 : UInt256 := v38 + v36
  let v43 : UInt256 := UInt256.addMod v27 (UInt256.lnot v39) P
  let v44 : UInt256 := UInt256.shiftRight v43 (UInt256.ofNat 5)
  let v45 : UInt256 := UInt256.land mask v39
  let v46 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v45.toNat 32) 1504
  let v47 : UInt256 := UInt256.shiftLeft v44 (UInt256.ofNat 12)
  let v48 : UInt256 := UInt256.shiftRight v39 (UInt256.ofNat 244)
  let v49 : UInt256 := v48 + v47
  {s with pc := UInt256.ofNat 7938, memory := v46, stack := v49 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col13_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1)) :
    runInstructions col13Program (cachedState 13
      {s with pc := UInt256.ofNat 7817, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 14 (col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  change runInstructions col13Program
    {s with pc := UInt256.ofNat 7817, stack := carry :: P :: (MachineState.readWord s.memory 1312) :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = _
  rw [col13_raw_run s carry P (MachineState.readWord s.memory 1312) n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap hact]
  apply congrArg some
  subst mask
  simp only [col13RawModel, col13Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint]

#print axioms col13_run

theorem col13_read0 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col13Model, read_store_disjoint]

theorem col13_read224 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col13Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

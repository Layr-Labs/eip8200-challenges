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

def col12part0Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 896,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def col12part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 896
  let v2 : UInt256 := v0 * v1
  {s with pc := UInt256.ofNat 7655, memory := s.memory, stack := v2 :: v1 :: x1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem col12part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part0Program {s with pc := UInt256.ofNat 7643, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (col12part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
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
  have ha896 : (896 : UInt256).toNat = 896 := rfl
  have hf896 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 896 32 (by decide) (by norm_num) hact
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  simp [col12part0Program, col12part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha896, hf896, ha1024, hf1024]

#print axioms col12part0_run

def col12part1Program : List Instr :=
  [.push 2 992,
   .op .MLOAD,
   .push 2 928,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def col12part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 992
  let v1 : UInt256 := MachineState.readWord s.memory 928
  let v2 : UInt256 := v1 * v0
  let v3 : UInt256 := v2 + x0
  let v4 : UInt256 := v3 + v3
  {s with pc := UInt256.ofNat 7667, memory := s.memory, stack := v4 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col12part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part1Program {s with pc := UInt256.ofNat 7655, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col12part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col12part1Program, col12part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha928, hf928, ha992, hf992]

#print axioms col12part1_run

def col12part2Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 992,
   .op .MLOAD,
   .push 2 928,
   .op .MLOAD,
   .op .MULMOD]

def col12part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x1 x2
  let v1 : UInt256 := MachineState.readWord s.memory 992
  let v2 : UInt256 := MachineState.readWord s.memory 928
  let v3 : UInt256 := UInt256.mulMod v2 v1 x5
  {s with pc := UInt256.ofNat 7679, memory := s.memory, stack := v3 :: v0 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col12part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part2Program {s with pc := UInt256.ofNat 7667, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col12part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col12part2Program, col12part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha928, hf928, ha992, hf992]

#print axioms col12part2_run

def col12part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 960,
   .op .MLOAD]

def col12part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := x3 + v1
  let v3 : UInt256 := x3 + x2
  let v4 : UInt256 := MachineState.readWord s.memory 960
  {s with pc := UInt256.ofNat 7690, memory := s.memory, stack := v4 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col12part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part3Program {s with pc := UInt256.ofNat 7679, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col12part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  simp [col12part3Program, col12part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha960, hf960]

#print axioms col12part3_run

def col12part4Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD]

def col12part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1184
  let v3 : UInt256 := x12 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7700, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col12part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part4Program {s with pc := UInt256.ofNat 7690, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col12part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1184 : (1184 : UInt256).toNat = 1184 := rfl
  have hf1184 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1184 32 (by decide) (by norm_num) hact
  simp [col12part4Program, col12part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1184, hf1184]

#print axioms col12part4_run

def col12part5Program : List Instr :=
  [.push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩)]

def col12part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1216
  let v1 : UInt256 := x10 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := rest.headD (UInt256.ofNat 0)
  {s with pc := UInt256.ofNat 7709, memory := s.memory, stack := x9 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col12part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part5Program {s with pc := UInt256.ofNat 7700, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col12part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  rcases rest with _ | ⟨slot, rest⟩
  · simp at hrest
  simp only [List.length_cons] at hcap hrest
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
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [col12part5Program, col12part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1216, hf1216, ha1248, hf1248]

#print axioms col12part5_run

def col12part6Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩)]

def col12part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x15
  let v3 : UInt256 := x10 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7716, memory := s.memory, stack := x5 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col12part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part6Program {s with pc := UInt256.ofNat 7709, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col12part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col12part6Program, col12part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1280, hf1280]

#print axioms col12part6_run

def col12part7Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 2 960,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩)]

def col12part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x8 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 960
  {s with pc := UInt256.ofNat 7726, memory := s.memory, stack := v2 :: v2 :: x3 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col12part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part7Program {s with pc := UInt256.ofNat 7716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col12part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  simp [col12part7Program, col12part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha960, hf960]

#print axioms col12part7_run

def col12part8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def col12part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 1184
  let v3 : UInt256 := UInt256.mulMod x14 v2 x5
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7736, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col12part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part8Program {s with pc := UInt256.ofNat 7726, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col12part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha1184 : (1184 : UInt256).toNat = 1184 := rfl
  have hf1184 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1184 32 (by decide) (by norm_num) hact
  simp [col12part8Program, col12part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1184, hf1184]

#print axioms col12part8_run

def col12part9Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def col12part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1216
  let v1 : UInt256 := UInt256.mulMod x10 v0 x2
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := rest.headD (UInt256.ofNat 0)
  {s with pc := UInt256.ofNat 7746, memory := s.memory, stack := v3 :: x2 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col12part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part9Program {s with pc := UInt256.ofNat 7736, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col12part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  rcases rest with _ | ⟨slot, rest⟩
  · simp at hrest
  simp only [List.length_cons] at hcap hrest
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
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [col12part9Program, col12part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha1216, hf1216, ha1248, hf1248]

#print axioms col12part9_run

def col12part10Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def col12part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x15
  let v3 : UInt256 := UInt256.mulMod x10 v2 x4
  {s with pc := UInt256.ofNat 7753, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col12part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part10Program {s with pc := UInt256.ofNat 7746, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col12part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [col12part10Program, col12part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1280, hf1280]

#print axioms col12part10_run

def col12part11Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT]

def col12part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x8 x4 x3
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := UInt256.lnot x2
  {s with pc := UInt256.ofNat 7761, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col12part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part11Program {s with pc := UInt256.ofNat 7753, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col12part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col12part11Program, col12part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

#print axioms col12part11_run

def col12part12Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND]

def col12part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.addMod x1 x0 x3
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := UInt256.land x13 x2
  {s with pc := UInt256.ofNat 7770, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col12part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part12Program {s with pc := UInt256.ofNat 7761, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col12part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col12part12Program, col12part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

#print axioms col12part12_run

def col12part13Program : List Instr :=
  [.push 2 1472,
   .op .MSTORE,
   .push 1 12,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 244,
   .op .SHR,
   .op .ADD]

def col12part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1472
  let v1 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 12)
  let v2 : UInt256 := UInt256.shiftRight x2 (UInt256.ofNat 244)
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7782, memory := v0, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col12part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12part13Program {s with pc := UInt256.ofNat 7770, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col12part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1472 : (1472 : UInt256).toNat = 1472 := rfl
  have hf1472 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1472 32 (by decide) (by norm_num) hact
  simp [col12part13Program, col12part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1472, hf1472]

#print axioms col12part13_run

def col12Program : List Instr :=
  col12part0Program ++ (col12part1Program ++ (col12part2Program ++ (col12part3Program ++ (col12part4Program ++ (col12part5Program ++ (col12part6Program ++ (col12part7Program ++ (col12part8Program ++ (col12part9Program ++ (col12part10Program ++ (col12part11Program ++ (col12part12Program ++ (col12part13Program)))))))))))))

def col12RawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 896
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 992
  let v4 : UInt256 := MachineState.readWord s.memory 928
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod v0 v1 P
  let v9 : UInt256 := MachineState.readWord s.memory 992
  let v10 : UInt256 := MachineState.readWord s.memory 928
  let v11 : UInt256 := UInt256.mulMod v10 v9 P
  let v12 : UInt256 := v11 + v8
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v7
  let v16 : UInt256 := MachineState.readWord s.memory 960
  let v17 : UInt256 := v16 * v16
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := MachineState.readWord s.memory 1184
  let v20 : UInt256 := n8 * v19
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 1216
  let v23 : UInt256 := n7 * v22
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v26 : UInt256 := n6 * v25
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := minv
  let v29 : UInt256 := n5 * v28
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := n4 * n0
  let v32 : UInt256 := v31 + v30
  let v33 : UInt256 := MachineState.readWord s.memory 960
  let v34 : UInt256 := UInt256.mulMod v33 v33 P
  let v35 : UInt256 := v34 + v14
  let v36 : UInt256 := MachineState.readWord s.memory 1184
  let v37 : UInt256 := UInt256.mulMod n8 v36 P
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := MachineState.readWord s.memory 1216
  let v40 : UInt256 := UInt256.mulMod n7 v39 P
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v43 : UInt256 := UInt256.mulMod n6 v42 P
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := minv
  let v46 : UInt256 := UInt256.mulMod n5 v45 P
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := UInt256.mulMod n4 n0 P
  let v49 : UInt256 := v48 + v47
  let v50 : UInt256 := UInt256.lnot v32
  let v51 : UInt256 := UInt256.addMod v49 v50 P
  let v52 : UInt256 := UInt256.shiftRight v51 (UInt256.ofNat 5)
  let v53 : UInt256 := UInt256.land mask v32
  let v54 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v53.toNat 32) 1472
  let v55 : UInt256 := UInt256.shiftLeft v52 (UInt256.ofNat 12)
  let v56 : UInt256 := UInt256.shiftRight v32 (UInt256.ofNat 244)
  let v57 : UInt256 := v56 + v55
  {s with pc := UInt256.ofNat 7782, memory := v54, stack := v57 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col12_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col12Program {s with pc := UInt256.ofNat 7643, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col12RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 896
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 992
  let v4 : UInt256 := MachineState.readWord s.memory 928
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod v0 v1 P
  let v9 : UInt256 := MachineState.readWord s.memory 992
  let v10 : UInt256 := MachineState.readWord s.memory 928
  let v11 : UInt256 := UInt256.mulMod v10 v9 P
  let v12 : UInt256 := v11 + v8
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v7
  let v16 : UInt256 := MachineState.readWord s.memory 960
  let v17 : UInt256 := v16 * v16
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := MachineState.readWord s.memory 1184
  let v20 : UInt256 := n8 * v19
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 1216
  let v23 : UInt256 := n7 * v22
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v26 : UInt256 := n6 * v25
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := minv
  let v29 : UInt256 := n5 * v28
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := n4 * n0
  let v32 : UInt256 := v31 + v30
  let v33 : UInt256 := MachineState.readWord s.memory 960
  let v34 : UInt256 := UInt256.mulMod v33 v33 P
  let v35 : UInt256 := v34 + v14
  let v36 : UInt256 := MachineState.readWord s.memory 1184
  let v37 : UInt256 := UInt256.mulMod n8 v36 P
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := MachineState.readWord s.memory 1216
  let v40 : UInt256 := UInt256.mulMod n7 v39 P
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v43 : UInt256 := UInt256.mulMod n6 v42 P
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := minv
  let v46 : UInt256 := UInt256.mulMod n5 v45 P
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := UInt256.mulMod n4 n0 P
  let v49 : UInt256 := v48 + v47
  let v50 : UInt256 := UInt256.lnot v32
  let v51 : UInt256 := UInt256.addMod v49 v50 P
  let v52 : UInt256 := UInt256.shiftRight v51 (UInt256.ofNat 5)
  let v53 : UInt256 := UInt256.land mask v32
  let v54 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v53.toNat 32) 1472
  let v55 : UInt256 := UInt256.shiftLeft v52 (UInt256.ofNat 12)
  let v56 : UInt256 := UInt256.shiftRight v32 (UInt256.ofNat 244)
  let v57 : UInt256 := v56 + v55
  have h0 : runInstructions col12part0Program {s with pc := UInt256.ofNat 7643, memory := s.memory, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7655, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part0Model, v0, v1, v2] using col12part0_run (s) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col12part1Program {s with pc := UInt256.ofNat 7655, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7667, memory := s.memory, stack := v7 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part1Model, v3, v4, v5, v6, v7] using col12part1_run (s) (v2) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h2 : runInstructions col12part2Program {s with pc := UInt256.ofNat 7667, memory := s.memory, stack := v7 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7679, memory := s.memory, stack := v11 :: v8 :: v7 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part2Model, v8, v9, v10, v11] using col12part2_run (s) (v7) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h3 : runInstructions col12part3Program {s with pc := UInt256.ofNat 7679, memory := s.memory, stack := v11 :: v8 :: v7 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7690, memory := s.memory, stack := v16 :: v15 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part3Model, v12, v13, v14, v15, v16] using col12part3_run (s) (v11) (v8) (v7) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h4 : runInstructions col12part4Program {s with pc := UInt256.ofNat 7690, memory := s.memory, stack := v16 :: v15 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7700, memory := s.memory, stack := v21 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part4Model, v17, v18, v19, v20, v21] using col12part4_run (s) (v16) (v15) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h5 : runInstructions col12part5Program {s with pc := UInt256.ofNat 7700, memory := s.memory, stack := v21 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7709, memory := s.memory, stack := n6 :: v25 :: v24 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part5Model, v22, v23, v24, v25] using col12part5_run (s) (v21) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hrest hact
  have h6 : runInstructions col12part6Program {s with pc := UInt256.ofNat 7709, memory := s.memory, stack := n6 :: v25 :: v24 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7716, memory := s.memory, stack := n0 :: v30 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part6Model, v26, v27, v28, v29, v30] using col12part6_run (s) (n6) (v25) (v24) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h7 : runInstructions col12part7Program {s with pc := UInt256.ofNat 7716, memory := s.memory, stack := n0 :: v30 :: v14 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7726, memory := s.memory, stack := v33 :: v33 :: P :: v14 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part7Model, v31, v32, v33] using col12part7_run (s) (n0) (v30) (v14) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h8 : runInstructions col12part8Program {s with pc := UInt256.ofNat 7726, memory := s.memory, stack := v33 :: v33 :: P :: v14 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7736, memory := s.memory, stack := v38 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part8Model, v34, v35, v36, v37, v38] using col12part8_run (s) (v33) (v33) (P) (v14) (v32) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h9 : runInstructions col12part9Program {s with pc := UInt256.ofNat 7736, memory := s.memory, stack := v38 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7746, memory := s.memory, stack := v42 :: P :: v41 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part9Model, v39, v40, v41, v42] using col12part9_run (s) (v38) (v32) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hrest hact
  have h10 : runInstructions col12part10Program {s with pc := UInt256.ofNat 7746, memory := s.memory, stack := v42 :: P :: v41 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7753, memory := s.memory, stack := v46 :: v44 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part10Model, v43, v44, v45, v46] using col12part10_run (s) (v42) (P) (v41) (v32) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h11 : runInstructions col12part11Program {s with pc := UInt256.ofNat 7753, memory := s.memory, stack := v46 :: v44 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7761, memory := s.memory, stack := v50 :: v49 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part11Model, v47, v48, v49, v50] using col12part11_run (s) (v46) (v44) (v32) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h12 : runInstructions col12part12Program {s with pc := UInt256.ofNat 7761, memory := s.memory, stack := v50 :: v49 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7770, memory := s.memory, stack := v53 :: v52 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part12Model, v51, v52, v53] using col12part12_run (s) (v50) (v49) (v32) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h13 : runInstructions col12part13Program {s with pc := UInt256.ofNat 7770, memory := s.memory, stack := v53 :: v52 :: v32 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7782, memory := v54, stack := v57 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col12part13Model, v54, v55, v56, v57] using col12part13_run (s) (v53) (v52) (v32) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms col12_raw_run

def col12Model (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 896
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := MachineState.readWord s.memory 992
  let v5 : UInt256 := MachineState.readWord s.memory 928
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 992
  let v9 : UInt256 := MachineState.readWord s.memory 928
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v7 + v7
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v12
  let v16 : UInt256 := MachineState.readWord s.memory 960
  let v17 : UInt256 := UInt256.mulMod v16 v16 P
  let v18 : UInt256 := v17 + v14
  let v19 : UInt256 := MachineState.readWord s.memory 1184
  let v20 : UInt256 := UInt256.mulMod n8 v19 P
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 1216
  let v23 : UInt256 := UInt256.mulMod n7 v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := MachineState.readWord s.memory 1248
  let v26 : UInt256 := UInt256.mulMod n6 v25 P
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := MachineState.readWord s.memory 1280
  let v29 : UInt256 := UInt256.mulMod n5 v28 P
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := MachineState.readWord s.memory 1312
  let v32 : UInt256 := UInt256.mulMod n4 v31 P
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := MachineState.readWord s.memory 960
  let v35 : UInt256 := v34 * v34
  let v36 : UInt256 := v35 + v15
  let v37 : UInt256 := MachineState.readWord s.memory 1184
  let v38 : UInt256 := n8 * v37
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := MachineState.readWord s.memory 1216
  let v41 : UInt256 := n7 * v40
  let v42 : UInt256 := v41 + v39
  let v43 : UInt256 := MachineState.readWord s.memory 1248
  let v44 : UInt256 := n6 * v43
  let v45 : UInt256 := v44 + v42
  let v46 : UInt256 := MachineState.readWord s.memory 1280
  let v47 : UInt256 := n5 * v46
  let v48 : UInt256 := v47 + v45
  let v49 : UInt256 := MachineState.readWord s.memory 1312
  let v50 : UInt256 := n4 * v49
  let v51 : UInt256 := v50 + v48
  let v55 : UInt256 := UInt256.addMod v33 (UInt256.lnot v51) P
  let v56 : UInt256 := UInt256.shiftRight v55 (UInt256.ofNat 5)
  let v57 : UInt256 := UInt256.land mask v51
  let v58 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v57.toNat 32) 1472
  let v59 : UInt256 := UInt256.shiftLeft v56 (UInt256.ofNat 12)
  let v60 : UInt256 := UInt256.shiftRight v51 (UInt256.ofNat 244)
  let v61 : UInt256 := v60 + v59
  {s with pc := UInt256.ofNat 7782, memory := v58, stack := v61 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col12_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1)) :
    runInstructions col12Program (cachedState 12
      {s with pc := UInt256.ofNat 7643, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 13 (col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  rcases rest with _ | ⟨slot, rest⟩
  · simp at hrest
  simp only [List.length_cons] at hcap hrest
  change runInstructions col12Program
    {s with pc := UInt256.ofNat 7643, stack := carry :: P :: (MachineState.readWord s.memory 1312) :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: (MachineState.readWord s.memory 1280) :: (MachineState.readWord s.memory 1248) :: rest} = _
  rw [col12_raw_run s carry P (MachineState.readWord s.memory 1312) n1 n2 n3 n4 n5 n6 n7 n8 mask (MachineState.readWord s.memory 1280) ((MachineState.readWord s.memory 1248) :: rest) (by simp; omega) (by simp) hact]
  apply congrArg some
  subst mask
  simp only [col12RawModel, col12Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint]

#print axioms col12_run

theorem col12_read0 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col12Model, read_store_disjoint]

theorem col12_read224 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col12Model, read_store_disjoint]

theorem col12_read2720 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 2720 =
      MachineState.readWord s.memory 2720 := by
  simp (disch := omega) [col12Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

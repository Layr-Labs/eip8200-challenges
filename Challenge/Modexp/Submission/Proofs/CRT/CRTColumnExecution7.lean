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

def col7part0Program : List Instr :=
  [.push 2 992,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def col7part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 992
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  {s with pc := UInt256.ofNat 6599, memory := s.memory, stack := v2 :: v1 :: x1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem col7part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part0Program {s with pc := UInt256.ofNat 6587, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (col7part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
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
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col7part0Program, col7part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha768, hf768, ha992, hf992]

#print axioms col7part0_run

def col7part1Program : List Instr :=
  [.push 2 960,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 928,
   .op .MLOAD]

def col7part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 960
  let v1 : UInt256 := MachineState.readWord s.memory 800
  let v2 : UInt256 := v1 * v0
  let v3 : UInt256 := v2 + x0
  let v4 : UInt256 := MachineState.readWord s.memory 928
  {s with pc := UInt256.ofNat 6613, memory := s.memory, stack := v4 :: v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col7part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part1Program {s with pc := UInt256.ofNat 6599, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col7part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  simp [col7part1Program, col7part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha800, hf800, ha928, hf928, ha960, hf960]

#print axioms col7part1_run

def col7part2Program : List Instr :=
  [.push 2 832,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 896,
   .op .MLOAD,
   .push 2 864,
   .op .MLOAD]

def col7part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 832
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 896
  let v4 : UInt256 := MachineState.readWord s.memory 864
  {s with pc := UInt256.ofNat 6627, memory := s.memory, stack := v4 :: v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem col7part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part2Program {s with pc := UInt256.ofNat 6613, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (col7part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
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
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  have ha864 : (864 : UInt256).toNat = 864 := rfl
  have hf864 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 864 32 (by decide) (by norm_num) hact
  have ha896 : (896 : UInt256).toNat = 896 := rfl
  have hf896 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 896 32 (by decide) (by norm_num) hact
  simp [col7part2Program, col7part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha832, hf832, ha864, hf864, ha896, hf896]

#print axioms col7part2_run

def col7part3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 960,
   .op .MLOAD]

def col7part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := UInt256.mulMod x5 x3 x4
  let v4 : UInt256 := MachineState.readWord s.memory 960
  {s with pc := UInt256.ofNat 6638, memory := s.memory, stack := v4 :: x7 :: v3 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem col7part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part3Program {s with pc := UInt256.ofNat 6627, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (col7part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
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
  simp [col7part3Program, col7part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha960, hf960]

#print axioms col7part3_run

def col7part4Program : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 928,
   .op .MLOAD,
   .push 2 832,
   .op .MLOAD]

def col7part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 800
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  let v3 : UInt256 := MachineState.readWord s.memory 928
  let v4 : UInt256 := MachineState.readWord s.memory 832
  {s with pc := UInt256.ofNat 6653, memory := s.memory, stack := v4 :: v3 :: x5 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col7part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part4Program {s with pc := UInt256.ofNat 6638, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col7part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  simp [col7part4Program, col7part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha800, hf800, ha832, hf832, ha928, hf928]

#print axioms col7part4_run

def col7part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 896,
   .op .MLOAD,
   .push 2 864,
   .op .MLOAD,
   .op .MULMOD]

def col7part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 896
  let v3 : UInt256 := MachineState.readWord s.memory 864
  let v4 : UInt256 := UInt256.mulMod v3 v2 x6
  {s with pc := UInt256.ofNat 6665, memory := s.memory, stack := v4 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem col7part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part5Program {s with pc := UInt256.ofNat 6653, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (col7part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
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
  have ha864 : (864 : UInt256).toNat = 864 := rfl
  have hf864 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 864 32 (by decide) (by norm_num) hact
  have ha896 : (896 : UInt256).toNat = 896 := rfl
  have hf896 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 896 32 (by decide) (by norm_num) hact
  simp [col7part5Program, col7part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha864, hf864, ha896, hf896]

#print axioms col7part5_run

def col7part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩)]

def col7part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := x3 + v1
  let v3 : UInt256 := x3 + x2
  {s with pc := UInt256.ofNat 6673, memory := s.memory, stack := x13 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col7part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part6Program {s with pc := UInt256.ofNat 6665, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col7part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col7part6Program, col7part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

#print axioms col7part6_run

def col7part7Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD]

def col7part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x11 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  let v3 : UInt256 := x10 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6683, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col7part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part7Program {s with pc := UInt256.ofNat 6673, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col7part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col7part7Program, col7part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1088, hf1088]

#print axioms col7part7_run

def col7part8Program : List Instr :=
  [.push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1152,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩)]

def col7part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1120
  let v1 : UInt256 := x8 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 1152
  {s with pc := UInt256.ofNat 6695, memory := s.memory, stack := x7 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col7part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part8Program {s with pc := UInt256.ofNat 6683, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col7part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  have ha1152 : (1152 : UInt256).toNat = 1152 := rfl
  have hf1152 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1152 32 (by decide) (by norm_num) hact
  simp [col7part8Program, col7part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1120, hf1120, ha1152, hf1152]

#print axioms col7part8_run

def col7part9Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD]

def col7part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1184
  let v3 : UInt256 := x8 * v2
  let v4 : UInt256 := v3 + v1
  let v5 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 6708, memory := s.memory, stack := v5 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col7part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part9Program {s with pc := UInt256.ofNat 6695, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col7part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [col7part9Program, col7part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1184, hf1184, ha1216, hf1216]

#print axioms col7part9_run

def col7part10Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD]

def col7part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x6 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1248
  let v3 : UInt256 := x5 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6718, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col7part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part10Program {s with pc := UInt256.ofNat 6708, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col7part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col7part10Program, col7part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1248, hf1248]

#print axioms col7part10_run

def col7part11Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1088,
   .op .MLOAD]

def col7part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x11 x2
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  {s with pc := UInt256.ofNat 6729, memory := s.memory, stack := v2 :: x2 :: v1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col7part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part11Program {s with pc := UInt256.ofNat 6718, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col7part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  simp [col7part11Program, col7part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1088, hf1088]

#print axioms col7part11_run

def col7part12Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def col7part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1120
  let v3 : UInt256 := UInt256.mulMod x10 v2 x4
  {s with pc := UInt256.ofNat 6739, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col7part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part12Program {s with pc := UInt256.ofNat 6729, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col7part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col7part12Program, col7part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1120, hf1120]

#print axioms col7part12_run

def col7part13Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1152,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def col7part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1152
  let v2 : UInt256 := UInt256.mulMod x8 v1 x3
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 6749, memory := s.memory, stack := x3 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col7part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part13Program {s with pc := UInt256.ofNat 6739, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col7part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1152 : (1152 : UInt256).toNat = 1152 := rfl
  have hf1152 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1152 32 (by decide) (by norm_num) hact
  simp [col7part13Program, col7part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1152, hf1152]

#print axioms col7part13_run

def col7part14Program : List Instr :=
  [.push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def col7part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1184
  let v1 : UInt256 := UInt256.mulMod x7 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 6761, memory := s.memory, stack := v3 :: x3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col7part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part14Program {s with pc := UInt256.ofNat 6749, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col7part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [col7part14Program, col7part14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1184, hf1184, ha1216, hf1216]

#print axioms col7part14_run

def col7part15Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD]

def col7part15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x7 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1248
  let v3 : UInt256 := UInt256.mulMod x6 v2 x4
  {s with pc := UInt256.ofNat 6771, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col7part15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part15Program {s with pc := UInt256.ofNat 6761, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col7part15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col7part15Program, col7part15Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1248, hf1248]

#print axioms col7part15_run

def col7part16Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩)]

def col7part16Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x2 * x14
  {s with pc := UInt256.ofNat 6779, memory := s.memory, stack := x13 :: v1 :: x4 :: x3 :: v0 :: x3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col7part16_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part16Program {s with pc := UInt256.ofNat 6771, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col7part16Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col7part16Program, col7part16Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

#print axioms col7part16_run

def col7part17Program : List Instr :=
  [.op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1280,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 1 128,
   .op .MULMOD]

def col7part17Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1280
  let v2 : UInt256 := UInt256.mulMod v0 x2 x3
  let v3 : UInt256 := v2 + x4
  let v4 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v3 x5
  {s with pc := UInt256.ofNat 6790, memory := v1, stack := v4 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem col7part17_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7part17Program {s with pc := UInt256.ofNat 6779, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (col7part17Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
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
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [col7part17Program, col7part17Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha1280, hf1280]

#print axioms col7part17_run

def col7Program : List Instr :=
  [.push 2 992,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 2 960,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 928,
   .op .MLOAD,
   .push 2 832,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 896,
   .op .MLOAD,
   .push 2 864,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 960,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 928,
   .op .MLOAD,
   .push 2 832,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 896,
   .op .MLOAD,
   .push 2 864,
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
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1152,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1152,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
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
   .push 2 1280,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 1 128,
   .op .MULMOD]

def col7RawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 992
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 960
  let v4 : UInt256 := MachineState.readWord s.memory 800
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := MachineState.readWord s.memory 928
  let v8 : UInt256 := MachineState.readWord s.memory 832
  let v9 : UInt256 := v8 * v7
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := MachineState.readWord s.memory 896
  let v12 : UInt256 := MachineState.readWord s.memory 864
  let v13 : UInt256 := v12 * v11
  let v14 : UInt256 := v13 + v10
  let v15 : UInt256 := v14 + v14
  let v16 : UInt256 := UInt256.mulMod v0 v1 P
  let v17 : UInt256 := MachineState.readWord s.memory 960
  let v18 : UInt256 := MachineState.readWord s.memory 800
  let v19 : UInt256 := UInt256.mulMod v18 v17 P
  let v20 : UInt256 := v19 + v16
  let v21 : UInt256 := MachineState.readWord s.memory 928
  let v22 : UInt256 := MachineState.readWord s.memory 832
  let v23 : UInt256 := UInt256.mulMod v22 v21 P
  let v24 : UInt256 := v23 + v20
  let v25 : UInt256 := MachineState.readWord s.memory 896
  let v26 : UInt256 := MachineState.readWord s.memory 864
  let v27 : UInt256 := UInt256.mulMod v26 v25 P
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := v28 + v28
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v15
  let v32 : UInt256 := n7 * n8
  let v33 : UInt256 := v32 + v31
  let v34 : UInt256 := MachineState.readWord s.memory 1088
  let v35 : UInt256 := n6 * v34
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := MachineState.readWord s.memory 1120
  let v38 : UInt256 := n5 * v37
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := MachineState.readWord s.memory 1152
  let v41 : UInt256 := n4 * v40
  let v42 : UInt256 := v41 + v39
  let v43 : UInt256 := MachineState.readWord s.memory 1184
  let v44 : UInt256 := n3 * v43
  let v45 : UInt256 := v44 + v42
  let v46 : UInt256 := MachineState.readWord s.memory 1216
  let v47 : UInt256 := n2 * v46
  let v48 : UInt256 := v47 + v45
  let v49 : UInt256 := MachineState.readWord s.memory 1248
  let v50 : UInt256 := n1 * v49
  let v51 : UInt256 := v50 + v48
  let v52 : UInt256 := UInt256.mulMod n7 n8 P
  let v53 : UInt256 := v52 + v30
  let v54 : UInt256 := MachineState.readWord s.memory 1088
  let v55 : UInt256 := UInt256.mulMod n6 v54 P
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := MachineState.readWord s.memory 1120
  let v58 : UInt256 := UInt256.mulMod n5 v57 P
  let v59 : UInt256 := v58 + v56
  let v60 : UInt256 := MachineState.readWord s.memory 1152
  let v61 : UInt256 := UInt256.mulMod n4 v60 P
  let v62 : UInt256 := v61 + v59
  let v63 : UInt256 := MachineState.readWord s.memory 1184
  let v64 : UInt256 := UInt256.mulMod n3 v63 P
  let v65 : UInt256 := v64 + v62
  let v66 : UInt256 := MachineState.readWord s.memory 1216
  let v67 : UInt256 := UInt256.mulMod n2 v66 P
  let v68 : UInt256 := v67 + v65
  let v69 : UInt256 := MachineState.readWord s.memory 1248
  let v70 : UInt256 := UInt256.mulMod n1 v69 P
  let v71 : UInt256 := v70 + v68
  let v72 : UInt256 := v51 * minv
  let v73 : UInt256 := UInt256.land mask v72
  let v74 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v73.toNat 32) 1280
  let v75 : UInt256 := UInt256.mulMod v73 n0 P
  let v76 : UInt256 := v75 + v71
  let v77 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v76 P
  {s with pc := UInt256.ofNat 6790, memory := v74, stack := v77 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col7_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col7Program {s with pc := UInt256.ofNat 6587, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col7RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 992
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 960
  let v4 : UInt256 := MachineState.readWord s.memory 800
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := MachineState.readWord s.memory 928
  let v8 : UInt256 := MachineState.readWord s.memory 832
  let v9 : UInt256 := v8 * v7
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := MachineState.readWord s.memory 896
  let v12 : UInt256 := MachineState.readWord s.memory 864
  let v13 : UInt256 := v12 * v11
  let v14 : UInt256 := v13 + v10
  let v15 : UInt256 := v14 + v14
  let v16 : UInt256 := UInt256.mulMod v0 v1 P
  let v17 : UInt256 := MachineState.readWord s.memory 960
  let v18 : UInt256 := MachineState.readWord s.memory 800
  let v19 : UInt256 := UInt256.mulMod v18 v17 P
  let v20 : UInt256 := v19 + v16
  let v21 : UInt256 := MachineState.readWord s.memory 928
  let v22 : UInt256 := MachineState.readWord s.memory 832
  let v23 : UInt256 := UInt256.mulMod v22 v21 P
  let v24 : UInt256 := v23 + v20
  let v25 : UInt256 := MachineState.readWord s.memory 896
  let v26 : UInt256 := MachineState.readWord s.memory 864
  let v27 : UInt256 := UInt256.mulMod v26 v25 P
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := v28 + v28
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v15
  let v32 : UInt256 := n7 * n8
  let v33 : UInt256 := v32 + v31
  let v34 : UInt256 := MachineState.readWord s.memory 1088
  let v35 : UInt256 := n6 * v34
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := MachineState.readWord s.memory 1120
  let v38 : UInt256 := n5 * v37
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := MachineState.readWord s.memory 1152
  let v41 : UInt256 := n4 * v40
  let v42 : UInt256 := v41 + v39
  let v43 : UInt256 := MachineState.readWord s.memory 1184
  let v44 : UInt256 := n3 * v43
  let v45 : UInt256 := v44 + v42
  let v46 : UInt256 := MachineState.readWord s.memory 1216
  let v47 : UInt256 := n2 * v46
  let v48 : UInt256 := v47 + v45
  let v49 : UInt256 := MachineState.readWord s.memory 1248
  let v50 : UInt256 := n1 * v49
  let v51 : UInt256 := v50 + v48
  let v52 : UInt256 := UInt256.mulMod n7 n8 P
  let v53 : UInt256 := v52 + v30
  let v54 : UInt256 := MachineState.readWord s.memory 1088
  let v55 : UInt256 := UInt256.mulMod n6 v54 P
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := MachineState.readWord s.memory 1120
  let v58 : UInt256 := UInt256.mulMod n5 v57 P
  let v59 : UInt256 := v58 + v56
  let v60 : UInt256 := MachineState.readWord s.memory 1152
  let v61 : UInt256 := UInt256.mulMod n4 v60 P
  let v62 : UInt256 := v61 + v59
  let v63 : UInt256 := MachineState.readWord s.memory 1184
  let v64 : UInt256 := UInt256.mulMod n3 v63 P
  let v65 : UInt256 := v64 + v62
  let v66 : UInt256 := MachineState.readWord s.memory 1216
  let v67 : UInt256 := UInt256.mulMod n2 v66 P
  let v68 : UInt256 := v67 + v65
  let v69 : UInt256 := MachineState.readWord s.memory 1248
  let v70 : UInt256 := UInt256.mulMod n1 v69 P
  let v71 : UInt256 := v70 + v68
  let v72 : UInt256 := v51 * minv
  let v73 : UInt256 := UInt256.land mask v72
  let v74 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v73.toNat 32) 1280
  let v75 : UInt256 := UInt256.mulMod v73 n0 P
  let v76 : UInt256 := v75 + v71
  let v77 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v76 P
  have h0 : runInstructions col7part0Program {s with pc := UInt256.ofNat 6587, memory := s.memory, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6599, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part0Model, v0, v1, v2] using col7part0_run (s) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col7part1Program {s with pc := UInt256.ofNat 6599, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6613, memory := s.memory, stack := v7 :: v6 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part1Model, v3, v4, v5, v6, v7] using col7part1_run (s) (v2) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h2 : runInstructions col7part2Program {s with pc := UInt256.ofNat 6613, memory := s.memory, stack := v7 :: v6 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6627, memory := s.memory, stack := v12 :: v11 :: v10 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part2Model, v8, v9, v10, v11, v12] using col7part2_run (s) (v7) (v6) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h3 : runInstructions col7part3Program {s with pc := UInt256.ofNat 6627, memory := s.memory, stack := v12 :: v11 :: v10 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6638, memory := s.memory, stack := v17 :: P :: v16 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part3Model, v13, v14, v15, v16, v17] using col7part3_run (s) (v12) (v11) (v10) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h4 : runInstructions col7part4Program {s with pc := UInt256.ofNat 6638, memory := s.memory, stack := v17 :: P :: v16 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6653, memory := s.memory, stack := v22 :: v21 :: P :: v20 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part4Model, v18, v19, v20, v21, v22] using col7part4_run (s) (v17) (P) (v16) (v15) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h5 : runInstructions col7part5Program {s with pc := UInt256.ofNat 6653, memory := s.memory, stack := v22 :: v21 :: P :: v20 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6665, memory := s.memory, stack := v27 :: v24 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part5Model, v23, v24, v25, v26, v27] using col7part5_run (s) (v22) (v21) (P) (v20) (v15) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h6 : runInstructions col7part6Program {s with pc := UInt256.ofNat 6665, memory := s.memory, stack := v27 :: v24 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6673, memory := s.memory, stack := n8 :: v31 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part6Model, v28, v29, v30, v31] using col7part6_run (s) (v27) (v24) (v15) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h7 : runInstructions col7part7Program {s with pc := UInt256.ofNat 6673, memory := s.memory, stack := n8 :: v31 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6683, memory := s.memory, stack := v36 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part7Model, v32, v33, v34, v35, v36] using col7part7_run (s) (n8) (v31) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h8 : runInstructions col7part8Program {s with pc := UInt256.ofNat 6683, memory := s.memory, stack := v36 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6695, memory := s.memory, stack := n4 :: v40 :: v39 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part8Model, v37, v38, v39, v40] using col7part8_run (s) (v36) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h9 : runInstructions col7part9Program {s with pc := UInt256.ofNat 6695, memory := s.memory, stack := n4 :: v40 :: v39 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6708, memory := s.memory, stack := v46 :: v45 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part9Model, v41, v42, v43, v44, v45, v46] using col7part9_run (s) (n4) (v40) (v39) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h10 : runInstructions col7part10Program {s with pc := UInt256.ofNat 6708, memory := s.memory, stack := v46 :: v45 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6718, memory := s.memory, stack := v51 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part10Model, v47, v48, v49, v50, v51] using col7part10_run (s) (v46) (v45) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h11 : runInstructions col7part11Program {s with pc := UInt256.ofNat 6718, memory := s.memory, stack := v51 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6729, memory := s.memory, stack := v54 :: P :: v53 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part11Model, v52, v53, v54] using col7part11_run (s) (v51) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h12 : runInstructions col7part12Program {s with pc := UInt256.ofNat 6729, memory := s.memory, stack := v54 :: P :: v53 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6739, memory := s.memory, stack := v58 :: v56 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part12Model, v55, v56, v57, v58] using col7part12_run (s) (v54) (P) (v53) (v51) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h13 : runInstructions col7part13Program {s with pc := UInt256.ofNat 6739, memory := s.memory, stack := v58 :: v56 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6749, memory := s.memory, stack := P :: v62 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part13Model, v59, v60, v61, v62] using col7part13_run (s) (v58) (v56) (v51) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h14 : runInstructions col7part14Program {s with pc := UInt256.ofNat 6749, memory := s.memory, stack := P :: v62 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6761, memory := s.memory, stack := v66 :: P :: v65 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part14Model, v63, v64, v65, v66] using col7part14_run (s) (P) (v62) (v51) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h15 : runInstructions col7part15Program {s with pc := UInt256.ofNat 6761, memory := s.memory, stack := v66 :: P :: v65 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6771, memory := s.memory, stack := v70 :: v68 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part15Model, v67, v68, v69, v70] using col7part15_run (s) (v66) (P) (v65) (v51) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h16 : runInstructions col7part16Program {s with pc := UInt256.ofNat 6771, memory := s.memory, stack := v70 :: v68 :: v51 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6779, memory := s.memory, stack := mask :: v72 :: n0 :: P :: v71 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part16Model, v71, v72] using col7part16_run (s) (v70) (v68) (v51) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h17 : runInstructions col7part17Program {s with pc := UInt256.ofNat 6779, memory := s.memory, stack := mask :: v72 :: n0 :: P :: v71 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6790, memory := v74, stack := v77 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col7part17Model, v73, v74, v75, v76, v77] using col7part17_run (s) (mask) (v72) (n0) (P) (v71) (P) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 h17)))))))))))))))))

#print axioms col7_raw_run

def col7Model (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 992
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := MachineState.readWord s.memory 960
  let v5 : UInt256 := MachineState.readWord s.memory 800
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 928
  let v9 : UInt256 := MachineState.readWord s.memory 832
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := MachineState.readWord s.memory 896
  let v13 : UInt256 := MachineState.readWord s.memory 864
  let v14 : UInt256 := UInt256.mulMod v13 v12 P
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := MachineState.readWord s.memory 960
  let v17 : UInt256 := MachineState.readWord s.memory 800
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v3
  let v20 : UInt256 := MachineState.readWord s.memory 928
  let v21 : UInt256 := MachineState.readWord s.memory 832
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v19
  let v24 : UInt256 := MachineState.readWord s.memory 896
  let v25 : UInt256 := MachineState.readWord s.memory 864
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v23
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := v15 + v15
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v28
  let v32 : UInt256 := MachineState.readWord s.memory 1056
  let v33 : UInt256 := UInt256.mulMod n7 v32 P
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := MachineState.readWord s.memory 1088
  let v36 : UInt256 := UInt256.mulMod n6 v35 P
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := MachineState.readWord s.memory 1120
  let v39 : UInt256 := UInt256.mulMod n5 v38 P
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := MachineState.readWord s.memory 1152
  let v42 : UInt256 := UInt256.mulMod n4 v41 P
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := MachineState.readWord s.memory 1184
  let v45 : UInt256 := UInt256.mulMod n3 v44 P
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := MachineState.readWord s.memory 1216
  let v48 : UInt256 := UInt256.mulMod n2 v47 P
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := MachineState.readWord s.memory 1248
  let v51 : UInt256 := UInt256.mulMod n1 v50 P
  let v52 : UInt256 := v51 + v49
  let v53 : UInt256 := MachineState.readWord s.memory 1056
  let v54 : UInt256 := n7 * v53
  let v55 : UInt256 := v54 + v31
  let v56 : UInt256 := MachineState.readWord s.memory 1088
  let v57 : UInt256 := n6 * v56
  let v58 : UInt256 := v57 + v55
  let v59 : UInt256 := MachineState.readWord s.memory 1120
  let v60 : UInt256 := n5 * v59
  let v61 : UInt256 := v60 + v58
  let v62 : UInt256 := MachineState.readWord s.memory 1152
  let v63 : UInt256 := n4 * v62
  let v64 : UInt256 := v63 + v61
  let v65 : UInt256 := MachineState.readWord s.memory 1184
  let v66 : UInt256 := n3 * v65
  let v67 : UInt256 := v66 + v64
  let v68 : UInt256 := MachineState.readWord s.memory 1216
  let v69 : UInt256 := n2 * v68
  let v70 : UInt256 := v69 + v67
  let v71 : UInt256 := MachineState.readWord s.memory 1248
  let v72 : UInt256 := n1 * v71
  let v73 : UInt256 := v72 + v70
  let v74 : UInt256 := UInt256.land mask v73
  let v75 : UInt256 := minv * v74
  let v76 : UInt256 := UInt256.land mask v75
  let v77 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v76.toNat 32) 1280
  let v78 : UInt256 := n0 * v76
  let v79 : UInt256 := v78 + v73
  let v80 : UInt256 := UInt256.mulMod n0 v76 P
  let v81 : UInt256 := v80 + v52
  let v89 : UInt256 := UInt256.mulMod v81 (UInt256.ofNat 128) P
  {s with pc := UInt256.ofNat 6790, memory := v77, stack := v89 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col7_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1)) :
    runInstructions col7Program (cachedState 7
      {s with pc := UInt256.ofNat 6587, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 8 (col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  change runInstructions col7Program
    {s with pc := UInt256.ofNat 6587, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: (MachineState.readWord s.memory 1056) :: mask :: minv :: rest} = _
  rw [col7_raw_run s carry P n0 n1 n2 n3 n4 n5 n6 n7 (MachineState.readWord s.memory 1056) mask minv rest hcap hact]
  apply congrArg some
  subst mask
  simp only [col7RawModel, col7Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint]

#print axioms col7_run

theorem col7_read0 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col7Model, read_store_disjoint]

theorem col7_read224 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col7Model, read_store_disjoint]

theorem col7_read2720 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 2720 =
      MachineState.readWord s.memory 2720 := by
  simp (disch := omega) [col7Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

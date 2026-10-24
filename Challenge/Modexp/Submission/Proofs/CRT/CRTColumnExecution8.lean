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

def col8part0Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def col8part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  {s with pc := UInt256.ofNat 6801, memory := s.memory, stack := v2 :: v1 :: x1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem col8part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part0Program {s with pc := UInt256.ofNat 6789, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (col8part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
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
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  simp [col8part0Program, col8part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha768, hf768, ha1024, hf1024]

#print axioms col8part0_run

def col8part1Program : List Instr :=
  [.push 2 992,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 960,
   .op .MLOAD]

def col8part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 992
  let v1 : UInt256 := MachineState.readWord s.memory 800
  let v2 : UInt256 := v1 * v0
  let v3 : UInt256 := v2 + x0
  let v4 : UInt256 := MachineState.readWord s.memory 960
  {s with pc := UInt256.ofNat 6815, memory := s.memory, stack := v4 :: v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col8part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part1Program {s with pc := UInt256.ofNat 6801, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col8part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col8part1Program, col8part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha800, hf800, ha960, hf960, ha992, hf992]

#print axioms col8part1_run

def col8part2Program : List Instr :=
  [.push 2 832,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 928,
   .op .MLOAD,
   .push 2 864,
   .op .MLOAD]

def col8part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 832
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 928
  let v4 : UInt256 := MachineState.readWord s.memory 864
  {s with pc := UInt256.ofNat 6829, memory := s.memory, stack := v4 :: v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem col8part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part2Program {s with pc := UInt256.ofNat 6815, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (col8part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
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
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  simp [col8part2Program, col8part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha832, hf832, ha864, hf864, ha928, hf928]

#print axioms col8part2_run

def col8part3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 992,
   .op .MLOAD]

def col8part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := UInt256.mulMod x5 x3 x4
  let v4 : UInt256 := MachineState.readWord s.memory 992
  {s with pc := UInt256.ofNat 6840, memory := s.memory, stack := v4 :: x7 :: v3 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem col8part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part3Program {s with pc := UInt256.ofNat 6829, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (col8part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
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
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col8part3Program, col8part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha992, hf992]

#print axioms col8part3_run

def col8part4Program : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 960,
   .op .MLOAD,
   .push 2 832,
   .op .MLOAD]

def col8part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 800
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  let v3 : UInt256 := MachineState.readWord s.memory 960
  let v4 : UInt256 := MachineState.readWord s.memory 832
  {s with pc := UInt256.ofNat 6855, memory := s.memory, stack := v4 :: v3 :: x5 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col8part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part4Program {s with pc := UInt256.ofNat 6840, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col8part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  simp [col8part4Program, col8part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha800, hf800, ha832, hf832, ha960, hf960]

#print axioms col8part4_run

def col8part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 928,
   .op .MLOAD,
   .push 2 864,
   .op .MLOAD,
   .op .MULMOD]

def col8part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 928
  let v3 : UInt256 := MachineState.readWord s.memory 864
  let v4 : UInt256 := UInt256.mulMod v3 v2 x6
  {s with pc := UInt256.ofNat 6867, memory := s.memory, stack := v4 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem col8part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part5Program {s with pc := UInt256.ofNat 6855, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (col8part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
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
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  simp [col8part5Program, col8part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha864, hf864, ha928, hf928]

#print axioms col8part5_run

def col8part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 896,
   .op .MLOAD]

def col8part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := x3 + v1
  let v3 : UInt256 := x3 + x2
  let v4 : UInt256 := MachineState.readWord s.memory 896
  {s with pc := UInt256.ofNat 6878, memory := s.memory, stack := v4 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col8part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part6Program {s with pc := UInt256.ofNat 6867, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col8part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha896 : (896 : UInt256).toNat = 896 := rfl
  have hf896 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 896 32 (by decide) (by norm_num) hact
  simp [col8part6Program, col8part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha896, hf896]

#print axioms col8part6_run

def col8part7Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .push 1 160,
   .op .SHR,
   .op (.Swap ⟨11, by decide⟩)]

def col8part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 160)
  {s with pc := UInt256.ofNat 6887, memory := s.memory, stack := x12 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v3 :: x13 :: x14 :: rest}

theorem col8part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part7Program {s with pc := UInt256.ofNat 6878, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
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
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, col8part7Program, col8part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha0, hf0]

#print axioms col8part7_run

def col8part8Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def col8part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x12 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  let v3 : UInt256 := x11 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6897, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part8Program {s with pc := UInt256.ofNat 6887, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col8part8Program, col8part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1088, hf1088]

#print axioms col8part8_run

def col8part9Program : List Instr :=
  [.push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1152,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def col8part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1120
  let v1 : UInt256 := x9 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 1152
  {s with pc := UInt256.ofNat 6909, memory := s.memory, stack := x8 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col8part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part9Program {s with pc := UInt256.ofNat 6897, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col8part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  simp [col8part9Program, col8part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1120, hf1120, ha1152, hf1152]

#print axioms col8part9_run

def col8part10Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD]

def col8part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1184
  let v3 : UInt256 := x9 * v2
  let v4 : UInt256 := v3 + v1
  let v5 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 6922, memory := s.memory, stack := v5 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col8part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part10Program {s with pc := UInt256.ofNat 6909, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col8part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col8part10Program, col8part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1184, hf1184, ha1216, hf1216]

#print axioms col8part10_run

def col8part11Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def col8part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x7 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1248
  let v3 : UInt256 := x6 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6932, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part11Program {s with pc := UInt256.ofNat 6922, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col8part11Program, col8part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1248, hf1248]

#print axioms col8part11_run

def col8part12Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 2 896,
   .op .MLOAD]

def col8part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1280
  let v1 : UInt256 := x4 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 896
  {s with pc := UInt256.ofNat 6945, memory := s.memory, stack := v3 :: x2 :: x1 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col8part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part12Program {s with pc := UInt256.ofNat 6932, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col8part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  have ha896 : (896 : UInt256).toNat = 896 := rfl
  have hf896 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 896 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [col8part12Program, col8part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha896, hf896, ha1280, hf1280]

#print axioms col8part12_run

def col8part13Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1056,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD]

def col8part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1056
  let v3 : UInt256 := UInt256.mulMod x13 v2 x4
  {s with pc := UInt256.ofNat 6955, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col8part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part13Program {s with pc := UInt256.ofNat 6945, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col8part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha1056 : (1056 : UInt256).toNat = 1056 := rfl
  have hf1056 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1056 32 (by decide) (by norm_num) hact
  simp [col8part13Program, col8part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1056, hf1056]

#print axioms col8part13_run

def col8part14Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def col8part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1088
  let v2 : UInt256 := UInt256.mulMod x11 v1 x3
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 6965, memory := s.memory, stack := x3 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part14Program {s with pc := UInt256.ofNat 6955, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col8part14Program, col8part14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1088, hf1088]

#print axioms col8part14_run

def col8part15Program : List Instr :=
  [.push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1152,
   .op .MLOAD]

def col8part15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1120
  let v1 : UInt256 := UInt256.mulMod x10 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 1152
  {s with pc := UInt256.ofNat 6977, memory := s.memory, stack := v3 :: x3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part15Program {s with pc := UInt256.ofNat 6965, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1152 : (1152 : UInt256).toNat = 1152 := rfl
  have hf1152 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1152 32 (by decide) (by norm_num) hact
  simp [col8part15Program, col8part15Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1120, hf1120, ha1152, hf1152]

#print axioms col8part15_run

def col8part16Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD]

def col8part16Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1184
  let v3 : UInt256 := UInt256.mulMod x9 v2 x4
  {s with pc := UInt256.ofNat 6987, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col8part16_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part16Program {s with pc := UInt256.ofNat 6977, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col8part16Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col8part16Program, col8part16Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1184, hf1184]

#print axioms col8part16_run

def col8part17Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def col8part17Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1216
  let v2 : UInt256 := UInt256.mulMod x7 v1 x3
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 6997, memory := s.memory, stack := x3 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part17_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part17Program {s with pc := UInt256.ofNat 6987, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part17Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col8part17Program, col8part17Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1216, hf1216]

#print axioms col8part17_run

def col8part18Program : List Instr :=
  [.push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1280,
   .op .MLOAD]

def col8part18Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1248
  let v1 : UInt256 := UInt256.mulMod x6 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 1280
  {s with pc := UInt256.ofNat 7009, memory := s.memory, stack := v3 :: x3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part18_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part18Program {s with pc := UInt256.ofNat 6997, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part18Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col8part18Program, col8part18Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1248, hf1248, ha1280, hf1280]

#print axioms col8part18_run

def col8part19Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .push 12 79228162514264337593543950335,
   .op .AND]

def col8part19Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x6 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x15 * x3
  let v3 : UInt256 := UInt256.land (UInt256.ofNat 79228162514264337593543950335) v2
  {s with pc := UInt256.ofNat 7029, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col8part19_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part19Program {s with pc := UInt256.ofNat 7009, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col8part19Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col8part19Program, col8part19Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

#print axioms col8part19_run

def col8part20Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 2 1312,
   .op .MSTORE,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def col8part20Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1312
  {s with pc := UInt256.ofNat 7039, memory := v0, stack := x4 :: x0 :: x3 :: x0 :: x2 :: x1 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part20_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part20Program {s with pc := UInt256.ofNat 7029, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part20Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1312 : (1312 : UInt256).toNat = 1312 := rfl
  have hf1312 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1312 32 (by decide) (by norm_num) hact
  simp [col8part20Program, col8part20Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha1312, hf1312]

#print axioms col8part20_run

def col8part21Program : List Instr :=
  [.op .MULMOD,
   .op (.Swap ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩)]

def col8part21Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := x8 * x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := v0 + x5
  {s with pc := UInt256.ofNat 7047, memory := s.memory, stack := v2 :: v3 :: v2 :: x7 :: x6 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem col8part21_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part21Program {s with pc := UInt256.ofNat 7039, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (col8part21Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
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
  simp [col8part21Program, col8part21Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19]

#print axioms col8part21_run

def col8part22Program : List Instr :=
  [.op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def col8part22Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot x0
  let v1 : UInt256 := UInt256.addMod x1 v0 x3
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 5)
  {s with pc := UInt256.ofNat 7056, memory := s.memory, stack := x13 :: x2 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col8part22_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part22Program {s with pc := UInt256.ofNat 7047, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col8part22Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col8part22Program, col8part22Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16]

#print axioms col8part22_run

def col8part23Program : List Instr :=
  [.op .AND,
   .push 2 1344,
   .op .MSTORE,
   .push 1 12,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 244,
   .op .SHR]

def col8part23Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1344
  let v2 : UInt256 := UInt256.shiftLeft x2 (UInt256.ofNat 12)
  let v3 : UInt256 := UInt256.shiftRight x3 (UInt256.ofNat 244)
  {s with pc := UInt256.ofNat 7068, memory := v1, stack := v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col8part23_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part23Program {s with pc := UInt256.ofNat 7056, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col8part23Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [col8part23Program, col8part23Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1344, hf1344]

#print axioms col8part23_run

def col8part24Program : List Instr :=
  [.op .ADD]

def col8part24Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  {s with pc := UInt256.ofNat 7069, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col8part24_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8part24Program {s with pc := UInt256.ofNat 7068, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col8part24Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  simp [col8part24Program, col8part24Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14]

#print axioms col8part24_run

def col8Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 2 992,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 960,
   .op .MLOAD,
   .push 2 832,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 928,
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
   .push 2 992,
   .op .MLOAD,
   .push 2 800,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 960,
   .op .MLOAD,
   .push 2 832,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 928,
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
   .push 2 896,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .push 1 160,
   .op .SHR,
   .op (.Swap ⟨11, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1152,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 2 896,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1056,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1120,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1152,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1184,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .push 12 79228162514264337593543950335,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1312,
   .op .MSTORE,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
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
   .push 2 1344,
   .op .MSTORE,
   .push 1 12,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 244,
   .op .SHR,
   .op .ADD]

def col8RawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 992
  let v4 : UInt256 := MachineState.readWord s.memory 800
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := MachineState.readWord s.memory 960
  let v8 : UInt256 := MachineState.readWord s.memory 832
  let v9 : UInt256 := v8 * v7
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := MachineState.readWord s.memory 928
  let v12 : UInt256 := MachineState.readWord s.memory 864
  let v13 : UInt256 := v12 * v11
  let v14 : UInt256 := v13 + v10
  let v15 : UInt256 := v14 + v14
  let v16 : UInt256 := UInt256.mulMod v0 v1 P
  let v17 : UInt256 := MachineState.readWord s.memory 992
  let v18 : UInt256 := MachineState.readWord s.memory 800
  let v19 : UInt256 := UInt256.mulMod v18 v17 P
  let v20 : UInt256 := v19 + v16
  let v21 : UInt256 := MachineState.readWord s.memory 960
  let v22 : UInt256 := MachineState.readWord s.memory 832
  let v23 : UInt256 := UInt256.mulMod v22 v21 P
  let v24 : UInt256 := v23 + v20
  let v25 : UInt256 := MachineState.readWord s.memory 928
  let v26 : UInt256 := MachineState.readWord s.memory 864
  let v27 : UInt256 := UInt256.mulMod v26 v25 P
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := v28 + v28
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v15
  let v32 : UInt256 := MachineState.readWord s.memory 896
  let v33 : UInt256 := v32 * v32
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 0
  let v36 : UInt256 := UInt256.shiftRight v35 (UInt256.ofNat 160)
  let v37 : UInt256 := v36 * n8
  let v38 : UInt256 := v37 + v34
  let v39 : UInt256 := MachineState.readWord s.memory 1088
  let v40 : UInt256 := n7 * v39
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := MachineState.readWord s.memory 1120
  let v43 : UInt256 := n6 * v42
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := MachineState.readWord s.memory 1152
  let v46 : UInt256 := n5 * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := MachineState.readWord s.memory 1184
  let v49 : UInt256 := n4 * v48
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord s.memory 1216
  let v52 : UInt256 := n3 * v51
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := MachineState.readWord s.memory 1248
  let v55 : UInt256 := n2 * v54
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := MachineState.readWord s.memory 1280
  let v58 : UInt256 := n1 * v57
  let v59 : UInt256 := v58 + v56
  let v60 : UInt256 := MachineState.readWord s.memory 896
  let v61 : UInt256 := UInt256.mulMod v60 v60 P
  let v62 : UInt256 := v61 + v30
  let v63 : UInt256 := MachineState.readWord s.memory 1056
  let v64 : UInt256 := UInt256.mulMod v36 v63 P
  let v65 : UInt256 := v64 + v62
  let v66 : UInt256 := MachineState.readWord s.memory 1088
  let v67 : UInt256 := UInt256.mulMod n7 v66 P
  let v68 : UInt256 := v67 + v65
  let v69 : UInt256 := MachineState.readWord s.memory 1120
  let v70 : UInt256 := UInt256.mulMod n6 v69 P
  let v71 : UInt256 := v70 + v68
  let v72 : UInt256 := MachineState.readWord s.memory 1152
  let v73 : UInt256 := UInt256.mulMod n5 v72 P
  let v74 : UInt256 := v73 + v71
  let v75 : UInt256 := MachineState.readWord s.memory 1184
  let v76 : UInt256 := UInt256.mulMod n4 v75 P
  let v77 : UInt256 := v76 + v74
  let v78 : UInt256 := MachineState.readWord s.memory 1216
  let v79 : UInt256 := UInt256.mulMod n3 v78 P
  let v80 : UInt256 := v79 + v77
  let v81 : UInt256 := MachineState.readWord s.memory 1248
  let v82 : UInt256 := UInt256.mulMod n2 v81 P
  let v83 : UInt256 := v82 + v80
  let v84 : UInt256 := MachineState.readWord s.memory 1280
  let v85 : UInt256 := UInt256.mulMod n1 v84 P
  let v86 : UInt256 := v85 + v83
  let v87 : UInt256 := minv * v59
  let v88 : UInt256 := UInt256.land (UInt256.ofNat 79228162514264337593543950335) v87
  let v89 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v88.toNat 32) 1312
  let v90 : UInt256 := UInt256.mulMod n0 v88 P
  let v91 : UInt256 := n0 * v88
  let v92 : UInt256 := v91 + v59
  let v93 : UInt256 := v90 + v86
  let v94 : UInt256 := UInt256.lnot v92
  let v95 : UInt256 := UInt256.addMod v93 v94 P
  let v96 : UInt256 := UInt256.shiftRight v95 (UInt256.ofNat 5)
  let v97 : UInt256 := UInt256.land mask v92
  let v98 : ByteArray := MachineState.writeBytes v89 (Data.Bytes.natToBytesPadded v97.toNat 32) 1344
  let v99 : UInt256 := UInt256.shiftLeft v96 (UInt256.ofNat 12)
  let v100 : UInt256 := UInt256.shiftRight v92 (UInt256.ofNat 244)
  let v101 : UInt256 := v100 + v99
  {s with pc := UInt256.ofNat 7069, memory := v98, stack := v101 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest}

theorem col8_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col8Program {s with pc := UInt256.ofNat 6789, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col8RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := MachineState.readWord s.memory 992
  let v4 : UInt256 := MachineState.readWord s.memory 800
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := MachineState.readWord s.memory 960
  let v8 : UInt256 := MachineState.readWord s.memory 832
  let v9 : UInt256 := v8 * v7
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := MachineState.readWord s.memory 928
  let v12 : UInt256 := MachineState.readWord s.memory 864
  let v13 : UInt256 := v12 * v11
  let v14 : UInt256 := v13 + v10
  let v15 : UInt256 := v14 + v14
  let v16 : UInt256 := UInt256.mulMod v0 v1 P
  let v17 : UInt256 := MachineState.readWord s.memory 992
  let v18 : UInt256 := MachineState.readWord s.memory 800
  let v19 : UInt256 := UInt256.mulMod v18 v17 P
  let v20 : UInt256 := v19 + v16
  let v21 : UInt256 := MachineState.readWord s.memory 960
  let v22 : UInt256 := MachineState.readWord s.memory 832
  let v23 : UInt256 := UInt256.mulMod v22 v21 P
  let v24 : UInt256 := v23 + v20
  let v25 : UInt256 := MachineState.readWord s.memory 928
  let v26 : UInt256 := MachineState.readWord s.memory 864
  let v27 : UInt256 := UInt256.mulMod v26 v25 P
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := v28 + v28
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v15
  let v32 : UInt256 := MachineState.readWord s.memory 896
  let v33 : UInt256 := v32 * v32
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 0
  let v36 : UInt256 := UInt256.shiftRight v35 (UInt256.ofNat 160)
  let v37 : UInt256 := v36 * n8
  let v38 : UInt256 := v37 + v34
  let v39 : UInt256 := MachineState.readWord s.memory 1088
  let v40 : UInt256 := n7 * v39
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := MachineState.readWord s.memory 1120
  let v43 : UInt256 := n6 * v42
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := MachineState.readWord s.memory 1152
  let v46 : UInt256 := n5 * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := MachineState.readWord s.memory 1184
  let v49 : UInt256 := n4 * v48
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord s.memory 1216
  let v52 : UInt256 := n3 * v51
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := MachineState.readWord s.memory 1248
  let v55 : UInt256 := n2 * v54
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := MachineState.readWord s.memory 1280
  let v58 : UInt256 := n1 * v57
  let v59 : UInt256 := v58 + v56
  let v60 : UInt256 := MachineState.readWord s.memory 896
  let v61 : UInt256 := UInt256.mulMod v60 v60 P
  let v62 : UInt256 := v61 + v30
  let v63 : UInt256 := MachineState.readWord s.memory 1056
  let v64 : UInt256 := UInt256.mulMod v36 v63 P
  let v65 : UInt256 := v64 + v62
  let v66 : UInt256 := MachineState.readWord s.memory 1088
  let v67 : UInt256 := UInt256.mulMod n7 v66 P
  let v68 : UInt256 := v67 + v65
  let v69 : UInt256 := MachineState.readWord s.memory 1120
  let v70 : UInt256 := UInt256.mulMod n6 v69 P
  let v71 : UInt256 := v70 + v68
  let v72 : UInt256 := MachineState.readWord s.memory 1152
  let v73 : UInt256 := UInt256.mulMod n5 v72 P
  let v74 : UInt256 := v73 + v71
  let v75 : UInt256 := MachineState.readWord s.memory 1184
  let v76 : UInt256 := UInt256.mulMod n4 v75 P
  let v77 : UInt256 := v76 + v74
  let v78 : UInt256 := MachineState.readWord s.memory 1216
  let v79 : UInt256 := UInt256.mulMod n3 v78 P
  let v80 : UInt256 := v79 + v77
  let v81 : UInt256 := MachineState.readWord s.memory 1248
  let v82 : UInt256 := UInt256.mulMod n2 v81 P
  let v83 : UInt256 := v82 + v80
  let v84 : UInt256 := MachineState.readWord s.memory 1280
  let v85 : UInt256 := UInt256.mulMod n1 v84 P
  let v86 : UInt256 := v85 + v83
  let v87 : UInt256 := minv * v59
  let v88 : UInt256 := UInt256.land (UInt256.ofNat 79228162514264337593543950335) v87
  let v89 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v88.toNat 32) 1312
  let v90 : UInt256 := UInt256.mulMod n0 v88 P
  let v91 : UInt256 := n0 * v88
  let v92 : UInt256 := v91 + v59
  let v93 : UInt256 := v90 + v86
  let v94 : UInt256 := UInt256.lnot v92
  let v95 : UInt256 := UInt256.addMod v93 v94 P
  let v96 : UInt256 := UInt256.shiftRight v95 (UInt256.ofNat 5)
  let v97 : UInt256 := UInt256.land mask v92
  let v98 : ByteArray := MachineState.writeBytes v89 (Data.Bytes.natToBytesPadded v97.toNat 32) 1344
  let v99 : UInt256 := UInt256.shiftLeft v96 (UInt256.ofNat 12)
  let v100 : UInt256 := UInt256.shiftRight v92 (UInt256.ofNat 244)
  let v101 : UInt256 := v100 + v99
  have h0 : runInstructions col8part0Program {s with pc := UInt256.ofNat 6789, memory := s.memory, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6801, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col8part0Model, v0, v1, v2] using col8part0_run (s) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col8part1Program {s with pc := UInt256.ofNat 6801, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6815, memory := s.memory, stack := v7 :: v6 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col8part1Model, v3, v4, v5, v6, v7] using col8part1_run (s) (v2) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h2 : runInstructions col8part2Program {s with pc := UInt256.ofNat 6815, memory := s.memory, stack := v7 :: v6 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6829, memory := s.memory, stack := v12 :: v11 :: v10 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col8part2Model, v8, v9, v10, v11, v12] using col8part2_run (s) (v7) (v6) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h3 : runInstructions col8part3Program {s with pc := UInt256.ofNat 6829, memory := s.memory, stack := v12 :: v11 :: v10 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6840, memory := s.memory, stack := v17 :: P :: v16 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col8part3Model, v13, v14, v15, v16, v17] using col8part3_run (s) (v12) (v11) (v10) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h4 : runInstructions col8part4Program {s with pc := UInt256.ofNat 6840, memory := s.memory, stack := v17 :: P :: v16 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6855, memory := s.memory, stack := v22 :: v21 :: P :: v20 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col8part4Model, v18, v19, v20, v21, v22] using col8part4_run (s) (v17) (P) (v16) (v15) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h5 : runInstructions col8part5Program {s with pc := UInt256.ofNat 6855, memory := s.memory, stack := v22 :: v21 :: P :: v20 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6867, memory := s.memory, stack := v27 :: v24 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col8part5Model, v23, v24, v25, v26, v27] using col8part5_run (s) (v22) (v21) (P) (v20) (v15) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h6 : runInstructions col8part6Program {s with pc := UInt256.ofNat 6867, memory := s.memory, stack := v27 :: v24 :: v15 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6878, memory := s.memory, stack := v32 :: v31 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col8part6Model, v28, v29, v30, v31, v32] using col8part6_run (s) (v27) (v24) (v15) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h7 : runInstructions col8part7Program {s with pc := UInt256.ofNat 6878, memory := s.memory, stack := v32 :: v31 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6887, memory := s.memory, stack := n8 :: v34 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part7Model, v33, v34, v35, v36] using col8part7_run (s) (v32) (v31) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h8 : runInstructions col8part8Program {s with pc := UInt256.ofNat 6887, memory := s.memory, stack := n8 :: v34 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6897, memory := s.memory, stack := v41 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part8Model, v37, v38, v39, v40, v41] using col8part8_run (s) (n8) (v34) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h9 : runInstructions col8part9Program {s with pc := UInt256.ofNat 6897, memory := s.memory, stack := v41 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6909, memory := s.memory, stack := n5 :: v45 :: v44 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part9Model, v42, v43, v44, v45] using col8part9_run (s) (v41) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h10 : runInstructions col8part10Program {s with pc := UInt256.ofNat 6909, memory := s.memory, stack := n5 :: v45 :: v44 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6922, memory := s.memory, stack := v51 :: v50 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part10Model, v46, v47, v48, v49, v50, v51] using col8part10_run (s) (n5) (v45) (v44) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h11 : runInstructions col8part11Program {s with pc := UInt256.ofNat 6922, memory := s.memory, stack := v51 :: v50 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6932, memory := s.memory, stack := v56 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part11Model, v52, v53, v54, v55, v56] using col8part11_run (s) (v51) (v50) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h12 : runInstructions col8part12Program {s with pc := UInt256.ofNat 6932, memory := s.memory, stack := v56 :: v30 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6945, memory := s.memory, stack := v60 :: P :: v30 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part12Model, v57, v58, v59, v60] using col8part12_run (s) (v56) (v30) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h13 : runInstructions col8part13Program {s with pc := UInt256.ofNat 6945, memory := s.memory, stack := v60 :: P :: v30 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6955, memory := s.memory, stack := v64 :: v62 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part13Model, v61, v62, v63, v64] using col8part13_run (s) (v60) (P) (v30) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h14 : runInstructions col8part14Program {s with pc := UInt256.ofNat 6955, memory := s.memory, stack := v64 :: v62 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6965, memory := s.memory, stack := P :: v68 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part14Model, v65, v66, v67, v68] using col8part14_run (s) (v64) (v62) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h15 : runInstructions col8part15Program {s with pc := UInt256.ofNat 6965, memory := s.memory, stack := P :: v68 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6977, memory := s.memory, stack := v72 :: P :: v71 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part15Model, v69, v70, v71, v72] using col8part15_run (s) (P) (v68) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h16 : runInstructions col8part16Program {s with pc := UInt256.ofNat 6977, memory := s.memory, stack := v72 :: P :: v71 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6987, memory := s.memory, stack := v76 :: v74 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part16Model, v73, v74, v75, v76] using col8part16_run (s) (v72) (P) (v71) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h17 : runInstructions col8part17Program {s with pc := UInt256.ofNat 6987, memory := s.memory, stack := v76 :: v74 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 6997, memory := s.memory, stack := P :: v80 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part17Model, v77, v78, v79, v80] using col8part17_run (s) (v76) (v74) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h18 : runInstructions col8part18Program {s with pc := UInt256.ofNat 6997, memory := s.memory, stack := P :: v80 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7009, memory := s.memory, stack := v84 :: P :: v83 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part18Model, v81, v82, v83, v84] using col8part18_run (s) (P) (v80) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h19 : runInstructions col8part19Program {s with pc := UInt256.ofNat 7009, memory := s.memory, stack := v84 :: P :: v83 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7029, memory := s.memory, stack := v88 :: v86 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part19Model, v85, v86, v87, v88] using col8part19_run (s) (v84) (P) (v83) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h20 : runInstructions col8part20Program {s with pc := UInt256.ofNat 7029, memory := s.memory, stack := v88 :: v86 :: v59 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7039, memory := v89, stack := n0 :: v88 :: P :: v88 :: v59 :: v86 :: v88 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part20Model, v89] using col8part20_run (s) (v88) (v86) (v59) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h21 : runInstructions col8part21Program {s with pc := UInt256.ofNat 7039, memory := v89, stack := n0 :: v88 :: P :: v88 :: v59 :: v86 :: v88 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7047, memory := v89, stack := v92 :: v93 :: v92 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part21Model, v90, v91, v92, v93] using col8part21_run ({s with memory := v89}) (n0) (v88) (P) (v88) (v59) (v86) (v88) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h22 : runInstructions col8part22Program {s with pc := UInt256.ofNat 7047, memory := v89, stack := v92 :: v93 :: v92 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7056, memory := v89, stack := mask :: v92 :: v96 :: v92 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part22Model, v94, v95, v96] using col8part22_run ({s with memory := v89}) (v92) (v93) (v92) (P) (v88) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h23 : runInstructions col8part23Program {s with pc := UInt256.ofNat 7056, memory := v89, stack := mask :: v92 :: v96 :: v92 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7068, memory := v98, stack := v100 :: v99 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part23Model, v97, v98, v99, v100] using col8part23_run ({s with memory := v89}) (mask) (v92) (v96) (v92) (P) (v88) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  have h24 : runInstructions col8part24Program {s with pc := UInt256.ofNat 7068, memory := v98, stack := v100 :: v99 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7069, memory := v98, stack := v101 :: P :: v88 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v36 :: mask :: minv :: rest} := by
    simpa only [col8part24Model, v101] using col8part24_run ({s with memory := v98}) (v100) (v99) (P) (v88) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v36) (mask) (minv) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 (runInstructions_append_some _ _ _ _ _ h19 (runInstructions_append_some _ _ _ _ _ h20 (runInstructions_append_some _ _ _ _ _ h21 (runInstructions_append_some _ _ _ _ _ h22 (runInstructions_append_some _ _ _ _ _ h23 h24))))))))))))))))))))))))

#print axioms col8_raw_run

def col8Model (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 768
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := MachineState.readWord s.memory 992
  let v5 : UInt256 := MachineState.readWord s.memory 800
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 960
  let v9 : UInt256 := MachineState.readWord s.memory 832
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := MachineState.readWord s.memory 928
  let v13 : UInt256 := MachineState.readWord s.memory 864
  let v14 : UInt256 := UInt256.mulMod v13 v12 P
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := MachineState.readWord s.memory 992
  let v17 : UInt256 := MachineState.readWord s.memory 800
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v3
  let v20 : UInt256 := MachineState.readWord s.memory 960
  let v21 : UInt256 := MachineState.readWord s.memory 832
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v19
  let v24 : UInt256 := MachineState.readWord s.memory 928
  let v25 : UInt256 := MachineState.readWord s.memory 864
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v23
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := v15 + v15
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v28
  let v32 : UInt256 := MachineState.readWord s.memory 896
  let v33 : UInt256 := UInt256.mulMod v32 v32 P
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := MachineState.readWord s.memory 1056
  let v36 : UInt256 := UInt256.mulMod n8 v35 P
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := MachineState.readWord s.memory 1088
  let v39 : UInt256 := UInt256.mulMod n7 v38 P
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := MachineState.readWord s.memory 1120
  let v42 : UInt256 := UInt256.mulMod n6 v41 P
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := MachineState.readWord s.memory 1152
  let v45 : UInt256 := UInt256.mulMod n5 v44 P
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := MachineState.readWord s.memory 1184
  let v48 : UInt256 := UInt256.mulMod n4 v47 P
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := MachineState.readWord s.memory 1216
  let v51 : UInt256 := UInt256.mulMod n3 v50 P
  let v52 : UInt256 := v51 + v49
  let v53 : UInt256 := MachineState.readWord s.memory 1248
  let v54 : UInt256 := UInt256.mulMod n2 v53 P
  let v55 : UInt256 := v54 + v52
  let v56 : UInt256 := MachineState.readWord s.memory 1280
  let v57 : UInt256 := UInt256.mulMod n1 v56 P
  let v58 : UInt256 := v57 + v55
  let v59 : UInt256 := MachineState.readWord s.memory 896
  let v60 : UInt256 := v59 * v59
  let v61 : UInt256 := v60 + v31
  let v62 : UInt256 := MachineState.readWord s.memory 1056
  let v63 : UInt256 := n8 * v62
  let v64 : UInt256 := v63 + v61
  let v65 : UInt256 := MachineState.readWord s.memory 1088
  let v66 : UInt256 := n7 * v65
  let v67 : UInt256 := v66 + v64
  let v68 : UInt256 := MachineState.readWord s.memory 1120
  let v69 : UInt256 := n6 * v68
  let v70 : UInt256 := v69 + v67
  let v71 : UInt256 := MachineState.readWord s.memory 1152
  let v72 : UInt256 := n5 * v71
  let v73 : UInt256 := v72 + v70
  let v74 : UInt256 := MachineState.readWord s.memory 1184
  let v75 : UInt256 := n4 * v74
  let v76 : UInt256 := v75 + v73
  let v77 : UInt256 := MachineState.readWord s.memory 1216
  let v78 : UInt256 := n3 * v77
  let v79 : UInt256 := v78 + v76
  let v80 : UInt256 := MachineState.readWord s.memory 1248
  let v81 : UInt256 := n2 * v80
  let v82 : UInt256 := v81 + v79
  let v83 : UInt256 := MachineState.readWord s.memory 1280
  let v84 : UInt256 := n1 * v83
  let v85 : UInt256 := v84 + v82
  let v86 : UInt256 := UInt256.land mask v85
  let v87 : UInt256 := minv * v86
  let v88 : UInt256 := UInt256.land (UInt256.ofNat 79228162514264337593543950335) v87
  let v89 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v88.toNat 32) 1312
  let v90 : UInt256 := n0 * v88
  let v91 : UInt256 := v90 + v85
  let v92 : UInt256 := UInt256.mulMod n0 v88 P
  let v93 : UInt256 := v92 + v58
  let v97 : UInt256 := UInt256.addMod v93 (UInt256.lnot v91) P
  let v98 : UInt256 := UInt256.shiftRight v97 (UInt256.ofNat 5)
  let v99 : UInt256 := UInt256.land mask v91
  let v100 : ByteArray := MachineState.writeBytes v89 (Data.Bytes.natToBytesPadded v99.toNat 32) 1344
  let v101 : UInt256 := UInt256.shiftLeft v98 (UInt256.ofNat 12)
  let v102 : UInt256 := UInt256.shiftRight v91 (UInt256.ofNat 244)
  let v103 : UInt256 := v102 + v101
  {s with pc := UInt256.ofNat 7069, memory := v100, stack := v103 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col8_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1))
    (h8 : UInt256.shiftRight (MachineState.readWord s.memory 0) (UInt256.ofNat 160) = n8) :
    runInstructions col8Program (cachedState 8
      {s with pc := UInt256.ofNat 6789, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 9 (col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  change runInstructions col8Program
    {s with pc := UInt256.ofNat 6789, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: (MachineState.readWord s.memory 1056) :: mask :: minv :: rest} = _
  rw [col8_raw_run s carry P n0 n1 n2 n3 n4 n5 n6 n7 (MachineState.readWord s.memory 1056) mask minv rest hcap hact]
  apply congrArg some
  subst mask
  simp only [col8RawModel, col8Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm, h8]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint, h8]

#print axioms col8_run

theorem col8_read0 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col8Model, read_store_disjoint]

theorem col8_read224 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col8Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

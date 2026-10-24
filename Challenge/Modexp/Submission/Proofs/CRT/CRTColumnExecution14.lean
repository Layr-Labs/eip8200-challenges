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

def col14part0Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 960,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def col14part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 960
  let v2 : UInt256 := v0 * v1
  {s with pc := UInt256.ofNat 7903, memory := s.memory, stack := v2 :: v1 :: x1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem col14part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part0Program {s with pc := UInt256.ofNat 7891, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (col14part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
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
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  simp [col14part0Program, col14part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha960, hf960, ha1024, hf1024]

#print axioms col14part0_run

def col14part1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD]

def col14part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := UInt256.mulMod x3 x1 x2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := x4 + v2
  {s with pc := UInt256.ofNat 7911, memory := s.memory, stack := v3 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem col14part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part1Program {s with pc := UInt256.ofNat 7903, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (col14part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
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
  simp [col14part1Program, col14part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

#print axioms col14part1_run

def col14part2Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 992,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def col14part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 992
  let v2 : UInt256 := v1 * v1
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := rest.headD (UInt256.ofNat 0)
  {s with pc := UInt256.ofNat 7921, memory := s.memory, stack := v4 :: v3 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col14part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part2Program {s with pc := UInt256.ofNat 7911, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col14part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [col14part2Program, col14part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha992, hf992, ha1248, hf1248]

#print axioms col14part2_run

def col14part3Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def col14part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x12 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x14
  let v3 : UInt256 := x11 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7928, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col14part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part3Program {s with pc := UInt256.ofNat 7921, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col14part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col14part3Program, col14part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1280, hf1280]

#print axioms col14part3_run

def col14part4Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 2 992,
   .op .MLOAD]

def col14part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x9 * x3
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 992
  {s with pc := UInt256.ofNat 7938, memory := s.memory, stack := v2 :: x2 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col14part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part4Program {s with pc := UInt256.ofNat 7928, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col14part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [col14part4Program, col14part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha992, hf992]

#print axioms col14part4_run

def col14part5Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD]

def col14part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v3 : UInt256 := UInt256.mulMod x13 v2 x4
  {s with pc := UInt256.ofNat 7945, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col14part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part5Program {s with pc := UInt256.ofNat 7938, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col14part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [col14part5Program, col14part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha1248, hf1248]

#print axioms col14part5_run

def col14part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def col14part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x14
  let v2 : UInt256 := UInt256.mulMod x11 v1 x3
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 7952, memory := s.memory, stack := x3 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col14part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part6Program {s with pc := UInt256.ofNat 7945, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col14part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col14part6Program, col14part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha1280, hf1280]

#print axioms col14part6_run

def col14part7Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Swap ⟨1, by decide⟩)]

def col14part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x4 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.lnot x2
  {s with pc := UInt256.ofNat 7960, memory := s.memory, stack := v1 :: v2 :: x3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col14part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part7Program {s with pc := UInt256.ofNat 7952, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col14part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col14part7Program, col14part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17]

#print axioms col14part7_run

def col14part8Program : List Instr :=
  [.op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 2 1536,
   .op .MSTORE]

def col14part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.addMod x0 x1 x2
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := UInt256.land x14 x3
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 1536
  {s with pc := UInt256.ofNat 7971, memory := v3, stack := v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col14part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part8Program {s with pc := UInt256.ofNat 7960, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col14part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  have ha1536 : (1536 : UInt256).toNat = 1536 := rfl
  have hf1536 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1536 32 (by decide) (by norm_num) hact
  simp [col14part8Program, col14part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, ha1536, hf1536]

#print axioms col14part8_run

def col14part9Program : List Instr :=
  [.push 1 12,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 244,
   .op .SHR,
   .op .ADD]

def col14part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 12)
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 244)
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7979, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem col14part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14part9Program {s with pc := UInt256.ofNat 7971, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (col14part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
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
  simp [col14part9Program, col14part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

#print axioms col14part9_run

def col14Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 960,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 992,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 2 992,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
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
   .push 2 1536,
   .op .MSTORE,
   .push 1 12,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 244,
   .op .SHR,
   .op .ADD]

def col14RawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 960
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := UInt256.mulMod v0 v1 P
  let v5 : UInt256 := v4 + v4
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v3
  let v8 : UInt256 := MachineState.readWord s.memory 992
  let v9 : UInt256 := v8 * v8
  let v10 : UInt256 := v9 + v7
  let v11 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v12 : UInt256 := n8 * v11
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := minv
  let v15 : UInt256 := n7 * v14
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := n6 * n0
  let v18 : UInt256 := v17 + v16
  let v19 : UInt256 := MachineState.readWord s.memory 992
  let v20 : UInt256 := UInt256.mulMod v19 v19 P
  let v21 : UInt256 := v20 + v6
  let v22 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v23 : UInt256 := UInt256.mulMod n8 v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := minv
  let v26 : UInt256 := UInt256.mulMod n7 v25 P
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := UInt256.mulMod n6 n0 P
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := UInt256.lnot v18
  let v31 : UInt256 := UInt256.addMod v29 v30 P
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 5)
  let v33 : UInt256 := UInt256.land mask v18
  let v34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v33.toNat 32) 1536
  let v35 : UInt256 := UInt256.shiftLeft v32 (UInt256.ofNat 12)
  let v36 : UInt256 := UInt256.shiftRight v18 (UInt256.ofNat 244)
  let v37 : UInt256 := v36 + v35
  {s with pc := UInt256.ofNat 7979, memory := v34, stack := v37 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col14_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col14Program {s with pc := UInt256.ofNat 7891, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col14RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 960
  let v2 : UInt256 := v0 * v1
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := UInt256.mulMod v0 v1 P
  let v5 : UInt256 := v4 + v4
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v3
  let v8 : UInt256 := MachineState.readWord s.memory 992
  let v9 : UInt256 := v8 * v8
  let v10 : UInt256 := v9 + v7
  let v11 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v12 : UInt256 := n8 * v11
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := minv
  let v15 : UInt256 := n7 * v14
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := n6 * n0
  let v18 : UInt256 := v17 + v16
  let v19 : UInt256 := MachineState.readWord s.memory 992
  let v20 : UInt256 := UInt256.mulMod v19 v19 P
  let v21 : UInt256 := v20 + v6
  let v22 : UInt256 := rest.headD (UInt256.ofNat 0)
  let v23 : UInt256 := UInt256.mulMod n8 v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := minv
  let v26 : UInt256 := UInt256.mulMod n7 v25 P
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := UInt256.mulMod n6 n0 P
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := UInt256.lnot v18
  let v31 : UInt256 := UInt256.addMod v29 v30 P
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 5)
  let v33 : UInt256 := UInt256.land mask v18
  let v34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v33.toNat 32) 1536
  let v35 : UInt256 := UInt256.shiftLeft v32 (UInt256.ofNat 12)
  let v36 : UInt256 := UInt256.shiftRight v18 (UInt256.ofNat 244)
  let v37 : UInt256 := v36 + v35
  have h0 : runInstructions col14part0Program {s with pc := UInt256.ofNat 7891, memory := s.memory, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7903, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part0Model, v0, v1, v2] using col14part0_run (s) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col14part1Program {s with pc := UInt256.ofNat 7903, memory := s.memory, stack := v2 :: v1 :: P :: v0 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7911, memory := s.memory, stack := v6 :: v3 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part1Model, v3, v4, v5, v6] using col14part1_run (s) (v2) (v1) (P) (v0) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h2 : runInstructions col14part2Program {s with pc := UInt256.ofNat 7911, memory := s.memory, stack := v6 :: v3 :: carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7921, memory := s.memory, stack := v11 :: v10 :: v6 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part2Model, v7, v8, v9, v10, v11] using col14part2_run (s) (v6) (v3) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hrest hact
  have h3 : runInstructions col14part3Program {s with pc := UInt256.ofNat 7921, memory := s.memory, stack := v11 :: v10 :: v6 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7928, memory := s.memory, stack := v16 :: v6 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part3Model, v12, v13, v14, v15, v16] using col14part3_run (s) (v11) (v10) (v6) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h4 : runInstructions col14part4Program {s with pc := UInt256.ofNat 7928, memory := s.memory, stack := v16 :: v6 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7938, memory := s.memory, stack := v19 :: P :: v6 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part4Model, v17, v18, v19] using col14part4_run (s) (v16) (v6) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h5 : runInstructions col14part5Program {s with pc := UInt256.ofNat 7938, memory := s.memory, stack := v19 :: P :: v6 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7945, memory := s.memory, stack := v23 :: v21 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part5Model, v20, v21, v22, v23] using col14part5_run (s) (v19) (P) (v6) (v18) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hrest hact
  have h6 : runInstructions col14part6Program {s with pc := UInt256.ofNat 7945, memory := s.memory, stack := v23 :: v21 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7952, memory := s.memory, stack := P :: v27 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part6Model, v24, v25, v26, v27] using col14part6_run (s) (v23) (v21) (v18) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h7 : runInstructions col14part7Program {s with pc := UInt256.ofNat 7952, memory := s.memory, stack := P :: v27 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7960, memory := s.memory, stack := v29 :: v30 :: P :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part7Model, v28, v29, v30] using col14part7_run (s) (P) (v27) (v18) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h8 : runInstructions col14part8Program {s with pc := UInt256.ofNat 7960, memory := s.memory, stack := v29 :: v30 :: P :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7971, memory := v34, stack := v32 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part8Model, v31, v32, v33, v34] using col14part8_run (s) (v29) (v30) (P) (v18) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h9 : runInstructions col14part9Program {s with pc := UInt256.ofNat 7971, memory := v34, stack := v32 :: v18 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 7979, memory := v34, stack := v37 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col14part9Model, v35, v36, v37] using col14part9_run ({s with memory := v34}) (v32) (v18) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  let final : State := {s with pc := UInt256.ofNat 7979, memory := v34, stack := v37 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}
  change runInstructions col14Program
    {s with pc := UInt256.ofNat 7891, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some final
  simpa [col14Program, col14part0Program, col14part1Program, col14part2Program,
    col14part3Program, col14part4Program, col14part5Program, col14part6Program,
    col14part7Program, col14part8Program, col14part9Program] using
    (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))

#print axioms col14_raw_run

def col14Model (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := MachineState.readWord s.memory 960
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := v3 + v3
  let v5 : UInt256 := v2 + v2
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v4
  let v8 : UInt256 := MachineState.readWord s.memory 992
  let v9 : UInt256 := UInt256.mulMod v8 v8 P
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := MachineState.readWord s.memory 1248
  let v12 : UInt256 := UInt256.mulMod n8 v11 P
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := MachineState.readWord s.memory 1280
  let v15 : UInt256 := UInt256.mulMod n7 v14 P
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := MachineState.readWord s.memory 1312
  let v18 : UInt256 := UInt256.mulMod n6 v17 P
  let v19 : UInt256 := v18 + v16
  let v20 : UInt256 := MachineState.readWord s.memory 992
  let v21 : UInt256 := v20 * v20
  let v22 : UInt256 := v21 + v7
  let v23 : UInt256 := MachineState.readWord s.memory 1248
  let v24 : UInt256 := n8 * v23
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := MachineState.readWord s.memory 1280
  let v27 : UInt256 := n7 * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 1312
  let v30 : UInt256 := n6 * v29
  let v31 : UInt256 := v30 + v28
  let v35 : UInt256 := UInt256.addMod v19 (UInt256.lnot v31) P
  let v36 : UInt256 := UInt256.shiftRight v35 (UInt256.ofNat 5)
  let v37 : UInt256 := UInt256.land mask v31
  let v38 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v37.toNat 32) 1536
  let v39 : UInt256 := UInt256.shiftLeft v36 (UInt256.ofNat 12)
  let v40 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 244)
  let v41 : UInt256 := v40 + v39
  {s with pc := UInt256.ofNat 7979, memory := v38, stack := v41 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col14_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1)) :
    runInstructions col14Program (cachedState 14
      {s with pc := UInt256.ofNat 7891, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 15 (col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  rcases rest with _ | ⟨slot, rest⟩
  · simp at hrest
  simp only [List.length_cons] at hcap hrest
  change runInstructions col14Program
    {s with pc := UInt256.ofNat 7891, stack := carry :: P :: (MachineState.readWord s.memory 1312) :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: (MachineState.readWord s.memory 1280) :: (MachineState.readWord s.memory 1248) :: rest} = _
  rw [col14_raw_run s carry P (MachineState.readWord s.memory 1312) n1 n2 n3 n4 n5 n6 n7 n8 mask (MachineState.readWord s.memory 1280) ((MachineState.readWord s.memory 1248) :: rest) (by simp; omega) (by simp) hact]
  apply congrArg some
  subst mask
  simp only [col14RawModel, col14Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint]

#print axioms col14_run

theorem col14_read0 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col14Model, read_store_disjoint]

theorem col14_read224 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col14Model, read_store_disjoint]

theorem col14_read2720 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 2720 =
      MachineState.readWord s.memory 2720 := by
  simp (disch := omega) [col14Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

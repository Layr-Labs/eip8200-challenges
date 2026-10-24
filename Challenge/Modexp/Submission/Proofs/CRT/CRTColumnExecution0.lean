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

def col0part0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨2, by decide⟩)]

def col0part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := v0 * v0
  {s with pc := UInt256.ofNat 5868, memory := s.memory, stack := v0 :: v0 :: x0 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem col0part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col0part0Program {s with pc := UInt256.ofNat 5858, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (col0part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
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
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [col0part0Program, col0part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, ha768, hf768]

#print axioms col0part0_run

def col0part1Program : List Instr :=
  [.op .MULMOD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩)]

def col0part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := x3 * x15
  {s with pc := UInt256.ofNat 5876, memory := s.memory, stack := x14 :: v1 :: x5 :: x4 :: v0 :: x4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem col0part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col0part1Program {s with pc := UInt256.ofNat 5868, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (col0part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [col0part1Program, col0part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

#print axioms col0part1_run

def col0part2Program : List Instr :=
  [.op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1056,
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩),
   .op .POP,
   .op .MULMOD]

def col0part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 1056
  let v2 : UInt256 := UInt256.mulMod v0 x2 x3
  {s with pc := UInt256.ofNat 5886, memory := v1, stack := v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: v0 :: x16 :: x17 :: rest}

theorem col0part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col0part2Program {s with pc := UInt256.ofNat 5876, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (col0part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
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
  have ha1056 : (1056 : UInt256).toNat = 1056 := rfl
  have hf1056 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1056 32 (by decide) (by norm_num) hact
  simp [col0part2Program, col0part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, ha1056, hf1056]

#print axioms col0part2_run

def col0part3Program : List Instr :=
  [.op .ADD,
   .push 1 128,
   .op .MULMOD]

def col0part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v0 x2
  {s with pc := UInt256.ofNat 5890, memory := s.memory, stack := v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col0part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col0part3Program {s with pc := UInt256.ofNat 5886, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col0part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  simp [col0part3Program, col0part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]

#print axioms col0part3_run

def col0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1056,
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 1 128,
   .op .MULMOD]

def col0RawModel (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := UInt256.mulMod v0 v0 P
  let v3 : UInt256 := v1 * minv
  let v4 : UInt256 := UInt256.land mask v3
  let v5 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v4.toNat 32) 1056
  let v6 : UInt256 := UInt256.mulMod v4 n0 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v7 P
  {s with pc := UInt256.ofNat 5890, memory := v5, stack := v8 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v4 :: mask :: minv :: rest}

theorem col0_raw_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col0Program {s with pc := UInt256.ofNat 5858, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col0RawModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := UInt256.mulMod v0 v0 P
  let v3 : UInt256 := v1 * minv
  let v4 : UInt256 := UInt256.land mask v3
  let v5 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v4.toNat 32) 1056
  let v6 : UInt256 := UInt256.mulMod v4 n0 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := UInt256.mulMod (UInt256.ofNat 128) v7 P
  have h0 : runInstructions col0part0Program {s with pc := UInt256.ofNat 5858, memory := s.memory, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 5868, memory := s.memory, stack := v0 :: v0 :: P :: v1 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col0part0Model, v0, v1] using col0part0_run (s) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col0part1Program {s with pc := UInt256.ofNat 5868, memory := s.memory, stack := v0 :: v0 :: P :: v1 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 5876, memory := s.memory, stack := mask :: v3 :: n0 :: P :: v2 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col0part1Model, v2, v3] using col0part1_run (s) (v0) (v0) (P) (v1) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h2 : runInstructions col0part2Program {s with pc := UInt256.ofNat 5876, memory := s.memory, stack := mask :: v3 :: n0 :: P :: v2 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 5886, memory := v5, stack := v6 :: v2 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v4 :: mask :: minv :: rest} := by
    simpa only [col0part2Model, v4, v5, v6] using col0part2_run (s) (mask) (v3) (n0) (P) (v2) (P) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h3 : runInstructions col0part3Program {s with pc := UInt256.ofNat 5886, memory := v5, stack := v6 :: v2 :: P :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v4 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 5890, memory := v5, stack := v8 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: v4 :: mask :: minv :: rest} := by
    simpa only [col0part3Model, v7, v8] using col0part3_run ({s with memory := v5}) (v6) (v2) (P) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (v4) (mask) (minv) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 h3)))

#print axioms col0_raw_run

def col0Model (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := MachineState.readWord s.memory 768
  let v3 : UInt256 := UInt256.mulMod v2 v2 P
  let v4 : UInt256 := UInt256.land mask v1
  let v5 : UInt256 := minv * v4
  let v6 : UInt256 := UInt256.land mask v5
  let v7 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v6.toNat 32) 1056
  let v8 : UInt256 := n0 * v6
  let v9 : UInt256 := v8 + v1
  let v10 : UInt256 := UInt256.mulMod n0 v6 P
  let v11 : UInt256 := v10 + v3
  let v19 : UInt256 := UInt256.mulMod v11 (UInt256.ofNat 128) P
  {s with pc := UInt256.ofNat 5890, memory := v7, stack := v19 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col0_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1)) :
    runInstructions col0Program (cachedState 0
      {s with pc := UInt256.ofNat 5858, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 1 (col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  change runInstructions col0Program
    {s with pc := UInt256.ofNat 5858, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = _
  rw [col0_raw_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap hact]
  apply congrArg some
  subst mask
  simp only [col0RawModel, col0Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint]

#print axioms col0_run

theorem col0_read0 (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col0Model, read_store_disjoint]

theorem col0_read224 (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col0Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

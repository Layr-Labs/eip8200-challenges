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

def col16part0Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩)]

def col16part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 8054, memory := s.memory, stack := x11 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem col16part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col16part0Program {s with pc := UInt256.ofNat 8043, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (col16part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
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
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  simp [col16part0Program, col16part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, ha224, hf224, ha1024, hf1024]

#print axioms col16part0_run

def col16part1Program : List Instr :=
  [.op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MSTORE]

def col16part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : UInt256 := x12 * x4
  let v2 : UInt256 := v1 + x2
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 1600
  {s with pc := UInt256.ofNat 8063, memory := v3, stack := x3 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem col16part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col16part1Program {s with pc := UInt256.ofNat 8054, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (col16part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
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
  have ha1600 : (1600 : UInt256).toNat = 1600 := rfl
  have hf1600 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [col16part1Program, col16part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, ha1600, hf1600]

#print axioms col16part1_run

def col16PrefixProgram : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MSTORE]

def col16RawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := v1 + carry
  let v3 : UInt256 := MachineState.readWord s.memory 224
  let v4 : UInt256 := UInt256.land mask v3
  let v5 : UInt256 := n8 * n0
  let v6 : UInt256 := v5 + v2
  let v7 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v6.toNat 32) 1600
  {s with pc := UInt256.ofNat 8063, memory := v7, stack := P :: v4 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col16_prefix_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col16PrefixProgram {s with pc := UInt256.ofNat 8043, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (col16RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := v1 + carry
  let v3 : UInt256 := MachineState.readWord s.memory 224
  let v4 : UInt256 := UInt256.land mask v3
  let v5 : UInt256 := n8 * n0
  let v6 : UInt256 := v5 + v2
  let v7 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v6.toNat 32) 1600
  have h0 : runInstructions col16part0Program {s with pc := UInt256.ofNat 8043, memory := s.memory, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 8054, memory := s.memory, stack := mask :: v3 :: v2 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col16part0Model, v0, v1, v2, v3] using col16part0_run (s) (carry) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  have h1 : runInstructions col16part1Program {s with pc := UInt256.ofNat 8054, memory := s.memory, stack := mask :: v3 :: v2 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some {s with pc := UInt256.ofNat 8063, memory := v7, stack := P :: v4 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} := by
    simpa only [col16part1Model, v4, v5, v6, v7] using col16part1_run (s) (mask) (v3) (v2) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 h1)

#print axioms col16_prefix_raw_run

def col16RestoreProgram : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .push 0 0,
   .op (.Swap ⟨12, by decide⟩),
   .op .POP]

def col16Program : List Instr := col16PrefixProgram ++ col16RestoreProgram

def col16RestoredRawModel (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask q7 : UInt256)
    (rest : List UInt256) : State :=
  let t := col16RawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask q7 rest
  let u := {t with stack := t.stack.set 11 (MachineState.readWord t.memory 2720)}
  let v := {u with stack := u.stack.set 12 (UInt256.ofNat 0)}
  {v with pc := UInt256.ofNat 8072}

theorem col16_raw_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask q7 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions col16Program {s with pc := UInt256.ofNat 8043, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: q7 :: rest} =
      some (col16RestoredRawModel s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask q7 rest) := by
  rcases rest with _ | ⟨slot, rest⟩
  · simp at hrest
  simp only [List.length_cons] at hcap hrest
  rw [col16Program, runInstructions_append,
    col16_prefix_raw_run s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask q7
      (slot :: rest) (by simp; omega) hact]
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
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by rfl
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := HistoricalSearch.CRTMemoryBounds.activeWords_fix
    s 2720 32 (by decide) (by norm_num) hact
  simp [col16RestoreProgram, col16RestoredRawModel, col16RawModel, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, List.exchange,
    read_store_disjoint,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hz, ha2720, hf2720]

#print axioms col16_raw_run

def col16Model (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := v1 + carry
  let v3 : UInt256 := MachineState.readWord s.memory 1312
  let v4 : UInt256 := n8 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 1600
  {s with pc := UInt256.ofNat 8072, memory := v6, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}

theorem col16_run (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrest : 1 ≤ rest.length) (hzero : rest.headD (UInt256.ofNat 0) = UInt256.ofNat 0)
    (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1))
    (h0 : UInt256.land mask (MachineState.readWord s.memory 224) = n0)
    (hminv : MachineState.readWord s.memory 2720 = minv) :
    runInstructions col16Program (cachedState 16
      {s with pc := UInt256.ofNat 8043, stack := carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest}) =
      some (cachedState 17 (col16Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)) := by
  rcases rest with _ | ⟨slot, rest⟩
  · simp at hrest
  simp only [List.length_cons, List.headD_cons] at hcap hrest hzero
  subst slot
  change runInstructions col16Program
    {s with pc := UInt256.ofNat 8043, stack := carry :: P :: (MachineState.readWord s.memory 1312) :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: (MachineState.readWord s.memory 1280) :: (MachineState.readWord s.memory 1248) :: rest} = _
  rw [col16_raw_run s carry P (MachineState.readWord s.memory 1312) n1 n2 n3 n4 n5 n6 n7 n8 mask (MachineState.readWord s.memory 1280) ((MachineState.readWord s.memory 1248) :: rest) (by simp; omega) (by simp) hact]
  apply congrArg some
  subst mask
  simp only [col16RestoredRawModel, col16RawModel, col16Model,
    HistoricalSearch.CRTMaskElision.mask244_mul_mask244,
    HistoricalSearch.CRTMaskElision.mask96_mul_mask244,
    mulMod_comm, HistoricalSearch.WordCancellation.mul_comm, h0]
  simp (disch := omega) [cachedState,
    readWord_writeWord, read_store_disjoint, h0, hminv]

#print axioms col16_run

theorem col16_read0 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col16Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 0 =
      MachineState.readWord s.memory 0 := by
  simp (disch := omega) [col16Model, read_store_disjoint]

theorem col16_read224 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col16Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 224 =
      MachineState.readWord s.memory 224 := by
  simp (disch := omega) [col16Model, read_store_disjoint]

theorem col16_read2720 (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    MachineState.readWord (col16Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).memory 2720 =
      MachineState.readWord s.memory 2720 := by
  simp (disch := omega) [col16Model, read_store_disjoint]

end HistoricalSearch.GeneratedColumns

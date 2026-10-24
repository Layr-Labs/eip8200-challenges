import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace HistoricalSearch.GeneratedColumns
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

/-- Keep the semantic model in the inherited subtraction normal form while
executing no zero addition. This rewrite avoids reducing the byte-array model. -/
theorem normalizer_add_zero (w : UInt256) : w + UInt256.ofNat 0 = w := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  simp only [Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt w.val.isLt


def normalizepart0Program : List Instr :=
  [.op .JUMPDEST,
   .push 2 1344,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩)]

def normalizepart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1344
  let v1 : UInt256 := v0 + (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 768
  {s with pc := UInt256.ofNat 11024, memory := s.memory, stack := v1 :: v2 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem normalizepart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart0Program {s with pc := UInt256.ofNat 11014, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (normalizepart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart0Program, normalizepart0Model, normalizer_add_zero, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha1344, hf1344]


def normalizepart1Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE]

def normalizepart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x1 x0
  let v1 : UInt256 := x1 - x2
  let v2 : UInt256 := UInt256.land x13 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 768
  {s with pc := UInt256.ofNat 11035, memory := v3, stack := v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem normalizepart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart1Program {s with pc := UInt256.ofNat 11024, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (normalizepart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart1Program, normalizepart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768]


def normalizepart2Program : List Instr :=
  [.push 2 1376,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩)]

def normalizepart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1376
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.lt x4 v1
  {s with pc := UInt256.ofNat 11045, memory := s.memory, stack := v1 :: x4 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem normalizepart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart2Program {s with pc := UInt256.ofNat 11035, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (normalizepart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart2Program, normalizepart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1376, hf1376]


def normalizepart3Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD]

def normalizepart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 - x0
  let v1 : UInt256 := UInt256.land x13 v0
  let v2 : UInt256 := x3 + x2
  {s with pc := UInt256.ofNat 11053, memory := s.memory, stack := v2 :: x3 :: x4 :: x5 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem normalizepart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart3Program {s with pc := UInt256.ofNat 11045, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (normalizepart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, normalizepart3Program, normalizepart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def normalizepart4Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩)]

def normalizepart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x5 x0
  let v1 : UInt256 := x5 - x0
  {s with pc := UInt256.ofNat 11061, memory := s.memory, stack := x11 :: v1 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem normalizepart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart4Program {s with pc := UInt256.ofNat 11053, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (normalizepart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, normalizepart4Program, normalizepart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def normalizepart5Program : List Instr :=
  [.op .AND,
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .op (.Dup ⟨13, by decide⟩),
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩)]

def normalizepart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : UInt256 := x15 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 11070, memory := s.memory, stack := v1 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: v0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem normalizepart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart5Program {s with pc := UInt256.ofNat 11061, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (normalizepart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart5Program, normalizepart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32]


def normalizepart6Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 32,
   .op .MSTORE]

def normalizepart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x1 x0
  let v1 : UInt256 := x1 - x2
  let v2 : UInt256 := UInt256.land x13 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 32
  {s with pc := UInt256.ofNat 11080, memory := v3, stack := v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem normalizepart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart6Program {s with pc := UInt256.ofNat 11070, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (normalizepart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart6Program, normalizepart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32]


def normalizepart7Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩)]

def normalizepart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 + x0
  let v1 : UInt256 := MachineState.readWord s.memory 64
  let v2 : UInt256 := UInt256.lt v1 v0
  {s with pc := UInt256.ofNat 11089, memory := s.memory, stack := v0 :: v1 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem normalizepart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart7Program {s with pc := UInt256.ofNat 11080, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (normalizepart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart7Program, normalizepart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]


def normalizepart8Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 64,
   .op .MSTORE,
   .op (.Dup ⟨6, by decide⟩),
   .op .ADD]

def normalizepart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 - x0
  let v1 : UInt256 := UInt256.land x13 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 64
  let v3 : UInt256 := x8 + x2
  {s with pc := UInt256.ofNat 11098, memory := v2, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem normalizepart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart8Program {s with pc := UInt256.ofNat 11089, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (normalizepart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart8Program, normalizepart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]


def normalizepart9Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB]

def normalizepart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := UInt256.lt v0 x0
  let v2 : UInt256 := v0 - x0
  {s with pc := UInt256.ofNat 11107, memory := s.memory, stack := v2 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem normalizepart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart9Program {s with pc := UInt256.ofNat 11098, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (normalizepart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart9Program, normalizepart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]


def normalizepart10Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 96,
   .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def normalizepart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x12 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 96
  let v2 : UInt256 := x3 + x1
  let v3 : UInt256 := MachineState.readWord v1 128
  {s with pc := UInt256.ofNat 11117, memory := v1, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem normalizepart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart10Program {s with pc := UInt256.ofNat 11107, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (normalizepart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart10Program, normalizepart10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha128, hf128]


def normalizepart11Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND]

def normalizepart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x0 x1
  let v1 : UInt256 := x0 - x1
  let v2 : UInt256 := UInt256.land x12 v1
  {s with pc := UInt256.ofNat 11125, memory := s.memory, stack := v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem normalizepart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart11Program {s with pc := UInt256.ofNat 11117, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (normalizepart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, normalizepart11Program, normalizepart11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def normalizepart12Program : List Instr :=
  [.push 1 128,
   .op .MSTORE,
   .op (.Dup ⟨7, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩)]

def normalizepart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 128
  let v1 : UInt256 := x8 + x1
  let v2 : UInt256 := MachineState.readWord v0 160
  {s with pc := UInt256.ofNat 11135, memory := v0, stack := v2 :: v1 :: v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem normalizepart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart12Program {s with pc := UInt256.ofNat 11125, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (normalizepart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart12Program, normalizepart12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha160, hf160]


def normalizepart13Program : List Instr :=
  [.op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 160,
   .op .MSTORE]

def normalizepart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x0 x1
  let v1 : UInt256 := x2 - x3
  let v2 : UInt256 := UInt256.land x14 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 160
  {s with pc := UInt256.ofNat 11144, memory := v3, stack := v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem normalizepart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart13Program {s with pc := UInt256.ofNat 11135, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (normalizepart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart13Program, normalizepart13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def normalizepart14Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def normalizepart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x9 + x0
  {s with pc := UInt256.ofNat 11147, memory := s.memory, stack := x14 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem normalizepart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart14Program {s with pc := UInt256.ofNat 11144, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (normalizepart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, normalizepart14Program, normalizepart14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def normalizepart15Program : List Instr :=
  [.op .SUB,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩)]

def normalizepart15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := MachineState.readWord s.memory 1344
  {s with pc := UInt256.ofNat 11155, memory := s.memory, stack := x13 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: v1 :: x14 :: v0 :: rest}

theorem normalizepart15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizepart15Program {s with pc := UInt256.ofNat 11147, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (normalizepart15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, normalizepart15Program, normalizepart15Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1344, hf1344]


def normalizeProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 1344,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 2 1376,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .op (.Dup ⟨13, by decide⟩),
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 32,
   .op .MSTORE,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 64,
   .op .MSTORE,
   .op (.Dup ⟨6, by decide⟩),
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 96,
   .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 128,
   .op .MSTORE,
   .op (.Dup ⟨7, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .push 1 160,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩)]

def normalizeModel (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1344
  let v1 : UInt256 := v0 + (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 768
  let v3 : UInt256 := UInt256.lt v2 v1
  let v4 : UInt256 := v2 - v1
  let v5 : UInt256 := UInt256.land MASK v4
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 768
  let v7 : UInt256 := MachineState.readWord v6 1376
  let v8 : UInt256 := v7 + v3
  let v9 : UInt256 := UInt256.lt a1 v8
  let v10 : UInt256 := a1 - v8
  let v11 : UInt256 := UInt256.land MASK v10
  let v12 : UInt256 := n2 + v9
  let v13 : UInt256 := UInt256.lt a2 v12
  let v14 : UInt256 := a2 - v12
  let v15 : UInt256 := UInt256.land MASK v14
  let v16 : UInt256 := n3 + v13
  let v17 : UInt256 := MachineState.readWord v6 32
  let v18 : UInt256 := UInt256.lt v17 v16
  let v19 : UInt256 := v17 - v16
  let v20 : UInt256 := UInt256.land MASK v19
  let v21 : ByteArray := MachineState.writeBytes v6 (Data.Bytes.natToBytesPadded v20.toNat 32) 32
  let v22 : UInt256 := n4 + v18
  let v23 : UInt256 := MachineState.readWord v21 64
  let v24 : UInt256 := UInt256.lt v23 v22
  let v25 : UInt256 := v23 - v22
  let v26 : UInt256 := UInt256.land MASK v25
  let v27 : ByteArray := MachineState.writeBytes v21 (Data.Bytes.natToBytesPadded v26.toNat 32) 64
  let v28 : UInt256 := n5 + v24
  let v29 : UInt256 := MachineState.readWord v27 96
  let v30 : UInt256 := UInt256.lt v29 v28
  let v31 : UInt256 := v29 - v28
  let v32 : UInt256 := UInt256.land MASK v31
  let v33 : ByteArray := MachineState.writeBytes v27 (Data.Bytes.natToBytesPadded v32.toNat 32) 96
  let v34 : UInt256 := n6 + v30
  let v35 : UInt256 := MachineState.readWord v33 128
  let v36 : UInt256 := UInt256.lt v35 v34
  let v37 : UInt256 := v35 - v34
  let v38 : UInt256 := UInt256.land MASK v37
  let v39 : ByteArray := MachineState.writeBytes v33 (Data.Bytes.natToBytesPadded v38.toNat 32) 128
  let v40 : UInt256 := n7 + v36
  let v41 : UInt256 := MachineState.readWord v39 160
  let v42 : UInt256 := UInt256.lt v41 v40
  let v43 : UInt256 := v41 - v40
  let v44 : UInt256 := UInt256.land MASK v43
  let v45 : ByteArray := MachineState.writeBytes v39 (Data.Bytes.natToBytesPadded v44.toNat 32) 160
  let v46 : UInt256 := n8 + v42
  let v47 : UInt256 := UInt256.lt a8 v46
  let v48 : UInt256 := a8 - v46
  let v49 : UInt256 := MachineState.readWord v45 1344
  {s with pc := UInt256.ofNat 11155, memory := v45, stack := n0 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: v49 :: n3 :: v48 :: rest}

theorem normalize_run (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normalizeProgram {s with pc := UInt256.ofNat 11014, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} =
      some (normalizeModel s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1344
  let v1 : UInt256 := v0 + (UInt256.ofNat 0)
  let v2 : UInt256 := MachineState.readWord s.memory 768
  let v3 : UInt256 := UInt256.lt v2 v1
  let v4 : UInt256 := v2 - v1
  let v5 : UInt256 := UInt256.land MASK v4
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 768
  let v7 : UInt256 := MachineState.readWord v6 1376
  let v8 : UInt256 := v7 + v3
  let v9 : UInt256 := UInt256.lt a1 v8
  let v10 : UInt256 := a1 - v8
  let v11 : UInt256 := UInt256.land MASK v10
  let v12 : UInt256 := n2 + v9
  let v13 : UInt256 := UInt256.lt a2 v12
  let v14 : UInt256 := a2 - v12
  let v15 : UInt256 := UInt256.land MASK v14
  let v16 : UInt256 := n3 + v13
  let v17 : UInt256 := MachineState.readWord v6 32
  let v18 : UInt256 := UInt256.lt v17 v16
  let v19 : UInt256 := v17 - v16
  let v20 : UInt256 := UInt256.land MASK v19
  let v21 : ByteArray := MachineState.writeBytes v6 (Data.Bytes.natToBytesPadded v20.toNat 32) 32
  let v22 : UInt256 := n4 + v18
  let v23 : UInt256 := MachineState.readWord v21 64
  let v24 : UInt256 := UInt256.lt v23 v22
  let v25 : UInt256 := v23 - v22
  let v26 : UInt256 := UInt256.land MASK v25
  let v27 : ByteArray := MachineState.writeBytes v21 (Data.Bytes.natToBytesPadded v26.toNat 32) 64
  let v28 : UInt256 := n5 + v24
  let v29 : UInt256 := MachineState.readWord v27 96
  let v30 : UInt256 := UInt256.lt v29 v28
  let v31 : UInt256 := v29 - v28
  let v32 : UInt256 := UInt256.land MASK v31
  let v33 : ByteArray := MachineState.writeBytes v27 (Data.Bytes.natToBytesPadded v32.toNat 32) 96
  let v34 : UInt256 := n6 + v30
  let v35 : UInt256 := MachineState.readWord v33 128
  let v36 : UInt256 := UInt256.lt v35 v34
  let v37 : UInt256 := v35 - v34
  let v38 : UInt256 := UInt256.land MASK v37
  let v39 : ByteArray := MachineState.writeBytes v33 (Data.Bytes.natToBytesPadded v38.toNat 32) 128
  let v40 : UInt256 := n7 + v36
  let v41 : UInt256 := MachineState.readWord v39 160
  let v42 : UInt256 := UInt256.lt v41 v40
  let v43 : UInt256 := v41 - v40
  let v44 : UInt256 := UInt256.land MASK v43
  let v45 : ByteArray := MachineState.writeBytes v39 (Data.Bytes.natToBytesPadded v44.toNat 32) 160
  let v46 : UInt256 := n8 + v42
  let v47 : UInt256 := UInt256.lt a8 v46
  let v48 : UInt256 := a8 - v46
  let v49 : UInt256 := MachineState.readWord v45 1344
  have h0 : runInstructions normalizepart0Program {s with pc := UInt256.ofNat 11014, memory := s.memory, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11024, memory := s.memory, stack := v1 :: v2 :: v1 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart0Model, v0, v1, v2] using normalizepart0_run (s) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h1 : runInstructions normalizepart1Program {s with pc := UInt256.ofNat 11024, memory := s.memory, stack := v1 :: v2 :: v1 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11035, memory := v6, stack := v3 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart1Model, v3, v4, v5, v6] using normalizepart1_run (s) (v1) (v2) (v1) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h2 : runInstructions normalizepart2Program {s with pc := UInt256.ofNat 11035, memory := v6, stack := v3 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11045, memory := v6, stack := v8 :: a1 :: v9 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart2Model, v7, v8, v9] using normalizepart2_run ({s with memory := v6}) (v3) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h3 : runInstructions normalizepart3Program {s with pc := UInt256.ofNat 11045, memory := v6, stack := v8 :: a1 :: v9 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11053, memory := v6, stack := v12 :: n2 :: n6 :: n4 :: v11 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart3Model, v10, v11, v12] using normalizepart3_run ({s with memory := v6}) (v8) (a1) (v9) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h4 : runInstructions normalizepart4Program {s with pc := UInt256.ofNat 11053, memory := v6, stack := v12 :: n2 :: n6 :: n4 :: v11 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11061, memory := v6, stack := MASK :: v14 :: v13 :: n2 :: n6 :: n4 :: v11 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart4Model, v13, v14] using normalizepart4_run ({s with memory := v6}) (v12) (n2) (n6) (n4) (v11) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h5 : runInstructions normalizepart5Program {s with pc := UInt256.ofNat 11061, memory := v6, stack := MASK :: v14 :: v13 :: n2 :: n6 :: n4 :: v11 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11070, memory := v6, stack := v16 :: v17 :: v16 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart5Model, v15, v16, v17] using normalizepart5_run ({s with memory := v6}) (MASK) (v14) (v13) (n2) (n6) (n4) (v11) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h6 : runInstructions normalizepart6Program {s with pc := UInt256.ofNat 11070, memory := v6, stack := v16 :: v17 :: v16 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11080, memory := v21, stack := v18 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart6Model, v18, v19, v20, v21] using normalizepart6_run ({s with memory := v6}) (v16) (v17) (v16) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h7 : runInstructions normalizepart7Program {s with pc := UInt256.ofNat 11080, memory := v21, stack := v18 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11089, memory := v21, stack := v22 :: v23 :: v24 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart7Model, v22, v23, v24] using normalizepart7_run ({s with memory := v21}) (v18) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h8 : runInstructions normalizepart8Program {s with pc := UInt256.ofNat 11089, memory := v21, stack := v22 :: v23 :: v24 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11098, memory := v27, stack := v28 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart8Model, v25, v26, v27, v28] using normalizepart8_run ({s with memory := v21}) (v22) (v23) (v24) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h9 : runInstructions normalizepart9Program {s with pc := UInt256.ofNat 11098, memory := v27, stack := v28 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11107, memory := v27, stack := v31 :: v30 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart9Model, v29, v30, v31] using normalizepart9_run ({s with memory := v27}) (v28) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h10 : runInstructions normalizepart10Program {s with pc := UInt256.ofNat 11107, memory := v27, stack := v31 :: v30 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11117, memory := v33, stack := v35 :: v34 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart10Model, v32, v33, v34, v35] using normalizepart10_run ({s with memory := v27}) (v31) (v30) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h11 : runInstructions normalizepart11Program {s with pc := UInt256.ofNat 11117, memory := v33, stack := v35 :: v34 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11125, memory := v33, stack := v38 :: v36 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart11Model, v36, v37, v38] using normalizepart11_run ({s with memory := v33}) (v35) (v34) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h12 : runInstructions normalizepart12Program {s with pc := UInt256.ofNat 11125, memory := v33, stack := v38 :: v36 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11135, memory := v39, stack := v41 :: v40 :: v41 :: v40 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart12Model, v39, v40, v41] using normalizepart12_run ({s with memory := v33}) (v38) (v36) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h13 : runInstructions normalizepart13Program {s with pc := UInt256.ofNat 11135, memory := v39, stack := v41 :: v40 :: v41 :: v40 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11144, memory := v45, stack := v42 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart13Model, v42, v43, v44, v45] using normalizepart13_run ({s with memory := v39}) (v41) (v40) (v41) (v40) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h14 : runInstructions normalizepart14Program {s with pc := UInt256.ofNat 11144, memory := v45, stack := v42 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11147, memory := v45, stack := a8 :: v46 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [normalizepart14Model, v46, v47] using normalizepart14_run ({s with memory := v45}) (v42) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  have h15 : runInstructions normalizepart15Program {s with pc := UInt256.ofNat 11147, memory := v45, stack := a8 :: v46 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 11155, memory := v45, stack := n0 :: n2 :: n6 :: n4 :: v11 :: v15 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: v49 :: n3 :: v48 :: rest} := by
    simpa only [normalizepart15Model, v48, v49] using normalizepart15_run ({s with memory := v45}) (a8) (v46) (n2) (n6) (n4) (v11) (v15) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 h15)))))))))))))))


end HistoricalSearch.GeneratedColumns

#print axioms HistoricalSearch.GeneratedColumns.normalize_run

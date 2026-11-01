import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def productColumn19part0Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩)]

def productColumn19part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x1 x2 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 10198, memory := s.memory, stack := x1 :: x2 :: x0 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn19part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn19part0Program {s with pc := UInt256.ofNat 10190, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn19part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn19part0Program, productColumn19part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn19part0_run

def productColumn19part1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def productColumn19part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x12 * x15
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 10206, memory := s.memory, stack := x11 :: x3 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn19part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn19part1Program {s with pc := UInt256.ofNat 10198, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn19part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn19part1Program, productColumn19part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn19part1_run

def productColumn19part2Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def productColumn19part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x14 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.land x13 x2
  {s with pc := UInt256.ofNat 10214, memory := s.memory, stack := v2 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn19part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn19part2Program {s with pc := UInt256.ofNat 10206, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn19part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn19part2Program, productColumn19part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn19part2_run

def productColumn19part3Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .push 6 2048,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD]

def productColumn19part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 - x1
  let v1 : UInt256 := x10 + v0
  let v2 : UInt256 := UInt256.mulMod v1 (UInt256.ofNat 2048) x10
  {s with pc := UInt256.ofNat 10228, memory := s.memory, stack := v2 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn19part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn19part3Program {s with pc := UInt256.ofNat 10214, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn19part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn19part3Program, productColumn19part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]

#print axioms productColumn19part3_run

def productColumn19part4Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .push 1 160,
   .op .MSTORE,
   .op (.Swap ⟨12, by decide⟩)]

def productColumn19part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x1.toNat 32) 160
  {s with pc := UInt256.ofNat 10234, memory := v0, stack := x15 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x0 :: rest}

theorem productColumn19part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn19part4Program {s with pc := UInt256.ofNat 10228, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn19part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn19part4Program, productColumn19part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]

#print axioms productColumn19part4_run

def productColumn19Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .push 6 2048,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .push 1 160,
   .op .MSTORE,
   .op (.Swap ⟨12, by decide⟩)]

def productColumn19Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod word0 word1 word8
  let v1 : UInt256 := v0 + carry
  let v2 : UInt256 := word0 * word1
  let v3 : UInt256 := v2 + carry
  let v4 : UInt256 := word9 * word12
  let v5 : UInt256 := v4 + v3
  let v6 : UInt256 := UInt256.mulMod word9 word12 word8
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.land word11 v5
  let v9 : UInt256 := v7 - v8
  let v10 : UInt256 := word8 + v9
  let v11 : UInt256 := UInt256.mulMod v10 (UInt256.ofNat 2048) word8
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v8.toNat 32) 160
  {s with pc := UInt256.ofNat 10234, memory := v12, stack := word14 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: v11 :: rest}

theorem productColumn19_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn19Program {s with pc := UInt256.ofNat 10190, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} =
      some (productColumn19Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 rest) := by
  let v0 : UInt256 := UInt256.mulMod word0 word1 word8
  let v1 : UInt256 := v0 + carry
  let v2 : UInt256 := word0 * word1
  let v3 : UInt256 := v2 + carry
  let v4 : UInt256 := word9 * word12
  let v5 : UInt256 := v4 + v3
  let v6 : UInt256 := UInt256.mulMod word9 word12 word8
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.land word11 v5
  let v9 : UInt256 := v7 - v8
  let v10 : UInt256 := word8 + v9
  let v11 : UInt256 := UInt256.mulMod v10 (UInt256.ofNat 2048) word8
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v8.toNat 32) 160
  have h0 : runInstructions productColumn19part0Program {s with pc := UInt256.ofNat 10190, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} = some {s with pc := UInt256.ofNat 10198, memory := s.memory, stack := word0 :: word1 :: carry :: v1 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} := by
    simpa only [productColumn19part0Model, v0, v1] using productColumn19part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) rest hcap hact
  have h1 : runInstructions productColumn19part1Program {s with pc := UInt256.ofNat 10198, memory := s.memory, stack := word0 :: word1 :: carry :: v1 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} = some {s with pc := UInt256.ofNat 10206, memory := s.memory, stack := word8 :: v1 :: v5 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} := by
    simpa only [productColumn19part1Model, v2, v3, v4, v5] using productColumn19part1_run (s) (word0) (word1) (carry) (v1) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) rest hcap hact
  have h2 : runInstructions productColumn19part2Program {s with pc := UInt256.ofNat 10206, memory := s.memory, stack := word8 :: v1 :: v5 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} = some {s with pc := UInt256.ofNat 10214, memory := s.memory, stack := v8 :: v8 :: v7 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} := by
    simpa only [productColumn19part2Model, v6, v7, v8] using productColumn19part2_run (s) (word8) (v1) (v5) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) rest hcap hact
  have h3 : runInstructions productColumn19part3Program {s with pc := UInt256.ofNat 10214, memory := s.memory, stack := v8 :: v8 :: v7 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} = some {s with pc := UInt256.ofNat 10228, memory := s.memory, stack := v11 :: v8 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} := by
    simpa only [productColumn19part3Model, v9, v10, v11] using productColumn19part3_run (s) (v8) (v8) (v7) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) rest hcap hact
  have h4 : runInstructions productColumn19part4Program {s with pc := UInt256.ofNat 10228, memory := s.memory, stack := v11 :: v8 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest} = some {s with pc := UInt256.ofNat 10234, memory := v12, stack := word14 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: v11 :: rest} := by
    simpa only [productColumn19part4Model, v12] using productColumn19part4_run (s) (v11) (v8) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))

#print axioms productColumn19_run

end CycleSubmission.Execution

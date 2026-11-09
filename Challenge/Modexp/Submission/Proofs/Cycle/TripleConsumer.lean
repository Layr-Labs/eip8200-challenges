import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace CycleSubmission.TripleConsumer
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open CycleSubmission.Prepared.Arithmetic

def oldp0Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD]

def oldp0Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := q14 * v0
  let v2 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 7077, memory := s.memory, stack := v2 :: v1 :: v0 :: q8 :: q14 :: q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: rest}

theorem oldp0_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldp0Program {s with pc := UInt256.ofNat 7066, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: rest} =
      some (oldp0Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 rest) := by
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [oldp0Program, oldp0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha32, ha160, hf32, hf160]

def oldp1Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD]

def oldp1Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := v0 * q0
  let v2 : UInt256 := v1 + q1
  let v3 : UInt256 := MachineState.readWord s.memory 128
  let v4 : UInt256 := MachineState.readWord s.memory 96
  {s with pc := UInt256.ofNat 7088, memory := s.memory, stack := v4 :: v3 :: v2 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: rest}

theorem oldp1_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldp1Program {s with pc := UInt256.ofNat 7077, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: rest} =
      some (oldp1Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [oldp1Program, oldp1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha64, ha128, ha96, hf64, hf128, hf96]

def oldp2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def oldp2Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := q0 * q1
  let v1 : UInt256 := v0 + q2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := UInt256.mulMod q5 q3 q4
  let v4 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 7098, memory := s.memory, stack := v4 :: q14 :: v3 :: v2 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: rest}

theorem oldp2_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldp2Program {s with pc := UInt256.ofNat 7088, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: rest} =
      some (oldp2Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 rest) := by
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [oldp2Program, oldp2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha160, hf160]

def oldp3Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD]

def oldp3Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := UInt256.mulMod v0 q0 q1
  let v2 : UInt256 := v1 + q2
  let v3 : UInt256 := MachineState.readWord s.memory 128
  let v4 : UInt256 := MachineState.readWord s.memory 96
  {s with pc := UInt256.ofNat 7110, memory := s.memory, stack := v4 :: v3 :: q12 :: v2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: rest}

theorem oldp3_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldp3Program {s with pc := UInt256.ofNat 7098, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: rest} =
      some (oldp3Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [oldp3Program, oldp3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha64, ha128, ha96, hf64, hf128, hf96]

def oldp4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD]

def oldp4Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod q0 q1 q2
  let v1 : UInt256 := v0 + q3
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := q5 + v2
  let v4 : UInt256 := q5 + q4
  {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v4 :: v3 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: rest}

theorem oldp4_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldp4Program {s with pc := UInt256.ofNat 7110, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: rest} =
      some (oldp4Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [oldp4Program, oldp4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]

def oldProgram : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD]

def oldModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := x14 * v0
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := MachineState.readWord s.memory 128
  let v7 : UInt256 := MachineState.readWord s.memory 96
  let v8 : UInt256 := v7 * v6
  let v9 : UInt256 := v8 + v5
  let v10 : UInt256 := v9 + v9
  let v11 : UInt256 := UInt256.mulMod x14 v0 x8
  let v12 : UInt256 := MachineState.readWord s.memory 160
  let v13 : UInt256 := MachineState.readWord s.memory 64
  let v14 : UInt256 := UInt256.mulMod v13 v12 x8
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := MachineState.readWord s.memory 128
  let v17 : UInt256 := MachineState.readWord s.memory 96
  let v18 : UInt256 := UInt256.mulMod v17 v16 x8
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := x0 + v20
  let v22 : UInt256 := x0 + v10
  {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v22 :: v21 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem old_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions oldProgram {s with pc := UInt256.ofNat 7066, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some (oldModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := x14 * v0
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := MachineState.readWord s.memory 128
  let v7 : UInt256 := MachineState.readWord s.memory 96
  let v8 : UInt256 := v7 * v6
  let v9 : UInt256 := v8 + v5
  let v10 : UInt256 := v9 + v9
  let v11 : UInt256 := UInt256.mulMod x14 v0 x8
  let v12 : UInt256 := MachineState.readWord s.memory 160
  let v13 : UInt256 := MachineState.readWord s.memory 64
  let v14 : UInt256 := UInt256.mulMod v13 v12 x8
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := MachineState.readWord s.memory 128
  let v17 : UInt256 := MachineState.readWord s.memory 96
  let v18 : UInt256 := UInt256.mulMod v17 v16 x8
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := x0 + v20
  let v22 : UInt256 := x0 + v10
  have h0 : runInstructions oldp0Program {s with pc := UInt256.ofNat 7066, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7077, memory := s.memory, stack := v2 :: v1 :: v0 :: x8 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [oldp0Model, v0, v1, v2] using oldp0_run s (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h1 : runInstructions oldp1Program {s with pc := UInt256.ofNat 7077, memory := s.memory, stack := v2 :: v1 :: v0 :: x8 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7088, memory := s.memory, stack := v7 :: v6 :: v5 :: v0 :: x8 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [oldp1Model, v0, v1, v2, v3, v4, v5, v6, v7] using oldp1_run s (v2) (v1) (v0) (x8) (x14) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h2 : runInstructions oldp2Program {s with pc := UInt256.ofNat 7088, memory := s.memory, stack := v7 :: v6 :: v5 :: v0 :: x8 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7098, memory := s.memory, stack := v12 :: x8 :: v11 :: v10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [oldp2Model, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] using oldp2_run s (v7) (v6) (v5) (v0) (x8) (x14) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h3 : runInstructions oldp3Program {s with pc := UInt256.ofNat 7098, memory := s.memory, stack := v12 :: x8 :: v11 :: v10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7110, memory := s.memory, stack := v17 :: v16 :: x8 :: v15 :: v10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [oldp3Model, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17] using oldp3_run s (v12) (x8) (v11) (v10) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h4 : runInstructions oldp4Program {s with pc := UInt256.ofNat 7110, memory := s.memory, stack := v17 :: v16 :: x8 :: v15 :: v10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v22 :: v21 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [oldp4Model, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22] using oldp4_run s (v17) (v16) (x8) (v15) (v10) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  change runInstructions (oldp0Program ++ (oldp1Program ++ (oldp2Program ++ (oldp3Program ++ (oldp4Program))))) {s with pc := UInt256.ofNat 7066, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v22 :: v21 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))

def newp0Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 7 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .push 1 160,
   .op .MLOAD]

def newp0Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 96
  let v2 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 7083, memory := s.memory, stack := v2 :: v1 :: v0 :: q0 :: q14 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: rest}

theorem newp0_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newp0Program {s with pc := UInt256.ofNat 7066, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: rest} =
      some (newp0Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 rest) := by
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [newp0Program, newp0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha128, ha96, ha160, hf128, hf96, hf160]

def newp1Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MULMOD]

def newp1Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := MachineState.readWord s.memory 32
  let v2 : UInt256 := UInt256.mulMod v1 q4 q12
  {s with pc := UInt256.ofNat 7093, memory := s.memory, stack := v2 :: v1 :: v0 :: q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: rest}

theorem newp1_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newp1Program {s with pc := UInt256.ofNat 7083, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: rest} =
      some (newp1Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 25) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Challenge.Modexp.Submission.Proofs.Fast.Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [newp1Program, newp1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, ha64, ha32, hf64, hf32]

def newp2Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def newp2Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod q3 q2 q15
  let v1 : UInt256 := v0 + q0
  {s with pc := UInt256.ofNat 7101, memory := s.memory, stack := q5 :: q4 :: q15 :: v1 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: q21 :: rest}

theorem newp2_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newp2Program {s with pc := UInt256.ofNat 7093, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: q21 :: rest} =
      some (newp2Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 rest) := by
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  simp [newp2Program, newp2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]

def newp3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨6, by decide⟩),
   .op .MUL]

def newp3Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod q0 q1 q2
  let v1 : UInt256 := v0 + q3
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := q9 + v2
  let v4 : UInt256 := q10 * q4
  {s with pc := UInt256.ofNat 7109, memory := s.memory, stack := v4 :: q5 :: q6 :: q7 :: q8 :: q9 :: v3 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: q21 :: q22 :: q23 :: q24 :: rest}

theorem newp3_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newp3Program {s with pc := UInt256.ofNat 7101, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: q21 :: q22 :: q23 :: q24 :: rest} =
      some (newp3Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 rest) := by
  have capacity (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  simp [newp3Program, newp3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]

def newp4Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def newp4Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := q2 * q1
  let v1 : UInt256 := v0 + q0
  let v2 : UInt256 := q4 * q3
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := v3 + v3
  {s with pc := UInt256.ofNat 7117, memory := s.memory, stack := v4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: rest}

theorem newp4_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newp4Program {s with pc := UInt256.ofNat 7109, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: q17 :: q18 :: q19 :: q20 :: rest} =
      some (newp4Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 rest) := by
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [newp4Program, newp4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]

def newp5Program : List Instr :=
  [.op .ADD]

def newp5Model (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := q0 + q1
  {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v0 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: rest}

theorem newp5_run (s : State) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newp5Program {s with pc := UInt256.ofNat 7117, stack := q0 :: q1 :: q2 :: q3 :: q4 :: q5 :: q6 :: q7 :: q8 :: q9 :: q10 :: q11 :: q12 :: q13 :: q14 :: q15 :: q16 :: rest} =
      some (newp5Model s q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [newp5Program, newp5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity]

def newProgram : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 7 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .push 1 160,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨6, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD]

def newModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 96
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := MachineState.readWord s.memory 32
  let v5 : UInt256 := UInt256.mulMod v4 x14 x8
  let v6 : UInt256 := UInt256.mulMod v2 v3 x8
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := UInt256.mulMod v0 v1 x8
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := v9 + v9
  let v11 : UInt256 := x0 + v10
  let v12 : UInt256 := x14 * v4
  let v13 : UInt256 := v2 * v3
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := v0 * v1
  let v16 : UInt256 := v15 + v14
  let v17 : UInt256 := v16 + v16
  let v18 : UInt256 := v17 + x0
  {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v18 :: v11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem new_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := UInt256.ofNat 7066, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some (newModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 96
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := MachineState.readWord s.memory 32
  let v5 : UInt256 := UInt256.mulMod v4 x14 x8
  let v6 : UInt256 := UInt256.mulMod v2 v3 x8
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := UInt256.mulMod v0 v1 x8
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := v9 + v9
  let v11 : UInt256 := x0 + v10
  let v12 : UInt256 := x14 * v4
  let v13 : UInt256 := v2 * v3
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := v0 * v1
  let v16 : UInt256 := v15 + v14
  let v17 : UInt256 := v16 + v16
  let v18 : UInt256 := v17 + x0
  have h0 : runInstructions newp0Program {s with pc := UInt256.ofNat 7066, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7083, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newp0Model, v0, v1, v2] using newp0_run s (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h1 : runInstructions newp1Program {s with pc := UInt256.ofNat 7083, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7093, memory := s.memory, stack := v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: x0 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newp1Model, v0, v1, v2, v3, v4, v5] using newp1_run s (v2) (v1) (v0) (x0) (x14) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h2 : runInstructions newp2Program {s with pc := UInt256.ofNat 7093, memory := s.memory, stack := v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: x0 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7101, memory := s.memory, stack := v0 :: v1 :: x8 :: v7 :: v4 :: v3 :: v2 :: v1 :: v0 :: x0 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newp2Model, v0, v1, v2, v3, v4, v5, v6, v7] using newp2_run s (v5) (v4) (v3) (v2) (v1) (v0) (x0) (x14) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h3 : runInstructions newp3Program {s with pc := UInt256.ofNat 7101, memory := s.memory, stack := v0 :: v1 :: x8 :: v7 :: v4 :: v3 :: v2 :: v1 :: v0 :: x0 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7109, memory := s.memory, stack := v12 :: v3 :: v2 :: v1 :: v0 :: x0 :: v11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newp3Model, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] using newp3_run s (v0) (v1) (x8) (v7) (v4) (v3) (v2) (v1) (v0) (x0) (x14) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h4 : runInstructions newp4Program {s with pc := UInt256.ofNat 7109, memory := s.memory, stack := v12 :: v3 :: v2 :: v1 :: v0 :: x0 :: v11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7117, memory := s.memory, stack := v17 :: x0 :: v11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newp4Model, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17] using newp4_run s (v12) (v3) (v2) (v1) (v0) (x0) (v11) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h5 : runInstructions newp5Program {s with pc := UInt256.ofNat 7117, memory := s.memory, stack := v17 :: x0 :: v11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v18 :: v11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newp5Model, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18] using newp5_run s (v17) (x0) (v11) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  change runInstructions (newp0Program ++ (newp1Program ++ (newp2Program ++ (newp3Program ++ (newp4Program ++ (newp5Program)))))) {s with pc := UInt256.ofNat 7066, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := UInt256.ofNat 7118, memory := s.memory, stack := v18 :: v11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 h5)))))

/-- Exact arbitrary-word boundary: no digit or modulus bound is used. -/
theorem boundary_eq (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) :
    newModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest = oldModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest := by
  simp only [newModel, oldModel, addC, addA, addL, mulC, mmC]

/-- The replacement has four extra transient stack words. hcap supplies room. -/
theorem replacement_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := UInt256.ofNat 7066, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (oldModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  rw [new_run s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest hcap hact, boundary_eq]
#print axioms replacement_run
end CycleSubmission.TripleConsumer

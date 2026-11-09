import Challenge.Modexp.Submission.Proofs.Cycle.TripleConsumer
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square10
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square11
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace CycleSubmission.TripleColumns
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open CycleSubmission.Execution CycleSubmission.Prepared.Arithmetic
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

def lastPrefixProgram : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def lastPrefixModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 - x0
  let v1 : UInt256 := x9 + v0
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x9
  {s with pc := UInt256.ofNat 7066, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem lastPrefix_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions lastPrefixProgram {s with pc := UInt256.ofNat 7057, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (lastPrefixModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
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
  simp [lastPrefixProgram, lastPrefixModel, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18]

def prefixProgram : List Instr := sq10Newpart0Program ++ (sq10Newpart1Program ++ (sq10Newpart2Program ++ (sq10Newpart3Program ++ (sq10Newpart4Program ++ (sq10Newpart5Program ++ (sq10Newpart6Program ++ (sq10Newpart7Program ++ (lastPrefixProgram))))))))

def prefixModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := w6 * w5
  let v3 : W := v2 + v1
  let v4 : W := w15 * w12
  let v5 : W := v4 + v3
  let v6 : W := w14 * w3
  let v7 : W := v6 + v5
  let v8 : W := MachineState.readWord s.memory 96
  let v9 : W := UInt256.mulMod v8 v8 w10
  let v10 : W := v9 + w2
  let v11 : W := MachineState.readWord s.memory 192
  let v12 : W := UInt256.mulMod w11 v11 w10
  let v13 : W := v12 + v10
  let v14 : W := MachineState.readWord s.memory 0
  let v15 : W := UInt256.mulMod w9 v14 w10
  let v16 : W := v15 + v13
  let v17 : W := MachineState.readWord s.memory 224
  let v18 : W := UInt256.mulMod v17 w4 w10
  let v19 : W := v18 + v16
  let v20 : W := UInt256.mulMod w7 w8 w10
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w6 w5 w10
  let v23 : W := v22 + v21
  let v24 : W := UInt256.mulMod w12 w15 w10
  let v25 : W := v24 + v23
  let v26 : W := UInt256.mulMod w14 w3 w10
  let v27 : W := v26 + v25
  let v28 : W := UInt256.land w13 v7
  let v29 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v28.toNat 32) 800
  let v30 : W := v27 - v28
  let v31 : W := w10 + v30
  let v32 : W := UInt256.mulMod (N 2048) v31 w10
  {s with pc := N 7066, memory := v29, stack := v32 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem prefix_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prefixProgram {s with pc := N 6987, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} =
      some (prefixModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := w6 * w5
  let v3 : W := v2 + v1
  let v4 : W := w15 * w12
  let v5 : W := v4 + v3
  let v6 : W := w14 * w3
  let v7 : W := v6 + v5
  let v8 : W := MachineState.readWord s.memory 96
  let v9 : W := UInt256.mulMod v8 v8 w10
  let v10 : W := v9 + w2
  let v11 : W := MachineState.readWord s.memory 192
  let v12 : W := UInt256.mulMod w11 v11 w10
  let v13 : W := v12 + v10
  let v14 : W := MachineState.readWord s.memory 0
  let v15 : W := UInt256.mulMod w9 v14 w10
  let v16 : W := v15 + v13
  let v17 : W := MachineState.readWord s.memory 224
  let v18 : W := UInt256.mulMod v17 w4 w10
  let v19 : W := v18 + v16
  let v20 : W := UInt256.mulMod w7 w8 w10
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w6 w5 w10
  let v23 : W := v22 + v21
  let v24 : W := UInt256.mulMod w12 w15 w10
  let v25 : W := v24 + v23
  let v26 : W := UInt256.mulMod w14 w3 w10
  let v27 : W := v26 + v25
  let v28 : W := UInt256.land w13 v7
  let v29 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v28.toNat 32) 800
  let v30 : W := v27 - v28
  let v31 : W := w10 + v30
  let v32 : W := UInt256.mulMod (N 2048) v31 w10
  have h0 : runInstructions sq10Newpart0Program {s with pc := N 6987, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6995, memory := s.memory, stack := w15 :: w12 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart0Model, v0, v1, v2, v3] using sq10Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions sq10Newpart1Program {s with pc := N 6995, memory := s.memory, stack := w15 :: w12 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7003, memory := s.memory, stack := w10 :: w2 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart1Model, v4, v5, v6, v7] using sq10Newpart1_run (s) (w15) (w12) (v3) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions sq10Newpart2Program {s with pc := N 7003, memory := s.memory, stack := w10 :: w2 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7013, memory := s.memory, stack := v11 :: w10 :: v10 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart2Model, v8, v9, v10, v11] using sq10Newpart2_run (s) (w10) (w2) (v7) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions sq10Newpart3Program {s with pc := N 7013, memory := s.memory, stack := v11 :: w10 :: v10 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7021, memory := s.memory, stack := v15 :: v13 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart3Model, v12, v13, v14, v15] using sq10Newpart3_run (s) (v11) (w10) (v10) (v7) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h4 : runInstructions sq10Newpart4Program {s with pc := N 7021, memory := s.memory, stack := v15 :: v13 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7030, memory := s.memory, stack := w10 :: v19 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart4Model, v16, v17, v18, v19] using sq10Newpart4_run (s) (v15) (v13) (v7) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h5 : runInstructions sq10Newpart5Program {s with pc := N 7030, memory := s.memory, stack := w10 :: v19 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7038, memory := s.memory, stack := v22 :: v21 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart5Model, v20, v21, v22] using sq10Newpart5_run (s) (w10) (v19) (v7) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h6 : runInstructions sq10Newpart6Program {s with pc := N 7038, memory := s.memory, stack := v22 :: v21 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7046, memory := s.memory, stack := w3 :: w10 :: v25 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart6Model, v23, v24, v25] using sq10Newpart6_run (s) (v22) (v21) (v7) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h7 : runInstructions sq10Newpart7Program {s with pc := N 7046, memory := s.memory, stack := w3 :: w10 :: v25 :: v7 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7057, memory := v29, stack := v28 :: v27 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq10Newpart7Model, v26, v27, v28, v29] using sq10Newpart7_run (s) (w3) (w10) (v25) (v7) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h8 : runInstructions lastPrefixProgram {s with pc := N 7057, memory := v29, stack := v28 :: v27 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 7066, memory := v29, stack := v32 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [lastPrefixModel, v30, v31, v32] using lastPrefix_run ({s with memory := v29}) (v28) (v27) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

def tailProgram : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 832,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
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
   .push 1 96,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def program : List Instr := prefixProgram ++ (TripleConsumer.newProgram ++ tailProgram)

private theorem historical_program :
    squareColumn10Program ++ squareColumn11Program =
      prefixProgram ++ (TripleConsumer.oldProgram ++ tailProgram) := by rfl

private theorem append_eq (p q t : List Instr) (s : State)
    (h : runInstructions p s = runInstructions q s) :
    runInstructions (p ++ t) s = runInstructions (q ++ t) s := by
  exact (runInstructions_append p t s).trans ((congrArg (fun x => x.bind (runInstructions t)) h).trans (runInstructions_append q t s).symm)

private theorem prefix_eq (p q r : List Instr) (s t : State)
    (hp : runInstructions p s = some t) (h : runInstructions q t = runInstructions r t) :
    runInstructions (p ++ q) s = runInstructions (p ++ r) s := by
  have hq := (runInstructions_append p q s).trans (congrArg (fun x => x.bind (runInstructions q)) hp)
  have hr := (runInstructions_append p r s).trans (congrArg (fun x => x.bind (runInstructions r)) hp)
  exact hq.trans (h.trans hr.symm)

/-- Exact execution transport across the old column10/11 interface. -/
theorem run_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program {s with pc := N 6987, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} =
    runInstructions (squareColumn10Program ++ squareColumn11Program)
      {s with pc := N 6987, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := w6 * w5
  let v3 : W := v2 + v1
  let v4 : W := w15 * w12
  let v5 : W := v4 + v3
  let v6 : W := w14 * w3
  let v7 : W := v6 + v5
  let v8 : W := MachineState.readWord s.memory 96
  let v9 : W := UInt256.mulMod v8 v8 w10
  let v10 : W := v9 + w2
  let v11 : W := MachineState.readWord s.memory 192
  let v12 : W := UInt256.mulMod w11 v11 w10
  let v13 : W := v12 + v10
  let v14 : W := MachineState.readWord s.memory 0
  let v15 : W := UInt256.mulMod w9 v14 w10
  let v16 : W := v15 + v13
  let v17 : W := MachineState.readWord s.memory 224
  let v18 : W := UInt256.mulMod v17 w4 w10
  let v19 : W := v18 + v16
  let v20 : W := UInt256.mulMod w7 w8 w10
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w6 w5 w10
  let v23 : W := v22 + v21
  let v24 : W := UInt256.mulMod w12 w15 w10
  let v25 : W := v24 + v23
  let v26 : W := UInt256.mulMod w14 w3 w10
  let v27 : W := v26 + v25
  let v28 : W := UInt256.land w13 v7
  let v29 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v28.toNat 32) 800
  let v30 : W := v27 - v28
  let v31 : W := w10 + v30
  let v32 : W := UInt256.mulMod (N 2048) v31 w10

  have hp := prefix_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have hn := TripleConsumer.replacement_run ({s with memory := v29}) (v32) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have ho := TripleConsumer.old_run ({s with memory := v29}) (v32) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have he : runInstructions TripleConsumer.newProgram (prefixModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) =
      runInstructions TripleConsumer.oldProgram (prefixModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := hn.trans ho.symm
  have ht := append_eq TripleConsumer.newProgram TripleConsumer.oldProgram tailProgram _ he
  have hf := prefix_eq prefixProgram (TripleConsumer.newProgram ++ tailProgram) (TripleConsumer.oldProgram ++ tailProgram) _ _ hp ht
  calc
    _ = runInstructions (prefixProgram ++ (TripleConsumer.newProgram ++ tailProgram)) _ := rfl
    _ = runInstructions (prefixProgram ++ (TripleConsumer.oldProgram ++ tailProgram)) _ := hf
    _ = _ := congrArg (fun q => runInstructions q {s with pc := N 6987, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}) historical_program.symm
#print axioms run_eq
end CycleSubmission.TripleColumns
